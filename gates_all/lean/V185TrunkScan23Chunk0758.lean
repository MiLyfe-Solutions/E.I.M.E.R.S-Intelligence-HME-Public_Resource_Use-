import V185TrunkScan23Chunk0757

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4482481 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_4482481 : Nat := 118140960795 + 4482481 * 2 ^ 59
def prefixEnd_4482481 : Nat := 4983230072969 + 3 ^ 40 * 4482481 * 2
def baseEnd_4482481 : Nat := 2301667277646382006172951

theorem tailTrace_4482481 : CollatzResearch.WordTrace tailWord_4482481 prefixEnd_4482481 2301667277646382006172951 := by
  unfold tailWord_4482481
  simp only [CollatzResearch.WordTrace]
  refine ⟨163489513273744358651615297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108993008849162905767743531 163489513273744358651615297)
  ·
    refine ⟨122617134955308268988711473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163489513273744358651615297 122617134955308268988711473)
    ·
      refine ⟨91962851216481201741533605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122617134955308268988711473 91962851216481201741533605)
      ·
        refine ⟨17243034603090225326537551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91962851216481201741533605 17243034603090225326537551)
        ·
          refine ⟨25864551904635337989806327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17243034603090225326537551 25864551904635337989806327)
          ·
            refine ⟨38796827856953006984709491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25864551904635337989806327 38796827856953006984709491)
            ·
              refine ⟨58195241785429510477064237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38796827856953006984709491 58195241785429510477064237)
              ·
                refine ⟨21823215669536066428899089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58195241785429510477064237 21823215669536066428899089)
                ·
                  refine ⟨16367411752152049821674317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21823215669536066428899089 16367411752152049821674317)
                  ·
                    refine ⟨6137779407057018683127869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16367411752152049821674317 6137779407057018683127869)
                    ·
                      refine ⟨2301667277646382006172951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6137779407057018683127869 2301667277646382006172951)
                      ·
                        rfl

theorem cell23_4482481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_4482481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482481 prefixEnd_4482481 := by exact prefixLift 4482481
  have htrace : WordTrace (prefixWord ++ tailWord_4482481) baseStart_4482481 baseEnd_4482481 := by
    simpa [prefixWord, tailWord_4482481, baseEnd_4482481] using wordTrace_append hprefix tailTrace_4482481
  have hstable : (prefixWord ++ tailWord_4482481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482481).length < 2 ^ (prefixWord ++ tailWord_4482481).sum := by decide
  have hdescent : baseEnd_4482481 < baseStart_4482481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482518 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_4482518 : Nat := 118140960795 + 4482518 * 2 ^ 59
def prefixEnd_4482518 : Nat := 4983230072969 + 3 ^ 40 * 4482518 * 2
def baseEnd_4482518 : Nat := 767228758810199453803427

theorem tailTrace_4482518 : CollatzResearch.WordTrace tailWord_4482518 prefixEnd_4482518 767228758810199453803427 := by
  unfold tailWord_4482518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10218178923413144623169513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108993908516406875980474805 10218178923413144623169513)
  ·
    refine ⟨7663634192559858467377135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10218178923413144623169513 7663634192559858467377135)
    ·
      refine ⟨11495451288839787701065703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7663634192559858467377135 11495451288839787701065703)
      ·
        refine ⟨17243176933259681551598555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11495451288839787701065703 17243176933259681551598555)
        ·
          refine ⟨25864765399889522327397833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17243176933259681551598555 25864765399889522327397833)
          ·
            refine ⟨19398574049917141745548375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25864765399889522327397833 19398574049917141745548375)
            ·
              refine ⟨29097861074875712618322563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19398574049917141745548375 29097861074875712618322563)
              ·
                refine ⟨43646791612313568927483845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29097861074875712618322563 43646791612313568927483845)
                ·
                  refine ⟨8183773427308794173903221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43646791612313568927483845 8183773427308794173903221)
                  ·
                    refine ⟨767228758810199453803427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8183773427308794173903221 767228758810199453803427)
                    ·
                      rfl

theorem cell23_4482518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_4482518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482518 prefixEnd_4482518 := by exact prefixLift 4482518
  have htrace : WordTrace (prefixWord ++ tailWord_4482518) baseStart_4482518 baseEnd_4482518 := by
    simpa [prefixWord, tailWord_4482518, baseEnd_4482518] using wordTrace_append hprefix tailTrace_4482518
  have hstable : (prefixWord ++ tailWord_4482518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482518).length < 2 ^ (prefixWord ++ tailWord_4482518).sum := by decide
  have hdescent : baseEnd_4482518 < baseStart_4482518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482521 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_4482521 : Nat := 118140960795 + 4482521 * 2 ^ 59
def prefixEnd_4482521 : Nat := 4983230072969 + 3 ^ 40 * 4482521 * 2
def baseEnd_4482521 : Nat := 2301687816872561849672767

theorem tailTrace_4482521 : CollatzResearch.WordTrace tailWord_4482521 prefixEnd_4482521 2301687816872561849672767 := by
  unfold tailWord_4482521
  simp only [CollatzResearch.WordTrace]
  refine ⟨163490972193599445483071417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108993981462399630322047611 163490972193599445483071417)
  ·
    refine ⟨122618229145199584112303563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163490972193599445483071417 122618229145199584112303563)
    ·
      refine ⟨183927343717799376168455345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122618229145199584112303563 183927343717799376168455345)
      ·
        refine ⟨137945507788349532126341509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183927343717799376168455345 137945507788349532126341509)
        ·
          refine ⟨25864782710315537273689033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137945507788349532126341509 25864782710315537273689033)
          ·
            refine ⟨19398587032736652955266775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25864782710315537273689033 19398587032736652955266775)
            ·
              refine ⟨29097880549104979432900163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19398587032736652955266775 29097880549104979432900163)
              ·
                refine ⟨43646820823657469149350245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29097880549104979432900163 43646820823657469149350245)
                ·
                  refine ⟨8183778904435775465503171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43646820823657469149350245 8183778904435775465503171)
                  ·
                    refine ⟨12275668356653663198254757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8183778904435775465503171 12275668356653663198254757)
                    ·
                      refine ⟨2301687816872561849672767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12275668356653663198254757 2301687816872561849672767)
                      ·
                        rfl

theorem cell23_4482521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_4482521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482521 prefixEnd_4482521 := by exact prefixLift 4482521
  have htrace : WordTrace (prefixWord ++ tailWord_4482521) baseStart_4482521 baseEnd_4482521 := by
    simpa [prefixWord, tailWord_4482521, baseEnd_4482521] using wordTrace_append hprefix tailTrace_4482521
  have hstable : (prefixWord ++ tailWord_4482521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482521).length < 2 ^ (prefixWord ++ tailWord_4482521).sum := by decide
  have hdescent : baseEnd_4482521 < baseStart_4482521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482591 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 3, 5]
def baseStart_4482591 : Nat := 118140960795 + 4482591 * 2 ^ 59
def prefixEnd_4482591 : Nat := 4983230072969 + 3 ^ 40 * 4482591 * 2
def baseEnd_4482591 : Nat := 767241253506125525265815

theorem tailTrace_4482591 : CollatzResearch.WordTrace tailWord_4482591 prefixEnd_4482591 767241253506125525265815 := by
  unfold tailWord_4482591
  simp only [CollatzResearch.WordTrace]
  refine ⟨163493525303345847438119627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108995683535563898292079751 163493525303345847438119627)
  ·
    refine ⟨245240287955018771157179441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163493525303345847438119627 245240287955018771157179441)
    ·
      refine ⟨183930215966264078367884581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245240287955018771157179441 183930215966264078367884581)
      ·
        refine ⟨34486915493674514693978359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183930215966264078367884581 34486915493674514693978359)
        ·
          refine ⟨51730373240511772040967539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34486915493674514693978359 51730373240511772040967539)
          ·
            refine ⟨77595559860767658061451309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51730373240511772040967539 77595559860767658061451309)
            ·
              refine ⟨29098334947787871773044241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77595559860767658061451309 29098334947787871773044241)
              ·
                refine ⟨21823751210840903829783181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29098334947787871773044241 21823751210840903829783181)
                ·
                  refine ⟨8183906704065338936168693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21823751210840903829783181 8183906704065338936168693)
                  ·
                    refine ⟨767241253506125525265815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8183906704065338936168693 767241253506125525265815)
                    ·
                      rfl

theorem cell23_4482591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_4482591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482591 prefixEnd_4482591 := by exact prefixLift 4482591
  have htrace : WordTrace (prefixWord ++ tailWord_4482591) baseStart_4482591 baseEnd_4482591 := by
    simpa [prefixWord, tailWord_4482591, baseEnd_4482591] using wordTrace_append hprefix tailTrace_4482591
  have hstable : (prefixWord ++ tailWord_4482591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482591).length < 2 ^ (prefixWord ++ tailWord_4482591).sum := by decide
  have hdescent : baseEnd_4482591 < baseStart_4482591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482615 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 2, 3, 2]
def baseStart_4482615 : Nat := 118140960795 + 4482615 * 2 ^ 59
def prefixEnd_4482615 : Nat := 4983230072969 + 3 ^ 40 * 4482615 * 2
def baseEnd_4482615 : Nat := 2301736084054084481897335

theorem tailTrace_4482615 : CollatzResearch.WordTrace tailWord_4482615 prefixEnd_4482615 2301736084054084481897335 := by
  unfold tailWord_4482615
  simp only [CollatzResearch.WordTrace]
  refine ⟨163494400655258899536993299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108996267103505933024662199 163494400655258899536993299)
  ·
    refine ⟨245241600982888349305489949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163494400655258899536993299 245241600982888349305489949)
    ·
      refine ⟨91965600368583130989558731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245241600982888349305489949 91965600368583130989558731)
      ·
        refine ⟨137948400552874696484338097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91965600368583130989558731 137948400552874696484338097)
        ·
          refine ⟨103461300414656022363253573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137948400552874696484338097 103461300414656022363253573)
          ·
            refine ⟨19398993827748004193110045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103461300414656022363253573 19398993827748004193110045)
            ·
              refine ⟨7274622685405501572416267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19398993827748004193110045 7274622685405501572416267)
              ·
                refine ⟨10911934028108252358624401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7274622685405501572416267 10911934028108252358624401)
                ·
                  refine ⟨8183950521081189268968301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10911934028108252358624401 8183950521081189268968301)
                  ·
                    refine ⟨3068981445405445975863113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8183950521081189268968301 3068981445405445975863113)
                    ·
                      refine ⟨2301736084054084481897335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068981445405445975863113 2301736084054084481897335)
                      ·
                        rfl

theorem cell23_4482615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_4482615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482615 prefixEnd_4482615 := by exact prefixLift 4482615
  have htrace : WordTrace (prefixWord ++ tailWord_4482615) baseStart_4482615 baseEnd_4482615 := by
    simpa [prefixWord, tailWord_4482615, baseEnd_4482615] using wordTrace_append hprefix tailTrace_4482615
  have hstable : (prefixWord ++ tailWord_4482615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482615).length < 2 ^ (prefixWord ++ tailWord_4482615).sum := by decide
  have hdescent : baseEnd_4482615 < baseStart_4482615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482641 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_4482641 : Nat := 118140960795 + 4482641 * 2 ^ 59
def prefixEnd_4482641 : Nat := 4983230072969 + 3 ^ 40 * 4482641 * 2
def baseEnd_4482641 : Nat := 2301749434551101380172215

theorem tailTrace_4482641 : CollatzResearch.WordTrace tailWord_4482641 prefixEnd_4482641 2301749434551101380172215 := by
  unfold tailWord_4482641
  simp only [CollatzResearch.WordTrace]
  refine ⟨163495348953164705977439777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108996899302109803984959851 163495348953164705977439777)
  ·
    refine ⟨122621511714873529483079833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163495348953164705977439777 122621511714873529483079833)
    ·
      refine ⟨91966133786155147112309875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122621511714873529483079833 91966133786155147112309875)
      ·
        refine ⟨137949200679232720668464813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91966133786155147112309875 137949200679232720668464813)
        ·
          refine ⟨51730950254712270250674305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137949200679232720668464813 51730950254712270250674305)
          ·
            refine ⟨38798212691034202688005729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51730950254712270250674305 38798212691034202688005729)
            ·
              refine ⟨29098659518275652016004297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38798212691034202688005729 29098659518275652016004297)
              ·
                refine ⟨21823994638706739012003223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29098659518275652016004297 21823994638706739012003223)
                ·
                  refine ⟨32735991958060108518004835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21823994638706739012003223 32735991958060108518004835)
                  ·
                    refine ⟨49103987937090162777007253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32735991958060108518004835 49103987937090162777007253)
                    ·
                      refine ⟨2301749434551101380172215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49103987937090162777007253 2301749434551101380172215)
                      ·
                        rfl

theorem cell23_4482641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_4482641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482641 prefixEnd_4482641 := by exact prefixLift 4482641
  have htrace : WordTrace (prefixWord ++ tailWord_4482641) baseStart_4482641 baseEnd_4482641 := by
    simpa [prefixWord, tailWord_4482641, baseEnd_4482641] using wordTrace_append hprefix tailTrace_4482641
  have hstable : (prefixWord ++ tailWord_4482641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482641).length < 2 ^ (prefixWord ++ tailWord_4482641).sum := by decide
  have hdescent : baseEnd_4482641 < baseStart_4482641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482691 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5]
def baseStart_4482691 : Nat := 118140960795 + 4482691 * 2 ^ 59
def prefixEnd_4482691 : Nat := 4983230072969 + 3 ^ 40 * 4482691 * 2
def baseEnd_4482691 : Nat := 2301775108583826184546985

theorem tailTrace_4482691 : CollatzResearch.WordTrace tailWord_4482691 prefixEnd_4482691 2301775108583826184546985 := by
  unfold tailWord_4482691
  simp only [CollatzResearch.WordTrace]
  refine ⟨163497172602983564516759927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108998115068655709677839951 163497172602983564516759927)
  ·
    refine ⟨245245758904475346775139891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163497172602983564516759927 245245758904475346775139891)
    ·
      refine ⟨367868638356713020162709837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245245758904475346775139891 367868638356713020162709837)
      ·
        refine ⟨137950739383767382561016189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367868638356713020162709837 137950739383767382561016189)
        ·
          refine ⟨51731527268912768460381071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137950739383767382561016189 51731527268912768460381071)
          ·
            refine ⟨77597290903369152690571607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51731527268912768460381071 77597290903369152690571607)
            ·
              refine ⟨116395936355053729035857411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77597290903369152690571607 116395936355053729035857411)
              ·
                refine ⟨174593904532580593553786117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116395936355053729035857411 174593904532580593553786117)
                ·
                  refine ⟨32736357099858861291334897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174593904532580593553786117 32736357099858861291334897)
                  ·
                    refine ⟨24552267824894145968501173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32736357099858861291334897 24552267824894145968501173)
                    ·
                      refine ⟨2301775108583826184546985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24552267824894145968501173 2301775108583826184546985)
                      ·
                        rfl

theorem cell23_4482691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_4482691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482691 prefixEnd_4482691 := by exact prefixLift 4482691
  have htrace : WordTrace (prefixWord ++ tailWord_4482691) baseStart_4482691 baseEnd_4482691 := by
    simpa [prefixWord, tailWord_4482691, baseEnd_4482691] using wordTrace_append hprefix tailTrace_4482691
  have hstable : (prefixWord ++ tailWord_4482691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482691).length < 2 ^ (prefixWord ++ tailWord_4482691).sum := by decide
  have hdescent : baseEnd_4482691 < baseStart_4482691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482695 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_4482695 : Nat := 118140960795 + 4482695 * 2 ^ 59
def prefixEnd_4482695 : Nat := 4983230072969 + 3 ^ 40 * 4482695 * 2
def baseEnd_4482695 : Nat := 2301777162506444168896967

theorem tailTrace_4482695 : CollatzResearch.WordTrace tailWord_4482695 prefixEnd_4482695 2301777162506444168896967 := by
  unfold tailWord_4482695
  simp only [CollatzResearch.WordTrace]
  refine ⟨163497318494969073199905539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108998212329979382133270359 163497318494969073199905539)
  ·
    refine ⟨245245977742453609799858309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163497318494969073199905539 245245977742453609799858309)
    ·
      refine ⟨45983620826710051837473433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245245977742453609799858309 45983620826710051837473433)
      ·
        refine ⟨34487715620032538878105075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45983620826710051837473433 34487715620032538878105075)
        ·
          refine ⟨51731573430048808317157613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34487715620032538878105075 51731573430048808317157613)
          ·
            refine ⟨19399340036268303118934105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51731573430048808317157613 19399340036268303118934105)
            ·
              refine ⟨14549505027201227339200579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19399340036268303118934105 14549505027201227339200579)
              ·
                refine ⟨21824257540801841008800869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14549505027201227339200579 21824257540801841008800869)
                ·
                  refine ⟨4092048288900345189150163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21824257540801841008800869 4092048288900345189150163)
                  ·
                    refine ⟨6138072433350517783725245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4092048288900345189150163 6138072433350517783725245)
                    ·
                      refine ⟨2301777162506444168896967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6138072433350517783725245 2301777162506444168896967)
                      ·
                        rfl

theorem cell23_4482695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_4482695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482695 prefixEnd_4482695 := by exact prefixLift 4482695
  have htrace : WordTrace (prefixWord ++ tailWord_4482695) baseStart_4482695 baseEnd_4482695 := by
    simpa [prefixWord, tailWord_4482695, baseEnd_4482695] using wordTrace_append hprefix tailTrace_4482695
  have hstable : (prefixWord ++ tailWord_4482695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482695).length < 2 ^ (prefixWord ++ tailWord_4482695).sum := by decide
  have hdescent : baseEnd_4482695 < baseStart_4482695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482696 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4482696 : Nat := 118140960795 + 4482696 * 2 ^ 59
def prefixEnd_4482696 : Nat := 4983230072969 + 3 ^ 40 * 4482696 * 2
def baseEnd_4482696 : Nat := 2301777675987098664984463

theorem tailTrace_4482696 : CollatzResearch.WordTrace tailWord_4482696 prefixEnd_4482696 2301777675987098664984463 := by
  unfold tailWord_4482696
  simp only [CollatzResearch.WordTrace]
  refine ⟨81748677483982725185345971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108998236645310300247127961 81748677483982725185345971)
  ·
    refine ⟨122623016225974087778018957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81748677483982725185345971 122623016225974087778018957)
    ·
      refine ⟨45983631084740282916757109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122623016225974087778018957 45983631084740282916757109)
      ·
        refine ⟨4310965414194401523445979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45983631084740282916757109 4310965414194401523445979)
        ·
          refine ⟨6466448121291602285168969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310965414194401523445979 6466448121291602285168969)
          ·
            refine ⟨4849836090968701713876727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6466448121291602285168969 4849836090968701713876727)
            ·
              refine ⟨7274754136453052570815091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849836090968701713876727 7274754136453052570815091)
              ·
                refine ⟨10912131204679578856222637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7274754136453052570815091 10912131204679578856222637)
                ·
                  refine ⟨4092049201754842071083489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10912131204679578856222637 4092049201754842071083489)
                  ·
                    refine ⟨3069036901316131553312617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4092049201754842071083489 3069036901316131553312617)
                    ·
                      refine ⟨2301777675987098664984463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069036901316131553312617 2301777675987098664984463)
                      ·
                        rfl

theorem cell23_4482696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4482696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482696 prefixEnd_4482696 := by exact prefixLift 4482696
  have htrace : WordTrace (prefixWord ++ tailWord_4482696) baseStart_4482696 baseEnd_4482696 := by
    simpa [prefixWord, tailWord_4482696, baseEnd_4482696] using wordTrace_append hprefix tailTrace_4482696
  have hstable : (prefixWord ++ tailWord_4482696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482696).length < 2 ^ (prefixWord ++ tailWord_4482696).sum := by decide
  have hdescent : baseEnd_4482696 < baseStart_4482696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482706 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4482706 : Nat := 118140960795 + 4482706 * 2 ^ 59
def prefixEnd_4482706 : Nat := 4983230072969 + 3 ^ 40 * 4482706 * 2
def baseEnd_4482706 : Nat := 767260936931214541953139

theorem tailTrace_4482706 : CollatzResearch.WordTrace tailWord_4482706 prefixEnd_4482706 767260936931214541953139 := by
  unfold tailWord_4482706
  simp only [CollatzResearch.WordTrace]
  refine ⟨40874429924482305519638993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108998479798619481385703981 40874429924482305519638993)
  ·
    refine ⟨30655822443361729139729245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40874429924482305519638993 30655822443361729139729245)
    ·
      refine ⟨11495933416260648427398467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30655822443361729139729245 11495933416260648427398467)
      ·
        refine ⟨17243900124390972641097701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11495933416260648427398467 17243900124390972641097701)
        ·
          refine ⟨3233231273323307370205819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17243900124390972641097701 3233231273323307370205819)
          ·
            refine ⟨4849846909984961055308729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233231273323307370205819 4849846909984961055308729)
            ·
              refine ⟨3637385182488720791481547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4849846909984961055308729 3637385182488720791481547)
              ·
                refine ⟨5456077773733081187222321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3637385182488720791481547 5456077773733081187222321)
                ·
                  refine ⟨4092058330299810890416741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5456077773733081187222321 4092058330299810890416741)
                  ·
                    refine ⟨767260936931214541953139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4092058330299810890416741 767260936931214541953139)
                    ·
                      rfl

theorem cell23_4482706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4482706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482706 prefixEnd_4482706 := by exact prefixLift 4482706
  have htrace : WordTrace (prefixWord ++ tailWord_4482706) baseStart_4482706 baseEnd_4482706 := by
    simpa [prefixWord, tailWord_4482706, baseEnd_4482706] using wordTrace_append hprefix tailTrace_4482706
  have hstable : (prefixWord ++ tailWord_4482706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482706).length < 2 ^ (prefixWord ++ tailWord_4482706).sum := by decide
  have hdescent : baseEnd_4482706 < baseStart_4482706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482712 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_4482712 : Nat := 118140960795 + 4482712 * 2 ^ 59
def prefixEnd_4482712 : Nat := 4983230072969 + 3 ^ 40 * 4482712 * 2
def baseEnd_4482712 : Nat := 2301785891677570602384389

theorem tailTrace_4482712 : CollatzResearch.WordTrace tailWord_4482712 prefixEnd_4482712 2301785891677570602384389 := by
  unfold tailWord_4482712
  simp only [CollatzResearch.WordTrace]
  refine ⟨81748969267953742551637195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108998625690604990068849593 81748969267953742551637195)
  ·
    refine ⟨122623453901930613827455793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81748969267953742551637195 122623453901930613827455793)
    ·
      refine ⟨91967590426447960370591845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122623453901930613827455793 91967590426447960370591845)
      ·
        refine ⟨17243923204958992569485971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91967590426447960370591845 17243923204958992569485971)
        ·
          refine ⟨25865884807438488854228957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17243923204958992569485971 25865884807438488854228957)
          ·
            refine ⟨9699706802789433320335859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25865884807438488854228957 9699706802789433320335859)
            ·
              refine ⟨14549560204184149980503789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9699706802789433320335859 14549560204184149980503789)
              ·
                refine ⟨5456085076569056242688921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14549560204184149980503789 5456085076569056242688921)
                ·
                  refine ⟨4092063807426792182016691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5456085076569056242688921 4092063807426792182016691)
                  ·
                    refine ⟨6138095711140188273025037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4092063807426792182016691 6138095711140188273025037)
                    ·
                      refine ⟨2301785891677570602384389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6138095711140188273025037 2301785891677570602384389)
                      ·
                        rfl

theorem cell23_4482712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_4482712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482712 prefixEnd_4482712 := by exact prefixLift 4482712
  have htrace : WordTrace (prefixWord ++ tailWord_4482712) baseStart_4482712 baseEnd_4482712 := by
    simpa [prefixWord, tailWord_4482712, baseEnd_4482712] using wordTrace_append hprefix tailTrace_4482712
  have hstable : (prefixWord ++ tailWord_4482712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482712).length < 2 ^ (prefixWord ++ tailWord_4482712).sum := by decide
  have hdescent : baseEnd_4482712 < baseStart_4482712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482735 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 1, 4, 2]
def baseStart_4482735 : Nat := 118140960795 + 4482735 * 2 ^ 59
def prefixEnd_4482735 : Nat := 4983230072969 + 3 ^ 40 * 4482735 * 2
def baseEnd_4482735 : Nat := 2301797701732624012396783

theorem tailTrace_4482735 : CollatzResearch.WordTrace tailWord_4482735 prefixEnd_4482735 2301797701732624012396783 := by
  unfold tailWord_4482735
  simp only [CollatzResearch.WordTrace]
  refine ⟨163498777414824160031361659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108999184943216106687574439 163498777414824160031361659)
  ·
    refine ⟨245248166122236240047042489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163498777414824160031361659 245248166122236240047042489)
    ·
      refine ⟨183936124591677180035281867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245248166122236240047042489 183936124591677180035281867)
      ·
        refine ⟨275904186887515770052922801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183936124591677180035281867 275904186887515770052922801)
        ·
          refine ⟨206928140165636827539692101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275904186887515770052922801 206928140165636827539692101)
          ·
            refine ⟨38799026281056905163692269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206928140165636827539692101 38799026281056905163692269)
            ·
              refine ⟨14549634855396339436384601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38799026281056905163692269 14549634855396339436384601)
              ·
                refine ⟨10912226141547254577288451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14549634855396339436384601 10912226141547254577288451)
                ·
                  refine ⟨16368339212320881865932677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10912226141547254577288451 16368339212320881865932677)
                  ·
                    refine ⟨3069063602310165349862377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16368339212320881865932677 3069063602310165349862377)
                    ·
                      refine ⟨2301797701732624012396783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069063602310165349862377 2301797701732624012396783)
                      ·
                        rfl

theorem cell23_4482735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4, 2].length) (baseStart_4482735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482735 prefixEnd_4482735 := by exact prefixLift 4482735
  have htrace : WordTrace (prefixWord ++ tailWord_4482735) baseStart_4482735 baseEnd_4482735 := by
    simpa [prefixWord, tailWord_4482735, baseEnd_4482735] using wordTrace_append hprefix tailTrace_4482735
  have hstable : (prefixWord ++ tailWord_4482735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482735).length < 2 ^ (prefixWord ++ tailWord_4482735).sum := by decide
  have hdescent : baseEnd_4482735 < baseStart_4482735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482738 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_4482738 : Nat := 118140960795 + 4482738 * 2 ^ 59
def prefixEnd_4482738 : Nat := 4983230072969 + 3 ^ 40 * 4482738 * 2
def baseEnd_4482738 : Nat := 2301799242174587500659269

theorem tailTrace_4482738 : CollatzResearch.WordTrace tailWord_4482738 prefixEnd_4482738 2301799242174587500659269 := by
  unfold tailWord_4482738
  simp only [CollatzResearch.WordTrace]
  refine ⟨40874721708453322885930217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108999257889208861029147245 40874721708453322885930217)
  ·
    refine ⟨30656041281339992164447663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40874721708453322885930217 30656041281339992164447663)
    ·
      refine ⟨45984061922009988246671495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30656041281339992164447663 45984061922009988246671495)
      ·
        refine ⟨68976092883014982370007243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45984061922009988246671495 68976092883014982370007243)
        ·
          refine ⟨103464139324522473555010865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68976092883014982370007243 103464139324522473555010865)
          ·
            refine ⟨77598104493391855166258149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103464139324522473555010865 77598104493391855166258149)
            ·
              refine ⟨14549644592510972843673403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77598104493391855166258149 14549644592510972843673403)
              ·
                refine ⟨21824466888766459265510105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14549644592510972843673403 21824466888766459265510105)
                ·
                  refine ⟨16368350166574844449132579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21824466888766459265510105 16368350166574844449132579)
                  ·
                    refine ⟨24552525249862266673698869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16368350166574844449132579 24552525249862266673698869)
                    ·
                      refine ⟨2301799242174587500659269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24552525249862266673698869 2301799242174587500659269)
                      ·
                        rfl

theorem cell23_4482738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_4482738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482738 prefixEnd_4482738 := by exact prefixLift 4482738
  have htrace : WordTrace (prefixWord ++ tailWord_4482738) baseStart_4482738 baseEnd_4482738 := by
    simpa [prefixWord, tailWord_4482738, baseEnd_4482738] using wordTrace_append hprefix tailTrace_4482738
  have hstable : (prefixWord ++ tailWord_4482738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482738).length < 2 ^ (prefixWord ++ tailWord_4482738).sum := by decide
  have hdescent : baseEnd_4482738 < baseStart_4482738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482771 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 11]
def baseStart_4482771 : Nat := 118140960795 + 4482771 * 2 ^ 59
def prefixEnd_4482771 : Nat := 4983230072969 + 3 ^ 40 * 4482771 * 2
def baseEnd_4482771 : Nat := 767272062345395290515539

theorem tailTrace_4482771 : CollatzResearch.WordTrace tailWord_4482771 prefixEnd_4482771 767272062345395290515539 := by
  unfold tailWord_4482771
  simp only [CollatzResearch.WordTrace]
  refine ⟨163500090442693738179672167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109000060295129158786448111 163500090442693738179672167)
  ·
    refine ⟨245250135664040607269508251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163500090442693738179672167 245250135664040607269508251)
    ·
      refine ⟨367875203496060910904262377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245250135664040607269508251 367875203496060910904262377)
      ·
        refine ⟨275906402622045683178196783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367875203496060910904262377 275906402622045683178196783)
        ·
          refine ⟨413859603933068524767295175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275906402622045683178196783 413859603933068524767295175)
          ·
            refine ⟨620789405899602787150942763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413859603933068524767295175 620789405899602787150942763)
            ·
              refine ⟨931184108849404180726414145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620789405899602787150942763 931184108849404180726414145)
              ·
                refine ⟨698388081637053135544810609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931184108849404180726414145 698388081637053135544810609)
                ·
                  refine ⟨523791061227789851658607957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 698388081637053135544810609 523791061227789851658607957)
                  ·
                    refine ⟨767272062345395290515539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 523791061227789851658607957 767272062345395290515539)
                    ·
                      rfl

theorem cell23_4482771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 11].length) (baseStart_4482771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482771 prefixEnd_4482771 := by exact prefixLift 4482771
  have htrace : WordTrace (prefixWord ++ tailWord_4482771) baseStart_4482771 baseEnd_4482771 := by
    simpa [prefixWord, tailWord_4482771, baseEnd_4482771] using wordTrace_append hprefix tailTrace_4482771
  have hstable : (prefixWord ++ tailWord_4482771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482771).length < 2 ^ (prefixWord ++ tailWord_4482771).sum := by decide
  have hdescent : baseEnd_4482771 < baseStart_4482771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482788 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_4482788 : Nat := 118140960795 + 4482788 * 2 ^ 59
def prefixEnd_4482788 : Nat := 4983230072969 + 3 ^ 40 * 4482788 * 2
def baseEnd_4482788 : Nat := 767274972069104101678013

theorem tailTrace_4482788 : CollatzResearch.WordTrace tailWord_4482788 prefixEnd_4482788 767274972069104101678013 := by
  unfold tailWord_4482788
  simp only [CollatzResearch.WordTrace]
  refine ⟨81750355241816075041520509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109000473655754766722027345 81750355241816075041520509)
  ·
    refine ⟨30656383215681028140570191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81750355241816075041520509 30656383215681028140570191)
    ·
      refine ⟨45984574823521542210855287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30656383215681028140570191 45984574823521542210855287)
      ·
        refine ⟨68976862235282313316282931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45984574823521542210855287 68976862235282313316282931)
        ·
          refine ⟨103465293352923469974424397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68976862235282313316282931 103465293352923469974424397)
          ·
            refine ⟨38799485007346301240409149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103465293352923469974424397 38799485007346301240409149)
            ·
              refine ⟨14549806877754862965153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38799485007346301240409149 14549806877754862965153431)
              ·
                refine ⟨21824710316632294447730147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14549806877754862965153431 21824710316632294447730147)
                ·
                  refine ⟨32737065474948441671595221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21824710316632294447730147 32737065474948441671595221)
                  ·
                    refine ⟨767274972069104101678013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32737065474948441671595221 767274972069104101678013)
                    ·
                      rfl

theorem cell23_4482788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_4482788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482788 prefixEnd_4482788 := by exact prefixLift 4482788
  have htrace : WordTrace (prefixWord ++ tailWord_4482788) baseStart_4482788 baseEnd_4482788 := by
    simpa [prefixWord, tailWord_4482788, baseEnd_4482788] using wordTrace_append hprefix tailTrace_4482788
  have hstable : (prefixWord ++ tailWord_4482788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482788).length < 2 ^ (prefixWord ++ tailWord_4482788).sum := by decide
  have hdescent : baseEnd_4482788 < baseStart_4482788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482792 : List Nat := [2, 1, 4, 1, 3, 2, 2, 3, 5]
def baseStart_4482792 : Nat := 118140960795 + 4482792 * 2 ^ 59
def prefixEnd_4482792 : Nat := 4983230072969 + 3 ^ 40 * 4482792 * 2
def baseEnd_4482792 : Nat := 255758552236658921042669

theorem tailTrace_4482792 : CollatzResearch.WordTrace tailWord_4482792 prefixEnd_4482792 255758552236658921042669 := by
  unfold tailWord_4482792
  simp only [CollatzResearch.WordTrace]
  refine ⟨81750428187808829383093315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109000570917078439177457753 81750428187808829383093315)
  ·
    refine ⟨122625642281713244074639973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81750428187808829383093315 122625642281713244074639973)
    ·
      refine ⟨22992307927821233263994995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122625642281713244074639973 22992307927821233263994995)
      ·
        refine ⟨34488461891731849895992493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22992307927821233263994995 34488461891731849895992493)
        ·
          refine ⟨12933173209399443710997185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34488461891731849895992493 12933173209399443710997185)
          ·
            refine ⟨9699879907049582783247889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12933173209399443710997185 9699879907049582783247889)
            ·
              refine ⟨7274909930287187087435917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9699879907049582783247889 7274909930287187087435917)
              ·
                refine ⟨2728091223857695157788469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7274909930287187087435917 2728091223857695157788469)
                ·
                  refine ⟨255758552236658921042669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2728091223857695157788469 255758552236658921042669)
                  ·
                    rfl

theorem cell23_4482792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 5].length) (baseStart_4482792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482792 prefixEnd_4482792 := by exact prefixLift 4482792
  have htrace : WordTrace (prefixWord ++ tailWord_4482792) baseStart_4482792 baseEnd_4482792 := by
    simpa [prefixWord, tailWord_4482792, baseEnd_4482792] using wordTrace_append hprefix tailTrace_4482792
  have hstable : (prefixWord ++ tailWord_4482792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482792).length < 2 ^ (prefixWord ++ tailWord_4482792).sum := by decide
  have hdescent : baseEnd_4482792 < baseStart_4482792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482848 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 10]
def baseStart_4482848 : Nat := 118140960795 + 4482848 * 2 ^ 59
def prefixEnd_4482848 : Nat := 4983230072969 + 3 ^ 40 * 4482848 * 2
def baseEnd_4482848 : Nat := 255761747227398007809307

theorem tailTrace_4482848 : CollatzResearch.WordTrace tailWord_4482848 prefixEnd_4482848 255761747227398007809307 := by
  unfold tailWord_4482848
  simp only [CollatzResearch.WordTrace]
  refine ⟨81751449431707390165112599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109001932575609853553483465 81751449431707390165112599)
  ·
    refine ⟨122627174147561085247668899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81751449431707390165112599 122627174147561085247668899)
    ·
      refine ⟨183940761221341627871503349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122627174147561085247668899 183940761221341627871503349)
      ·
        refine ⟨17244446364500777612953439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183940761221341627871503349 17244446364500777612953439)
        ·
          refine ⟨25866669546751166419430159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17244446364500777612953439 25866669546751166419430159)
          ·
            refine ⟨38800004320126749629145239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25866669546751166419430159 38800004320126749629145239)
            ·
              refine ⟨58200006480190124443717859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38800004320126749629145239 58200006480190124443717859)
              ·
                refine ⟨87300009720285186665576789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58200006480190124443717859 87300009720285186665576789)
                ·
                  refine ⟨255761747227398007809307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87300009720285186665576789 255761747227398007809307)
                  ·
                    rfl

theorem cell23_4482848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_4482848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482848 prefixEnd_4482848 := by exact prefixLift 4482848
  have htrace : WordTrace (prefixWord ++ tailWord_4482848) baseStart_4482848 baseEnd_4482848 := by
    simpa [prefixWord, tailWord_4482848, baseEnd_4482848] using wordTrace_append hprefix tailTrace_4482848
  have hstable : (prefixWord ++ tailWord_4482848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482848).length < 2 ^ (prefixWord ++ tailWord_4482848).sum := by decide
  have hdescent : baseEnd_4482848 < baseStart_4482848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482869 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_4482869 : Nat := 118140960795 + 4482869 * 2 ^ 59
def prefixEnd_4482869 : Nat := 4983230072969 + 3 ^ 40 * 4482869 * 2
def baseEnd_4482869 : Nat := 767288836046775496040389

theorem tailTrace_4482869 : CollatzResearch.WordTrace tailWord_4482869 prefixEnd_4482869 767288836046775496040389 := by
  unfold tailWord_4482869
  simp only [CollatzResearch.WordTrace]
  refine ⟨163503664796338700916739661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109002443197559133944493107 163503664796338700916739661)
  ·
    refine ⟨61313874298627012843777373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163503664796338700916739661 61313874298627012843777373)
    ·
      refine ⟨22992702861985129816416515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61313874298627012843777373 22992702861985129816416515)
      ·
        refine ⟨34489054292977694724624773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22992702861985129816416515 34489054292977694724624773)
        ·
          refine ⟨6466697679933317760867145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34489054292977694724624773 6466697679933317760867145)
          ·
            refine ⟨4850023259949988320650359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6466697679933317760867145 4850023259949988320650359)
            ·
              refine ⟨7275034889924982480975539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850023259949988320650359 7275034889924982480975539)
              ·
                refine ⟨10912552334887473721463309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7275034889924982480975539 10912552334887473721463309)
                ·
                  refine ⟨4092207125582802645548741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10912552334887473721463309 4092207125582802645548741)
                  ·
                    refine ⟨767288836046775496040389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4092207125582802645548741 767288836046775496040389)
                    ·
                      rfl

theorem cell23_4482869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_4482869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482869 prefixEnd_4482869 := by exact prefixLift 4482869
  have htrace : WordTrace (prefixWord ++ tailWord_4482869) baseStart_4482869 baseEnd_4482869 := by
    simpa [prefixWord, tailWord_4482869, baseEnd_4482869] using wordTrace_append hprefix tailTrace_4482869
  have hstable : (prefixWord ++ tailWord_4482869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482869).length < 2 ^ (prefixWord ++ tailWord_4482869).sum := by decide
  have hdescent : baseEnd_4482869 < baseStart_4482869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482949 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 3, 2, 2]
def baseStart_4482949 : Nat := 118140960795 + 4482949 * 2 ^ 59
def prefixEnd_4482949 : Nat := 4983230072969 + 3 ^ 40 * 4482949 * 2
def baseEnd_4482949 : Nat := 2301907586592686175120799

theorem tailTrace_4482949 : CollatzResearch.WordTrace tailWord_4482949 prefixEnd_4482949 2301907586592686175120799 := by
  unfold tailWord_4482949
  simp only [CollatzResearch.WordTrace]
  refine ⟨163506582636048874579651901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109004388424032583053101267 163506582636048874579651901)
  ·
    refine ⟨61314968488518327967369463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163506582636048874579651901 61314968488518327967369463)
    ·
      refine ⟨91972452732777491951054195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61314968488518327967369463 91972452732777491951054195)
      ·
        refine ⟨137958679099166237926581293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91972452732777491951054195 137958679099166237926581293)
        ·
          refine ⟨51734504662187339222467985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137958679099166237926581293 51734504662187339222467985)
          ·
            refine ⟨38800878496640504416850989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51734504662187339222467985 38800878496640504416850989)
            ·
              refine ⟨14550329436240189156319121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38800878496640504416850989 14550329436240189156319121)
              ·
                refine ⟨10912747077180141867239341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14550329436240189156319121 10912747077180141867239341)
                ·
                  refine ⟨4092280153942553200214753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10912747077180141867239341 4092280153942553200214753)
                  ·
                    refine ⟨3069210115456914900161065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4092280153942553200214753 3069210115456914900161065)
                    ·
                      refine ⟨2301907586592686175120799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069210115456914900161065 2301907586592686175120799)
                      ·
                        rfl

theorem cell23_4482949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_4482949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482949 prefixEnd_4482949 := by exact prefixLift 4482949
  have htrace : WordTrace (prefixWord ++ tailWord_4482949) baseStart_4482949 baseEnd_4482949 := by
    simpa [prefixWord, tailWord_4482949, baseEnd_4482949] using wordTrace_append hprefix tailTrace_4482949
  have hstable : (prefixWord ++ tailWord_4482949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482949).length < 2 ^ (prefixWord ++ tailWord_4482949).sum := by decide
  have hdescent : baseEnd_4482949 < baseStart_4482949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482969 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 1, 2, 3]
def baseStart_4482969 : Nat := 118140960795 + 4482969 * 2 ^ 59
def prefixEnd_4482969 : Nat := 4983230072969 + 3 ^ 40 * 4482969 * 2
def baseEnd_4482969 : Nat := 2301917856205776096870707

theorem tailTrace_4482969 : CollatzResearch.WordTrace tailWord_4482969 prefixEnd_4482969 2301917856205776096870707 := by
  unfold tailWord_4482969
  simp only [CollatzResearch.WordTrace]
  refine ⟨163507312095976417995379961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109004874730650945330253307 163507312095976417995379961)
  ·
    refine ⟨122630484071982313496534971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163507312095976417995379961 122630484071982313496534971)
    ·
      refine ⟨183945726107973470244802457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122630484071982313496534971 183945726107973470244802457)
      ·
        refine ⟨137959294580980102683601843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183945726107973470244802457 137959294580980102683601843)
        ·
          refine ⟨206938941871470154025402765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137959294580980102683601843 206938941871470154025402765)
          ·
            refine ⟨77602103201801307759526037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206938941871470154025402765 77602103201801307759526037)
            ·
              refine ⟨3637598587584436301227783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77602103201801307759526037 3637598587584436301227783)
              ·
                refine ⟨5456397881376654451841675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3637598587584436301227783 5456397881376654451841675)
                ·
                  refine ⟨8184596822064981677762513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5456397881376654451841675 8184596822064981677762513)
                  ·
                    refine ⟨6138447616548736258321885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8184596822064981677762513 6138447616548736258321885)
                    ·
                      refine ⟨2301917856205776096870707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6138447616548736258321885 2301917856205776096870707)
                      ·
                        rfl

theorem cell23_4482969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_4482969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482969 prefixEnd_4482969 := by exact prefixLift 4482969
  have htrace : WordTrace (prefixWord ++ tailWord_4482969) baseStart_4482969 baseEnd_4482969 := by
    simpa [prefixWord, tailWord_4482969, baseEnd_4482969] using wordTrace_append hprefix tailTrace_4482969
  have hstable : (prefixWord ++ tailWord_4482969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482969).length < 2 ^ (prefixWord ++ tailWord_4482969).sum := by decide
  have hdescent : baseEnd_4482969 < baseStart_4482969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482983 : List Nat := [1, 1, 6, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_4482983 : Nat := 118140960795 + 4482983 * 2 ^ 59
def prefixEnd_4482983 : Nat := 4983230072969 + 3 ^ 40 * 4482983 * 2
def baseEnd_4482983 : Nat := 2301925044934939042095643

theorem tailTrace_4482983 : CollatzResearch.WordTrace tailWord_4482983 prefixEnd_4482983 2301925044934939042095643 := by
  unfold tailWord_4482983
  simp only [CollatzResearch.WordTrace]
  refine ⟨163507822717925698386389603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109005215145283798924259735 163507822717925698386389603)
  ·
    refine ⟨245261734076888547579584405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163507822717925698386389603 245261734076888547579584405)
    ·
      refine ⟨11496643784854150667793019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 245261734076888547579584405 11496643784854150667793019)
      ·
        refine ⟨17244965677281226001689529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11496643784854150667793019 17244965677281226001689529)
        ·
          refine ⟨12933724257960919501267147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17244965677281226001689529 12933724257960919501267147)
          ·
            refine ⟨19400586386941379251900721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12933724257960919501267147 19400586386941379251900721)
            ·
              refine ⟨14550439790206034438925541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19400586386941379251900721 14550439790206034438925541)
              ·
                refine ⟨2728207460663631457298539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14550439790206034438925541 2728207460663631457298539)
                ·
                  refine ⟨4092311190995447185947809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728207460663631457298539 4092311190995447185947809)
                  ·
                    refine ⟨3069233393246585389460857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4092311190995447185947809 3069233393246585389460857)
                    ·
                      refine ⟨2301925044934939042095643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069233393246585389460857 2301925044934939042095643)
                      ·
                        rfl

theorem cell23_4482983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_4482983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482983 prefixEnd_4482983 := by exact prefixLift 4482983
  have htrace : WordTrace (prefixWord ++ tailWord_4482983) baseStart_4482983 baseEnd_4482983 := by
    simpa [prefixWord, tailWord_4482983, baseEnd_4482983] using wordTrace_append hprefix tailTrace_4482983
  have hstable : (prefixWord ++ tailWord_4482983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482983).length < 2 ^ (prefixWord ++ tailWord_4482983).sum := by decide
  have hdescent : baseEnd_4482983 < baseStart_4482983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483075 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 1, 7]
def baseStart_4483075 : Nat := 118140960795 + 4483075 * 2 ^ 59
def prefixEnd_4483075 : Nat := 4983230072969 + 3 ^ 40 * 4483075 * 2
def baseEnd_4483075 : Nat := 767324095051717560715073

theorem tailTrace_4483075 : CollatzResearch.WordTrace tailWord_4483075 prefixEnd_4483075 767324095051717560715073 := by
  unfold tailWord_4483075
  simp only [CollatzResearch.WordTrace]
  refine ⟨163511178233592398098738679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109007452155728265399159119 163511178233592398098738679)
  ·
    refine ⟨245266767350388597148108019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163511178233592398098738679 245266767350388597148108019)
    ·
      refine ⟨367900151025582895722162029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245266767350388597148108019 367900151025582895722162029)
      ·
        refine ⟨137962556634593585895810761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367900151025582895722162029 137962556634593585895810761)
        ·
          refine ⟨103471917475945189421858071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137962556634593585895810761 103471917475945189421858071)
          ·
            refine ⟨155207876213917784132787107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103471917475945189421858071 155207876213917784132787107)
            ·
              refine ⟨232811814320876676199180661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155207876213917784132787107 232811814320876676199180661)
              ·
                refine ⟨21826107592582188393673187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232811814320876676199180661 21826107592582188393673187)
                ·
                  refine ⟨32739161388873282590509781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21826107592582188393673187 32739161388873282590509781)
                  ·
                    refine ⟨767324095051717560715073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32739161388873282590509781 767324095051717560715073)
                    ·
                      rfl

theorem cell23_4483075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 7].length) (baseStart_4483075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483075 prefixEnd_4483075 := by exact prefixLift 4483075
  have htrace : WordTrace (prefixWord ++ tailWord_4483075) baseStart_4483075 baseEnd_4483075 := by
    simpa [prefixWord, tailWord_4483075, baseEnd_4483075] using wordTrace_append hprefix tailTrace_4483075
  have hstable : (prefixWord ++ tailWord_4483075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483075).length < 2 ^ (prefixWord ++ tailWord_4483075).sum := by decide
  have hdescent : baseEnd_4483075 < baseStart_4483075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483129 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4483129 : Nat := 118140960795 + 4483129 * 2 ^ 59
def prefixEnd_4483129 : Nat := 4983230072969 + 3 ^ 40 * 4483129 * 2
def baseEnd_4483129 : Nat := 2302000013110495470869971

theorem tailTrace_4483129 : CollatzResearch.WordTrace tailWord_4483129 prefixEnd_4483129 2302000013110495470869971 := by
  unfold tailWord_4483129
  simp only [CollatzResearch.WordTrace]
  refine ⟨163513147775396765321204441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109008765183597843547469627 163513147775396765321204441)
  ·
    refine ⟨122634860831547573990903331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163513147775396765321204441 122634860831547573990903331)
    ·
      refine ⟨183952291247321360986354997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122634860831547573990903331 183952291247321360986354997)
      ·
        refine ⟨17245527304436377592470781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183952291247321360986354997 17245527304436377592470781)
        ·
          refine ⟨6467072739163641597176543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17245527304436377592470781 6467072739163641597176543)
          ·
            refine ⟨9700609108745462395764815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467072739163641597176543 9700609108745462395764815)
            ·
              refine ⟨14550913663118193593647223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700609108745462395764815 14550913663118193593647223)
              ·
                refine ⟨21826370494677290390470835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14550913663118193593647223 21826370494677290390470835)
                ·
                  refine ⟨32739555742015935585706253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21826370494677290390470835 32739555742015935585706253)
                  ·
                    refine ⟨12277333403255975844639845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32739555742015935585706253 12277333403255975844639845)
                    ·
                      refine ⟨2302000013110495470869971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12277333403255975844639845 2302000013110495470869971)
                      ·
                        rfl

theorem cell23_4483129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4483129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483129 prefixEnd_4483129 := by exact prefixLift 4483129
  have htrace : WordTrace (prefixWord ++ tailWord_4483129) baseStart_4483129 baseEnd_4483129 := by
    simpa [prefixWord, tailWord_4483129, baseEnd_4483129] using wordTrace_append hprefix tailTrace_4483129
  have hstable : (prefixWord ++ tailWord_4483129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483129).length < 2 ^ (prefixWord ++ tailWord_4483129).sum := by decide
  have hdescent : baseEnd_4483129 < baseStart_4483129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483190 : List Nat := [5, 1, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_4483190 : Nat := 118140960795 + 4483190 * 2 ^ 59
def prefixEnd_4483190 : Nat := 4983230072969 + 3 ^ 40 * 4483190 * 2
def baseEnd_4483190 : Nat := 767343778476806577402397

theorem tailTrace_4483190 : CollatzResearch.WordTrace tailWord_4483190 prefixEnd_4483190 767343778476806577402397 := by
  unfold tailWord_4483190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219710789260985796198439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109010248418783848492783349 10219710789260985796198439)
  ·
    refine ⟨15329566183891478694297659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10219710789260985796198439 15329566183891478694297659)
    ·
      refine ⟨22994349275837218041446489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15329566183891478694297659 22994349275837218041446489)
      ·
        refine ⟨17245761956877913531084867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22994349275837218041446489 17245761956877913531084867)
        ·
          refine ⟨25868642935316870296627301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17245761956877913531084867 25868642935316870296627301)
          ·
            refine ⟨4850370550371913180617619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25868642935316870296627301 4850370550371913180617619)
            ·
              refine ⟨7275555825557869770926429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850370550371913180617619 7275555825557869770926429)
              ·
                refine ⟨2728333434584201164097411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7275555825557869770926429 2728333434584201164097411)
                ·
                  refine ⟨4092500151876301746146117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728333434584201164097411 4092500151876301746146117)
                  ·
                    refine ⟨767343778476806577402397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4092500151876301746146117 767343778476806577402397)
                    ·
                      rfl

theorem cell23_4483190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_4483190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483190 prefixEnd_4483190 := by exact prefixLift 4483190
  have htrace : WordTrace (prefixWord ++ tailWord_4483190) baseStart_4483190 baseEnd_4483190 := by
    simpa [prefixWord, tailWord_4483190, baseEnd_4483190] using wordTrace_append hprefix tailTrace_4483190
  have hstable : (prefixWord ++ tailWord_4483190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483190).length < 2 ^ (prefixWord ++ tailWord_4483190).sum := by decide
  have hdescent : baseEnd_4483190 < baseStart_4483190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483220 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 6]
def baseStart_4483220 : Nat := 118140960795 + 4483220 * 2 ^ 59
def prefixEnd_4483220 : Nat := 4983230072969 + 3 ^ 40 * 4483220 * 2
def baseEnd_4483220 : Nat := 255782971094450512759117

theorem tailTrace_4483220 : CollatzResearch.WordTrace tailWord_4483220 prefixEnd_4483220 255782971094450512759117 := by
  unfold tailWord_4483220
  simp only [CollatzResearch.WordTrace]
  refine ⟨81758233409033543931383557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109010977878711391908511409 81758233409033543931383557)
  ·
    refine ⟨15329668764193789487134417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81758233409033543931383557 15329668764193789487134417)
    ·
      refine ⟨11497251573145342115350813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15329668764193789487134417 11497251573145342115350813)
      ·
        refine ⟨4311469339929503293256555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11497251573145342115350813 4311469339929503293256555)
        ·
          refine ⟨6467204009894254939884833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311469339929503293256555 6467204009894254939884833)
          ·
            refine ⟨4850403007420691204913625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6467204009894254939884833 4850403007420691204913625)
            ·
              refine ⟨3637802255565518403685219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4850403007420691204913625 3637802255565518403685219)
              ·
                refine ⟨5456703383348277605527829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3637802255565518403685219 5456703383348277605527829)
                ·
                  refine ⟨255782971094450512759117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5456703383348277605527829 255782971094450512759117)
                  ·
                    rfl

theorem cell23_4483220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_4483220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483220 prefixEnd_4483220 := by exact prefixLift 4483220
  have htrace : WordTrace (prefixWord ++ tailWord_4483220) baseStart_4483220 baseEnd_4483220 := by
    simpa [prefixWord, tailWord_4483220, baseEnd_4483220] using wordTrace_append hprefix tailTrace_4483220
  have hstable : (prefixWord ++ tailWord_4483220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483220).length < 2 ^ (prefixWord ++ tailWord_4483220).sum := by decide
  have hdescent : baseEnd_4483220 < baseStart_4483220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483236 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_4483236 : Nat := 118140960795 + 4483236 * 2 ^ 59
def prefixEnd_4483236 : Nat := 4983230072969 + 3 ^ 40 * 4483236 * 2
def baseEnd_4483236 : Nat := 2302054955540526552231979

theorem tailTrace_4483236 : CollatzResearch.WordTrace tailWord_4483236 prefixEnd_4483236 2302054955540526552231979 := by
  unfold tailWord_4483236
  simp only [CollatzResearch.WordTrace]
  refine ⟨81758525193004561297674781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109011366924006081730233041 81758525193004561297674781)
  ·
    refine ⟨30659446947376710486628043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81758525193004561297674781 30659446947376710486628043)
    ·
      refine ⟨45989170421065065729942065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30659446947376710486628043 45989170421065065729942065)
      ·
        refine ⟨34491877815798799297456549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45989170421065065729942065 34491877815798799297456549)
        ·
          refine ⟨6467227090462274868273103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34491877815798799297456549 6467227090462274868273103)
          ·
            refine ⟨9700840635693412302409655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467227090462274868273103 9700840635693412302409655)
            ·
              refine ⟨14551260953540118453614483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700840635693412302409655 14551260953540118453614483)
              ·
                refine ⟨21826891430310177680421725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14551260953540118453614483 21826891430310177680421725)
                ·
                  refine ⟨8185084286366316630158147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21826891430310177680421725 8185084286366316630158147)
                  ·
                    refine ⟨12277626429549474945237221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8185084286366316630158147 12277626429549474945237221)
                    ·
                      refine ⟨2302054955540526552231979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12277626429549474945237221 2302054955540526552231979)
                      ·
                        rfl

theorem cell23_4483236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_4483236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483236 prefixEnd_4483236 := by exact prefixLift 4483236
  have htrace : WordTrace (prefixWord ++ tailWord_4483236) baseStart_4483236 baseEnd_4483236 := by
    simpa [prefixWord, tailWord_4483236, baseEnd_4483236] using wordTrace_append hprefix tailTrace_4483236
  have hstable : (prefixWord ++ tailWord_4483236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483236).length < 2 ^ (prefixWord ++ tailWord_4483236).sum := by decide
  have hdescent : baseEnd_4483236 < baseStart_4483236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483296 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 3, 3, 2]
def baseStart_4483296 : Nat := 118140960795 + 4483296 * 2 ^ 59
def prefixEnd_4483296 : Nat := 4983230072969 + 3 ^ 40 * 4483296 * 2
def baseEnd_4483296 : Nat := 2302085764379796317481703

theorem tailTrace_4483296 : CollatzResearch.WordTrace tailWord_4483296 prefixEnd_4483296 2302085764379796317481703 := by
  unfold tailWord_4483296
  simp only [CollatzResearch.WordTrace]
  refine ⟨81759619382895876421266871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109012825843861168561689161 81759619382895876421266871)
  ·
    refine ⟨122639429074343814631900307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81759619382895876421266871 122639429074343814631900307)
    ·
      refine ⟨183959143611515721947850461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122639429074343814631900307 183959143611515721947850461)
      ·
        refine ⟨68984678854318395730443923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183959143611515721947850461 68984678854318395730443923)
        ·
          refine ⟨103477018281477593595665885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68984678854318395730443923 103477018281477593595665885)
          ·
            refine ⟨38803881855554097598374707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103477018281477593595665885 38803881855554097598374707)
            ·
              refine ⟨58205822783331146397562061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38803881855554097598374707 58205822783331146397562061)
              ·
                refine ⟨21827183543749179899085773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58205822783331146397562061 21827183543749179899085773)
                ·
                  refine ⟨8185193828905942462157165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21827183543749179899085773 8185193828905942462157165)
                  ·
                    refine ⟨3069447685839728423308937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8185193828905942462157165 3069447685839728423308937)
                    ·
                      refine ⟨2302085764379796317481703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069447685839728423308937 2302085764379796317481703)
                      ·
                        rfl

theorem cell23_4483296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_4483296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483296 prefixEnd_4483296 := by exact prefixLift 4483296
  have htrace : WordTrace (prefixWord ++ tailWord_4483296) baseStart_4483296 baseEnd_4483296 := by
    simpa [prefixWord, tailWord_4483296, baseEnd_4483296] using wordTrace_append hprefix tailTrace_4483296
  have hstable : (prefixWord ++ tailWord_4483296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483296).length < 2 ^ (prefixWord ++ tailWord_4483296).sum := by decide
  have hdescent : baseEnd_4483296 < baseStart_4483296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483339 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4]
def baseStart_4483339 : Nat := 118140960795 + 4483339 * 2 ^ 59
def prefixEnd_4483339 : Nat := 4983230072969 + 3 ^ 40 * 4483339 * 2
def baseEnd_4483339 : Nat := 2302107844047939649244005

theorem tailTrace_4483339 : CollatzResearch.WordTrace tailWord_4483339 prefixEnd_4483339 2302107844047939649244005 := by
  unfold tailWord_4483339
  simp only [CollatzResearch.WordTrace]
  refine ⟨163520807104635971186349071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109013871403090647457566047 163520807104635971186349071)
  ·
    refine ⟨245281210656953956779523607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163520807104635971186349071 245281210656953956779523607)
    ·
      refine ⟨367921815985430935169285411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245281210656953956779523607 367921815985430935169285411)
      ·
        refine ⟨551882723978146402753928117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367921815985430935169285411 551882723978146402753928117)
        ·
          refine ⟨51739005372951225258180761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 551882723978146402753928117 51739005372951225258180761)
          ·
            refine ⟨38804254029713418943635571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51739005372951225258180761 38804254029713418943635571)
            ·
              refine ⟨58206381044570128415453357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38804254029713418943635571 58206381044570128415453357)
              ·
                refine ⟨21827392891713798155795009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58206381044570128415453357 21827392891713798155795009)
                ·
                  refine ⟨16370544668785348616846257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21827392891713798155795009 16370544668785348616846257)
                  ·
                    refine ⟨12277908501589011462634693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16370544668785348616846257 12277908501589011462634693)
                    ·
                      refine ⟨2302107844047939649244005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12277908501589011462634693 2302107844047939649244005)
                      ·
                        rfl

theorem cell23_4483339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_4483339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483339 prefixEnd_4483339 := by exact prefixLift 4483339
  have htrace : WordTrace (prefixWord ++ tailWord_4483339) baseStart_4483339 baseEnd_4483339 := by
    simpa [prefixWord, tailWord_4483339, baseEnd_4483339] using wordTrace_append hprefix tailTrace_4483339
  have hstable : (prefixWord ++ tailWord_4483339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483339).length < 2 ^ (prefixWord ++ tailWord_4483339).sum := by decide
  have hdescent : baseEnd_4483339 < baseStart_4483339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483343 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 2, 2, 2]
def baseStart_4483343 : Nat := 118140960795 + 4483343 * 2 ^ 59
def prefixEnd_4483343 : Nat := 4983230072969 + 3 ^ 40 * 4483343 * 2
def baseEnd_4483343 : Nat := 2302109897970557633593987

theorem tailTrace_4483343 : CollatzResearch.WordTrace tailWord_4483343 prefixEnd_4483343 2302109897970557633593987 := by
  unfold tailWord_4483343
  simp only [CollatzResearch.WordTrace]
  refine ⟨163520952996621479869494683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109013968664414319912996455 163520952996621479869494683)
  ·
    refine ⟨245281429494932219804242025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163520952996621479869494683 245281429494932219804242025)
    ·
      refine ⟨183961072121199164853181519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245281429494932219804242025 183961072121199164853181519)
      ·
        refine ⟨275941608181798747279772279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183961072121199164853181519 275941608181798747279772279)
        ·
          refine ⟨413912412272698120919658419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275941608181798747279772279 413912412272698120919658419)
          ·
            refine ⟨620868618409047181379487629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413912412272698120919658419 620868618409047181379487629)
            ·
              refine ⟨232825731903392693017307861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620868618409047181379487629 232825731903392693017307861)
              ·
                refine ⟨5456853091485766242593153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232825731903392693017307861 5456853091485766242593153)
                ·
                  refine ⟨4092639818614324681944865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5456853091485766242593153 4092639818614324681944865)
                  ·
                    refine ⟨3069479863960743511458649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4092639818614324681944865 3069479863960743511458649)
                    ·
                      refine ⟨2302109897970557633593987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069479863960743511458649 2302109897970557633593987)
                      ·
                        rfl

theorem cell23_4483343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 2, 2].length) (baseStart_4483343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483343 prefixEnd_4483343 := by exact prefixLift 4483343
  have htrace : WordTrace (prefixWord ++ tailWord_4483343) baseStart_4483343 baseEnd_4483343 := by
    simpa [prefixWord, tailWord_4483343, baseEnd_4483343] using wordTrace_append hprefix tailTrace_4483343
  have hstable : (prefixWord ++ tailWord_4483343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483343).length < 2 ^ (prefixWord ++ tailWord_4483343).sum := by decide
  have hdescent : baseEnd_4483343 < baseStart_4483343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483349 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 7]
def baseStart_4483349 : Nat := 118140960795 + 4483349 * 2 ^ 59
def prefixEnd_4483349 : Nat := 4983230072969 + 3 ^ 40 * 4483349 * 2
def baseEnd_4483349 : Nat := 255790330983831623346551

theorem tailTrace_4483349 : CollatzResearch.WordTrace tailWord_4483349 prefixEnd_4483349 255790330983831623346551 := by
  unfold tailWord_4483349
  simp only [CollatzResearch.WordTrace]
  refine ⟨163521171834599742894213101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109014114556399828596142067 163521171834599742894213101)
  ·
    refine ⟨61320439437974903585329913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163521171834599742894213101 61320439437974903585329913)
    ·
      refine ⟨45990329578481177688997435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61320439437974903585329913 45990329578481177688997435)
      ·
        refine ⟨68985494367721766533496153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45990329578481177688997435 68985494367721766533496153)
        ·
          refine ⟨51739120775791324900122115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68985494367721766533496153 51739120775791324900122115)
          ·
            refine ⟨77608681163686987350183173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51739120775791324900122115 77608681163686987350183173)
            ·
              refine ⟨14551627718191310128159345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77608681163686987350183173 14551627718191310128159345)
              ·
                refine ⟨10913720788643482596119509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14551627718191310128159345 10913720788643482596119509)
                ·
                  refine ⟨255790330983831623346551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10913720788643482596119509 255790330983831623346551)
                  ·
                    rfl

theorem cell23_4483349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_4483349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483349 prefixEnd_4483349 := by exact prefixLift 4483349
  have htrace : WordTrace (prefixWord ++ tailWord_4483349) baseStart_4483349 baseEnd_4483349 := by
    simpa [prefixWord, tailWord_4483349, baseEnd_4483349] using wordTrace_append hprefix tailTrace_4483349
  have hstable : (prefixWord ++ tailWord_4483349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483349).length < 2 ^ (prefixWord ++ tailWord_4483349).sum := by decide
  have hdescent : baseEnd_4483349 < baseStart_4483349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483413 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_4483413 : Nat := 118140960795 + 4483413 * 2 ^ 59
def prefixEnd_4483413 : Nat := 4983230072969 + 3 ^ 40 * 4483413 * 2
def baseEnd_4483413 : Nat := 767381947205457453239555

theorem tailTrace_4483413 : CollatzResearch.WordTrace tailWord_4483413 prefixEnd_4483413 767381947205457453239555 := by
  unfold tailWord_4483413
  simp only [CollatzResearch.WordTrace]
  refine ⟨163523506106367881824542893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109015670737578587883028595 163523506106367881824542893)
  ·
    refine ⟨61321314789887955684203585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163523506106367881824542893 61321314789887955684203585)
    ·
      refine ⟨45990986092415966763152689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61321314789887955684203585 45990986092415966763152689)
      ·
        refine ⟨34493239569311975072364517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45990986092415966763152689 34493239569311975072364517)
        ·
          refine ⟨6467482419245995326068347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34493239569311975072364517 6467482419245995326068347)
          ·
            refine ⟨9701223628868992989102521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467482419245995326068347 9701223628868992989102521)
            ·
              refine ⟨7275917721651744741826891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9701223628868992989102521 7275917721651744741826891)
              ·
                refine ⟨10913876582477617112740337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7275917721651744741826891 10913876582477617112740337)
                ·
                  refine ⟨8185407436858212834555253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10913876582477617112740337 8185407436858212834555253)
                  ·
                    refine ⟨767381947205457453239555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8185407436858212834555253 767381947205457453239555)
                    ·
                      rfl

theorem cell23_4483413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_4483413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483413 prefixEnd_4483413 := by exact prefixLift 4483413
  have htrace : WordTrace (prefixWord ++ tailWord_4483413) baseStart_4483413 baseEnd_4483413 := by
    simpa [prefixWord, tailWord_4483413, baseEnd_4483413] using wordTrace_append hprefix tailTrace_4483413
  have hstable : (prefixWord ++ tailWord_4483413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483413).length < 2 ^ (prefixWord ++ tailWord_4483413).sum := by decide
  have hdescent : baseEnd_4483413 < baseStart_4483413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483416 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 3, 6, 2]
def baseStart_4483416 : Nat := 118140960795 + 4483416 * 2 ^ 59
def prefixEnd_4483416 : Nat := 4983230072969 + 3 ^ 40 * 4483416 * 2
def baseEnd_4483416 : Nat := 2302147382058335847981151

theorem tailTrace_4483416 : CollatzResearch.WordTrace tailWord_4483416 prefixEnd_4483416 2302147382058335847981151 := by
  unfold tailWord_4483416
  simp only [CollatzResearch.WordTrace]
  refine ⟨81761807762678506668451051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109015743683571342224601401 81761807762678506668451051)
  ·
    refine ⟨122642711644017760002676577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81761807762678506668451051 122642711644017760002676577)
    ·
      refine ⟨91982033733013320002007433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122642711644017760002676577 91982033733013320002007433)
      ·
        refine ⟨68986525299759990001505575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91982033733013320002007433 68986525299759990001505575)
        ·
          refine ⟨103479787949639985002258363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68986525299759990001505575 103479787949639985002258363)
          ·
            refine ⟨155219681924459977503387545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103479787949639985002258363 155219681924459977503387545)
            ·
              refine ⟨116414761443344983127540659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155219681924459977503387545 116414761443344983127540659)
              ·
                refine ⟨174622142165017474691310989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116414761443344983127540659 174622142165017474691310989)
                ·
                  refine ⟨65483303311881553009241621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174622142165017474691310989 65483303311881553009241621)
                  ·
                    refine ⟨3069529842744447797308201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65483303311881553009241621 3069529842744447797308201)
                    ·
                      refine ⟨2302147382058335847981151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069529842744447797308201 2302147382058335847981151)
                      ·
                        rfl

theorem cell23_4483416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_4483416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483416 prefixEnd_4483416 := by exact prefixLift 4483416
  have htrace : WordTrace (prefixWord ++ tailWord_4483416) baseStart_4483416 baseEnd_4483416 := by
    simpa [prefixWord, tailWord_4483416, baseEnd_4483416] using wordTrace_append hprefix tailTrace_4483416
  have hstable : (prefixWord ++ tailWord_4483416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483416).length < 2 ^ (prefixWord ++ tailWord_4483416).sum := by decide
  have hdescent : baseEnd_4483416 < baseStart_4483416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483443 : List Nat := [1, 1, 1, 2, 2, 1, 2, 8, 1, 4]
def baseStart_4483443 : Nat := 118140960795 + 4483443 * 2 ^ 59
def prefixEnd_4483443 : Nat := 4983230072969 + 3 ^ 40 * 4483443 * 2
def baseEnd_4483443 : Nat := 767387082012002414114509

theorem tailTrace_4483443 : CollatzResearch.WordTrace tailWord_4483443 prefixEnd_4483443 767387082012002414114509 := by
  unfold tailWord_4483443
  simp only [CollatzResearch.WordTrace]
  refine ⟨163524600296259196948134983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109016400197506131298756655 163524600296259196948134983)
  ·
    refine ⟨245286900444388795422202475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163524600296259196948134983 245286900444388795422202475)
    ·
      refine ⟨367930350666583193133303713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245286900444388795422202475 367930350666583193133303713)
      ·
        refine ⟨275947762999937394849977785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367930350666583193133303713 275947762999937394849977785)
        ·
          refine ⟨206960822249953046137483339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275947762999937394849977785 206960822249953046137483339)
          ·
            refine ⟨310441233374929569206225009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206960822249953046137483339 310441233374929569206225009)
            ·
              refine ⟨232830925031197176904668757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310441233374929569206225009 232830925031197176904668757)
              ·
                refine ⟨2728487402709341916851587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 232830925031197176904668757 2728487402709341916851587)
                ·
                  refine ⟨4092731104064012875277381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728487402709341916851587 4092731104064012875277381)
                  ·
                    refine ⟨767387082012002414114509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4092731104064012875277381 767387082012002414114509)
                    ·
                      rfl

theorem cell23_4483443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 4].length) (baseStart_4483443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483443 prefixEnd_4483443 := by exact prefixLift 4483443
  have htrace : WordTrace (prefixWord ++ tailWord_4483443) baseStart_4483443 baseEnd_4483443 := by
    simpa [prefixWord, tailWord_4483443, baseEnd_4483443] using wordTrace_append hprefix tailTrace_4483443
  have hstable : (prefixWord ++ tailWord_4483443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483443).length < 2 ^ (prefixWord ++ tailWord_4483443).sum := by decide
  have hdescent : baseEnd_4483443 < baseStart_4483443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483470 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4483470 : Nat := 118140960795 + 4483470 * 2 ^ 59
def prefixEnd_4483470 : Nat := 4983230072969 + 3 ^ 40 * 4483470 * 2
def baseEnd_4483470 : Nat := 2302175110013678636705903

theorem tailTrace_4483470 : CollatzResearch.WordTrace tailWord_4483470 prefixEnd_4483470 2302175110013678636705903 := by
  unfold tailWord_4483470
  simp only [CollatzResearch.WordTrace]
  refine ⟨20440698133395172569920983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109017056711440920372911909 20440698133395172569920983)
  ·
    refine ⟨30661047200092758854881475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20440698133395172569920983 30661047200092758854881475)
    ·
      refine ⟨45991570800139138282322213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30661047200092758854881475 45991570800139138282322213)
      ·
        refine ⟨8623419525026088427935415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45991570800139138282322213 8623419525026088427935415)
        ·
          refine ⟨12935129287539132641903123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8623419525026088427935415 12935129287539132641903123)
          ·
            refine ⟨19402693931308698962854685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12935129287539132641903123 19402693931308698962854685)
            ·
              refine ⟨7276010224240762111070507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19402693931308698962854685 7276010224240762111070507)
              ·
                refine ⟨10914015336361143166605761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7276010224240762111070507 10914015336361143166605761)
                ·
                  refine ⟨8185511502270857374954321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10914015336361143166605761 8185511502270857374954321)
                  ·
                    refine ⟨6139133626703143031215741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8185511502270857374954321 6139133626703143031215741)
                    ·
                      refine ⟨2302175110013678636705903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139133626703143031215741 2302175110013678636705903)
                      ·
                        rfl

theorem cell23_4483470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4483470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483470 prefixEnd_4483470 := by exact prefixLift 4483470
  have htrace : WordTrace (prefixWord ++ tailWord_4483470) baseStart_4483470 baseEnd_4483470 := by
    simpa [prefixWord, tailWord_4483470, baseEnd_4483470] using wordTrace_append hprefix tailTrace_4483470
  have hstable : (prefixWord ++ tailWord_4483470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483470).length < 2 ^ (prefixWord ++ tailWord_4483470).sum := by decide
  have hdescent : baseEnd_4483470 < baseStart_4483470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483493 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 4, 3, 2]
def baseStart_4483493 : Nat := 118140960795 + 4483493 * 2 ^ 59
def prefixEnd_4483493 : Nat := 4983230072969 + 3 ^ 40 * 4483493 * 2
def baseEnd_4483493 : Nat := 2302186920068732046718297

theorem tailTrace_4483493 : CollatzResearch.WordTrace tailWord_4483493 prefixEnd_4483493 2302186920068732046718297 := by
  unfold tailWord_4483493
  simp only [CollatzResearch.WordTrace]
  refine ⟨163526423946078055487455133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109017615964052036991636755 163526423946078055487455133)
  ·
    refine ⟨61322408979779270807795675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163526423946078055487455133 61322408979779270807795675)
    ·
      refine ⟨91983613469668906211693513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61322408979779270807795675 91983613469668906211693513)
      ·
        refine ⟨68987710102251679658770135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91983613469668906211693513 68987710102251679658770135)
        ·
          refine ⟨103481565153377519488155203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68987710102251679658770135 103481565153377519488155203)
          ·
            refine ⟨155222347730066279232232805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103481565153377519488155203 155222347730066279232232805)
            ·
              refine ⟨29104190199387427356043651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155222347730066279232232805 29104190199387427356043651)
              ·
                refine ⟨43656285299081141034065477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29104190199387427356043651 43656285299081141034065477)
                ·
                  refine ⟨8185553493577713943887277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43656285299081141034065477 8185553493577713943887277)
                  ·
                    refine ⟨3069582560091642728957729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8185553493577713943887277 3069582560091642728957729)
                    ·
                      refine ⟨2302186920068732046718297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069582560091642728957729 2302186920068732046718297)
                      ·
                        rfl

theorem cell23_4483493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_4483493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483493 prefixEnd_4483493 := by exact prefixLift 4483493
  have htrace : WordTrace (prefixWord ++ tailWord_4483493) baseStart_4483493 baseEnd_4483493 := by
    simpa [prefixWord, tailWord_4483493, baseEnd_4483493] using wordTrace_append hprefix tailTrace_4483493
  have hstable : (prefixWord ++ tailWord_4483493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483493).length < 2 ^ (prefixWord ++ tailWord_4483493).sum := by decide
  have hdescent : baseEnd_4483493 < baseStart_4483493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483540 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_4483540 : Nat := 118140960795 + 4483540 * 2 ^ 59
def prefixEnd_4483540 : Nat := 4983230072969 + 3 ^ 40 * 4483540 * 2
def baseEnd_4483540 : Nat := 2302211053659493362830581

theorem tailTrace_4483540 : CollatzResearch.WordTrace tailWord_4483540 prefixEnd_4483540 2302211053659493362830581 := by
  unfold tailWord_4483540
  simp only [CollatzResearch.WordTrace]
  refine ⟨81764069088453891257208037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109018758784605188342944049 81764069088453891257208037)
  ·
    refine ⟨15330762954085104610726507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81764069088453891257208037 15330762954085104610726507)
    ·
      refine ⟨22996144431127656916089761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15330762954085104610726507 22996144431127656916089761)
      ·
        refine ⟨17247108323345742687067321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22996144431127656916089761 17247108323345742687067321)
        ·
          refine ⟨12935331242509307015300491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17247108323345742687067321 12935331242509307015300491)
          ·
            refine ⟨19402996863763960522950737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12935331242509307015300491 19402996863763960522950737)
            ·
              refine ⟨14552247647822970392213053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19402996863763960522950737 14552247647822970392213053)
              ·
                refine ⟨5457092867933613897079895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14552247647822970392213053 5457092867933613897079895)
                ·
                  refine ⟨8185639301900420845619843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5457092867933613897079895 8185639301900420845619843)
                  ·
                    refine ⟨12278458952850631268429765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8185639301900420845619843 12278458952850631268429765)
                    ·
                      refine ⟨2302211053659493362830581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12278458952850631268429765 2302211053659493362830581)
                      ·
                        rfl

theorem cell23_4483540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_4483540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483540 prefixEnd_4483540 := by exact prefixLift 4483540
  have htrace : WordTrace (prefixWord ++ tailWord_4483540) baseStart_4483540 baseEnd_4483540 := by
    simpa [prefixWord, tailWord_4483540, baseEnd_4483540] using wordTrace_append hprefix tailTrace_4483540
  have hstable : (prefixWord ++ tailWord_4483540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483540).length < 2 ^ (prefixWord ++ tailWord_4483540).sum := by decide
  have hdescent : baseEnd_4483540 < baseStart_4483540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483613 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4483613 : Nat := 118140960795 + 4483613 * 2 ^ 59
def prefixEnd_4483613 : Nat := 4983230072969 + 3 ^ 40 * 4483613 * 2
def baseEnd_4483613 : Nat := 2302248537747271577217745

theorem tailTrace_4483613 : CollatzResearch.WordTrace tailWord_4483613 prefixEnd_4483613 2302248537747271577217745 := by
  unfold tailWord_4483613
  simp only [CollatzResearch.WordTrace]
  refine ⟨163530800705643315981823493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109020533803762210654548995 163530800705643315981823493)
  ·
    refine ⟨30662025132308121746591905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163530800705643315981823493 30662025132308121746591905)
    ·
      refine ⟨22996518849231091309943929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30662025132308121746591905 22996518849231091309943929)
      ·
        refine ⟨17247389136923318482457947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22996518849231091309943929 17247389136923318482457947)
        ·
          refine ⟨25871083705384977723686921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17247389136923318482457947 25871083705384977723686921)
          ·
            refine ⟨19403312779038733292765191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25871083705384977723686921 19403312779038733292765191)
            ·
              refine ⟨29104969168558099939147787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19403312779038733292765191 29104969168558099939147787)
              ·
                refine ⟨43657453752837149908721681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29104969168558099939147787 43657453752837149908721681)
                ·
                  refine ⟨32743090314627862431541261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43657453752837149908721681 32743090314627862431541261)
                  ·
                    refine ⟨12278658867985448411827973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32743090314627862431541261 12278658867985448411827973)
                    ·
                      refine ⟨2302248537747271577217745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12278658867985448411827973 2302248537747271577217745)
                      ·
                        rfl

theorem cell23_4483613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4483613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483613 prefixEnd_4483613 := by exact prefixLift 4483613
  have htrace : WordTrace (prefixWord ++ tailWord_4483613) baseStart_4483613 baseEnd_4483613 := by
    simpa [prefixWord, tailWord_4483613, baseEnd_4483613] using wordTrace_append hprefix tailTrace_4483613
  have hstable : (prefixWord ++ tailWord_4483613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483613).length < 2 ^ (prefixWord ++ tailWord_4483613).sum := by decide
  have hdescent : baseEnd_4483613 < baseStart_4483613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483663 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 3]
def baseStart_4483663 : Nat := 118140960795 + 4483663 * 2 ^ 59
def prefixEnd_4483663 : Nat := 4983230072969 + 3 ^ 40 * 4483663 * 2
def baseEnd_4483663 : Nat := 2302274211779996381592515

theorem tailTrace_4483663 : CollatzResearch.WordTrace tailWord_4483663 prefixEnd_4483663 2302274211779996381592515 := by
  unfold tailWord_4483663
  simp only [CollatzResearch.WordTrace]
  refine ⟨163532624355462174521143643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109021749570308116347429095 163532624355462174521143643)
  ·
    refine ⟨245298936533193261781715465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163532624355462174521143643 245298936533193261781715465)
    ·
      refine ⟨183974202399894946336286599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245298936533193261781715465 183974202399894946336286599)
      ·
        refine ⟨275961303599842419504429899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183974202399894946336286599 275961303599842419504429899)
        ·
          refine ⟨413941955399763629256644849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275961303599842419504429899 413941955399763629256644849)
          ·
            refine ⟨310456466549822721942483637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413941955399763629256644849 310456466549822721942483637)
            ·
              refine ⟨29105293739045880182107841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 310456466549822721942483637 29105293739045880182107841)
              ·
                refine ⟨21828970304284410136580881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29105293739045880182107841 21828970304284410136580881)
                ·
                  refine ⟨16371727728213307602435661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21828970304284410136580881 16371727728213307602435661)
                  ·
                    refine ⟨6139397898079990350913373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16371727728213307602435661 6139397898079990350913373)
                    ·
                      refine ⟨2302274211779996381592515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139397898079990350913373 2302274211779996381592515)
                      ·
                        rfl

theorem cell23_4483663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_4483663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483663 prefixEnd_4483663 := by exact prefixLift 4483663
  have htrace : WordTrace (prefixWord ++ tailWord_4483663) baseStart_4483663 baseEnd_4483663 := by
    simpa [prefixWord, tailWord_4483663, baseEnd_4483663] using wordTrace_append hprefix tailTrace_4483663
  have hstable : (prefixWord ++ tailWord_4483663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483663).length < 2 ^ (prefixWord ++ tailWord_4483663).sum := by decide
  have hdescent : baseEnd_4483663 < baseStart_4483663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483703 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_4483703 : Nat := 118140960795 + 4483703 * 2 ^ 59
def prefixEnd_4483703 : Nat := 4983230072969 + 3 ^ 40 * 4483703 * 2
def baseEnd_4483703 : Nat := 2302294751006176225092331

theorem tailTrace_4483703 : CollatzResearch.WordTrace tailWord_4483703 prefixEnd_4483703 2302294751006176225092331 := by
  unfold tailWord_4483703
  simp only [CollatzResearch.WordTrace]
  refine ⟨163534083275317261352599763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109022722183544840901733175 163534083275317261352599763)
  ·
    refine ⟨245301124912975892028899645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163534083275317261352599763 245301124912975892028899645)
    ·
      refine ⟨91987921842365959510837367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245301124912975892028899645 91987921842365959510837367)
      ·
        refine ⟨137981882763548939266256051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91987921842365959510837367 137981882763548939266256051)
        ·
          refine ⟨206972824145323408899384077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137981882763548939266256051 206972824145323408899384077)
          ·
            refine ⟨77614809054496278337269029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206972824145323408899384077 77614809054496278337269029)
            ·
              refine ⟨14552776697718052188237943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77614809054496278337269029 14552776697718052188237943)
              ·
                refine ⟨21829165046577078282356915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14552776697718052188237943 21829165046577078282356915)
                ·
                  refine ⟨32743747569865617423535373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21829165046577078282356915 32743747569865617423535373)
                  ·
                    refine ⟨12278905338699606533825765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32743747569865617423535373 12278905338699606533825765)
                    ·
                      refine ⟨2302294751006176225092331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12278905338699606533825765 2302294751006176225092331)
                      ·
                        rfl

theorem cell23_4483703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_4483703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483703 prefixEnd_4483703 := by exact prefixLift 4483703
  have htrace : WordTrace (prefixWord ++ tailWord_4483703) baseStart_4483703 baseEnd_4483703 := by
    simpa [prefixWord, tailWord_4483703, baseEnd_4483703] using wordTrace_append hprefix tailTrace_4483703
  have hstable : (prefixWord ++ tailWord_4483703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483703).length < 2 ^ (prefixWord ++ tailWord_4483703).sum := by decide
  have hdescent : baseEnd_4483703 < baseStart_4483703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483723 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 3]
def baseStart_4483723 : Nat := 118140960795 + 4483723 * 2 ^ 59
def prefixEnd_4483723 : Nat := 4983230072969 + 3 ^ 40 * 4483723 * 2
def baseEnd_4483723 : Nat := 2302305020619266146842239

theorem tailTrace_4483723 : CollatzResearch.WordTrace tailWord_4483723 prefixEnd_4483723 2302305020619266146842239 := by
  unfold tailWord_4483723
  simp only [CollatzResearch.WordTrace]
  refine ⟨163534812735244804768327823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109023208490163203178885215 163534812735244804768327823)
  ·
    refine ⟨245302219102867207152491735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163534812735244804768327823 245302219102867207152491735)
    ·
      refine ⟨367953328654300810728737603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245302219102867207152491735 367953328654300810728737603)
      ·
        refine ⟨551929992981451216093106405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367953328654300810728737603 551929992981451216093106405)
        ·
          refine ⟨103486873684022103017457451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 551929992981451216093106405 103486873684022103017457451)
          ·
            refine ⟨155230310526033154526186177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103486873684022103017457451 155230310526033154526186177)
            ·
              refine ⟨116422732894524865894639633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155230310526033154526186177 116422732894524865894639633)
              ·
                refine ⟨87317049670893649420979725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116422732894524865894639633 87317049670893649420979725)
                ·
                  refine ⟨32743893626585118532867397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87317049670893649420979725 32743893626585118532867397)
                  ·
                    refine ⟨6139480054984709724912637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32743893626585118532867397 6139480054984709724912637)
                    ·
                      refine ⟨2302305020619266146842239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139480054984709724912637 2302305020619266146842239)
                      ·
                        rfl

theorem cell23_4483723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 3].length) (baseStart_4483723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483723 prefixEnd_4483723 := by exact prefixLift 4483723
  have htrace : WordTrace (prefixWord ++ tailWord_4483723) baseStart_4483723 baseEnd_4483723 := by
    simpa [prefixWord, tailWord_4483723, baseEnd_4483723] using wordTrace_append hprefix tailTrace_4483723
  have hstable : (prefixWord ++ tailWord_4483723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483723).length < 2 ^ (prefixWord ++ tailWord_4483723).sum := by decide
  have hdescent : baseEnd_4483723 < baseStart_4483723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483753 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 3]
def baseStart_4483753 : Nat := 118140960795 + 4483753 * 2 ^ 59
def prefixEnd_4483753 : Nat := 4983230072969 + 3 ^ 40 * 4483753 * 2
def baseEnd_4483753 : Nat := 2302320425038901029467101

theorem tailTrace_4483753 : CollatzResearch.WordTrace tailWord_4483753 prefixEnd_4483753 2302320425038901029467101 := by
  unfold tailWord_4483753
  simp only [CollatzResearch.WordTrace]
  refine ⟨163535906925136119891919913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109023937950090746594613275 163535906925136119891919913)
  ·
    refine ⟨122651930193852089918939935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163535906925136119891919913 122651930193852089918939935)
    ·
      refine ⟨183977895290778134878409903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122651930193852089918939935 183977895290778134878409903)
      ·
        refine ⟨275966842936167202317614855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183977895290778134878409903 275966842936167202317614855)
        ·
          refine ⟨413950264404250803476422283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275966842936167202317614855 413950264404250803476422283)
          ·
            refine ⟨620925396606376205214633425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413950264404250803476422283 620925396606376205214633425)
            ·
              refine ⟨465694047454782153910975069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620925396606376205214633425 465694047454782153910975069)
              ·
                refine ⟨174635267795543307716615651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 465694047454782153910975069 174635267795543307716615651)
                ·
                  refine ⟨261952901693314961574923477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174635267795543307716615651 261952901693314961574923477)
                  ·
                    refine ⟨6139521133437069411912269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 261952901693314961574923477 6139521133437069411912269)
                    ·
                      refine ⟨2302320425038901029467101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139521133437069411912269 2302320425038901029467101)
                      ·
                        rfl

theorem cell23_4483753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_4483753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483753 prefixEnd_4483753 := by exact prefixLift 4483753
  have htrace : WordTrace (prefixWord ++ tailWord_4483753) baseStart_4483753 baseEnd_4483753 := by
    simpa [prefixWord, tailWord_4483753, baseEnd_4483753] using wordTrace_append hprefix tailTrace_4483753
  have hstable : (prefixWord ++ tailWord_4483753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483753).length < 2 ^ (prefixWord ++ tailWord_4483753).sum := by decide
  have hdescent : baseEnd_4483753 < baseStart_4483753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483757 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_4483757 : Nat := 118140960795 + 4483757 * 2 ^ 59
def prefixEnd_4483757 : Nat := 4983230072969 + 3 ^ 40 * 4483757 * 2
def baseEnd_4483757 : Nat := 2302322478961519013817083

theorem tailTrace_4483757 : CollatzResearch.WordTrace tailWord_4483757 prefixEnd_4483757 2302322478961519013817083 := by
  unfold tailWord_4483757
  simp only [CollatzResearch.WordTrace]
  refine ⟨163536052817121628575065525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109024035211414419050043683 163536052817121628575065525)
  ·
    refine ⟨15331504951605152678912393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163536052817121628575065525 15331504951605152678912393)
    ·
      refine ⟨11498628713703864509184295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15331504951605152678912393 11498628713703864509184295)
      ·
        refine ⟨17247943070555796763776443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11498628713703864509184295 17247943070555796763776443)
        ·
          refine ⟨25871914605833695145664665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17247943070555796763776443 25871914605833695145664665)
          ·
            refine ⟨19403935954375271359248499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25871914605833695145664665 19403935954375271359248499)
            ·
              refine ⟨29105903931562907038872749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19403935954375271359248499 29105903931562907038872749)
              ·
                refine ⟨10914713974336090139577281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29105903931562907038872749 10914713974336090139577281)
                ·
                  refine ⟨8186035480752067604682961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10914713974336090139577281 8186035480752067604682961)
                  ·
                    refine ⟨6139526610564050703512221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8186035480752067604682961 6139526610564050703512221)
                    ·
                      refine ⟨2302322478961519013817083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139526610564050703512221 2302322478961519013817083)
                      ·
                        rfl

theorem cell23_4483757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_4483757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483757 prefixEnd_4483757 := by exact prefixLift 4483757
  have htrace : WordTrace (prefixWord ++ tailWord_4483757) baseStart_4483757 baseEnd_4483757 := by
    simpa [prefixWord, tailWord_4483757, baseEnd_4483757] using wordTrace_append hprefix tailTrace_4483757
  have hstable : (prefixWord ++ tailWord_4483757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483757).length < 2 ^ (prefixWord ++ tailWord_4483757).sum := by decide
  have hdescent : baseEnd_4483757 < baseStart_4483757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483790 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_4483790 : Nat := 118140960795 + 4483790 * 2 ^ 59
def prefixEnd_4483790 : Nat := 4983230072969 + 3 ^ 40 * 4483790 * 2
def baseEnd_4483790 : Nat := 767446474607705794901477

theorem tailTrace_4483790 : CollatzResearch.WordTrace tailWord_4483790 prefixEnd_4483790 767446474607705794901477 := by
  unfold tailWord_4483790
  simp only [CollatzResearch.WordTrace]
  refine ⟨20442157053250259401377103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109024837617334716807344549 20442157053250259401377103)
  ·
    refine ⟨30663235579875389102065655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20442157053250259401377103 30663235579875389102065655)
    ·
      refine ⟨45994853369813083653098483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30663235579875389102065655 45994853369813083653098483)
      ·
        refine ⟨68992280054719625479647725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45994853369813083653098483 68992280054719625479647725)
        ·
          refine ⟨25872105020519859554867897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68992280054719625479647725 25872105020519859554867897)
          ·
            refine ⟨19404078765389894666150923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25872105020519859554867897 19404078765389894666150923)
            ·
              refine ⟨29106118148084841999226385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19404078765389894666150923 29106118148084841999226385)
              ·
                refine ⟨21829588611063631499419789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29106118148084841999226385 21829588611063631499419789)
                ·
                  refine ⟨8186095729148861812282421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21829588611063631499419789 8186095729148861812282421)
                  ·
                    refine ⟨767446474607705794901477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8186095729148861812282421 767446474607705794901477)
                    ·
                      rfl

theorem cell23_4483790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_4483790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483790 prefixEnd_4483790 := by exact prefixLift 4483790
  have htrace : WordTrace (prefixWord ++ tailWord_4483790) baseStart_4483790 baseEnd_4483790 := by
    simpa [prefixWord, tailWord_4483790, baseEnd_4483790] using wordTrace_append hprefix tailTrace_4483790
  have hstable : (prefixWord ++ tailWord_4483790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483790).length < 2 ^ (prefixWord ++ tailWord_4483790).sum := by decide
  have hdescent : baseEnd_4483790 < baseStart_4483790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483804 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4483804 : Nat := 118140960795 + 4483804 * 2 ^ 59
def prefixEnd_4483804 : Nat := 4983230072969 + 3 ^ 40 * 4483804 * 2
def baseEnd_4483804 : Nat := 2302346612552280329929367

theorem tailTrace_4483804 : CollatzResearch.WordTrace tailWord_4483804 prefixEnd_4483804 2302346612552280329929367 := by
  unfold tailWord_4483804
  simp only [CollatzResearch.WordTrace]
  refine ⟨81768883523975677801013233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109025178031967570401350977 81768883523975677801013233)
  ·
    refine ⟨61326662642981758350759925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81768883523975677801013233 61326662642981758350759925)
    ·
      refine ⟨5749374622779539845383743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61326662642981758350759925 5749374622779539845383743)
      ·
        refine ⟨8624061934169309768075615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749374622779539845383743 8624061934169309768075615)
        ·
          refine ⟨12936092901253964652113423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624061934169309768075615 12936092901253964652113423)
          ·
            refine ⟨19404139351880946978170135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12936092901253964652113423 19404139351880946978170135)
            ·
              refine ⟨29106209027821420467255203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19404139351880946978170135 29106209027821420467255203)
              ·
                refine ⟨43659313541732130700882805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29106209027821420467255203 43659313541732130700882805)
                ·
                  refine ⟨4093060644537387253207763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43659313541732130700882805 4093060644537387253207763)
                  ·
                    refine ⟨6139590966806080879811645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4093060644537387253207763 6139590966806080879811645)
                    ·
                      refine ⟨2302346612552280329929367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139590966806080879811645 2302346612552280329929367)
                      ·
                        rfl

theorem cell23_4483804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4483804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483804 prefixEnd_4483804 := by exact prefixLift 4483804
  have htrace : WordTrace (prefixWord ++ tailWord_4483804) baseStart_4483804 baseEnd_4483804 := by
    simpa [prefixWord, tailWord_4483804, baseEnd_4483804] using wordTrace_append hprefix tailTrace_4483804
  have hstable : (prefixWord ++ tailWord_4483804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483804).length < 2 ^ (prefixWord ++ tailWord_4483804).sum := by decide
  have hdescent : baseEnd_4483804 < baseStart_4483804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483820 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_4483820 : Nat := 118140960795 + 4483820 * 2 ^ 59
def prefixEnd_4483820 : Nat := 4983230072969 + 3 ^ 40 * 4483820 * 2
def baseEnd_4483820 : Nat := 767451609414250755776431

theorem tailTrace_4483820 : CollatzResearch.WordTrace tailWord_4483820 prefixEnd_4483820 767451609414250755776431 := by
  unfold tailWord_4483820
  simp only [CollatzResearch.WordTrace]
  refine ⟨81769175307946695167304457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109025567077262260223072609 81769175307946695167304457)
  ·
    refine ⟨61326881480960021375478343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81769175307946695167304457 61326881480960021375478343)
    ·
      refine ⟨91990322221440032063217515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61326881480960021375478343 91990322221440032063217515)
      ·
        refine ⟨137985483332160048094826273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91990322221440032063217515 137985483332160048094826273)
        ·
          refine ⟨103489112499120036071119705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137985483332160048094826273 103489112499120036071119705)
          ·
            refine ⟨77616834374340027053339779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103489112499120036071119705 77616834374340027053339779)
            ·
              refine ⟨116425251561510040580009669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77616834374340027053339779 116425251561510040580009669)
              ·
                refine ⟨21829734667783132608751813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116425251561510040580009669 21829734667783132608751813)
                ·
                  refine ⟨4093075250209337364140965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21829734667783132608751813 4093075250209337364140965)
                  ·
                    refine ⟨767451609414250755776431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093075250209337364140965 767451609414250755776431)
                    ·
                      rfl

theorem cell23_4483820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_4483820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483820 prefixEnd_4483820 := by exact prefixLift 4483820
  have htrace : WordTrace (prefixWord ++ tailWord_4483820) baseStart_4483820 baseEnd_4483820 := by
    simpa [prefixWord, tailWord_4483820, baseEnd_4483820] using wordTrace_append hprefix tailTrace_4483820
  have hstable : (prefixWord ++ tailWord_4483820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483820).length < 2 ^ (prefixWord ++ tailWord_4483820).sum := by decide
  have hdescent : baseEnd_4483820 < baseStart_4483820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483821 : List Nat := [1, 5, 1, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4483821 : Nat := 118140960795 + 4483821 * 2 ^ 59
def prefixEnd_4483821 : Nat := 4983230072969 + 3 ^ 40 * 4483821 * 2
def baseEnd_4483821 : Nat := 2302355341723406763416789

theorem tailTrace_4483821 : CollatzResearch.WordTrace tailWord_4483821 prefixEnd_4483821 2302355341723406763416789 := by
  unfold tailWord_4483821
  simp only [CollatzResearch.WordTrace]
  refine ⟨163538387088889767505395317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109025591392593178336930211 163538387088889767505395317)
  ·
    refine ⟨15331723789583415703630811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163538387088889767505395317 15331723789583415703630811)
    ·
      refine ⟨22997585684375123555446217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15331723789583415703630811 22997585684375123555446217)
      ·
        refine ⟨17248189263281342666584663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22997585684375123555446217 17248189263281342666584663)
        ·
          refine ⟨25872283894922013999876995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17248189263281342666584663 25872283894922013999876995)
          ·
            refine ⟨38808425842383020999815493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25872283894922013999876995 38808425842383020999815493)
            ·
              refine ⟨7276579845446816437465405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38808425842383020999815493 7276579845446816437465405)
              ·
                refine ⟨2728717442042556164049527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7276579845446816437465405 2728717442042556164049527)
                ·
                  refine ⟨4093076163063834246074291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728717442042556164049527 4093076163063834246074291)
                  ·
                    refine ⟨6139614244595751369111437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4093076163063834246074291 6139614244595751369111437)
                    ·
                      refine ⟨2302355341723406763416789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139614244595751369111437 2302355341723406763416789)
                      ·
                        rfl

theorem cell23_4483821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4483821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483821 prefixEnd_4483821 := by exact prefixLift 4483821
  have htrace : WordTrace (prefixWord ++ tailWord_4483821) baseStart_4483821 baseEnd_4483821 := by
    simpa [prefixWord, tailWord_4483821, baseEnd_4483821] using wordTrace_append hprefix tailTrace_4483821
  have hstable : (prefixWord ++ tailWord_4483821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483821).length < 2 ^ (prefixWord ++ tailWord_4483821).sum := by decide
  have hdescent : baseEnd_4483821 < baseStart_4483821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483827 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 7, 2, 2]
def baseStart_4483827 : Nat := 118140960795 + 4483827 * 2 ^ 59
def prefixEnd_4483827 : Nat := 4983230072969 + 3 ^ 40 * 4483827 * 2
def baseEnd_4483827 : Nat := 2302358422607333739941761

theorem tailTrace_4483827 : CollatzResearch.WordTrace tailWord_4483827 prefixEnd_4483827 2302358422607333739941761 := by
  unfold tailWord_4483827
  simp only [CollatzResearch.WordTrace]
  refine ⟨163538605926868030530113735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109025737284578687020075823 163538605926868030530113735)
  ·
    refine ⟨245307908890302045795170603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163538605926868030530113735 245307908890302045795170603)
    ·
      refine ⟨367961863335453068692755905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245307908890302045795170603 367961863335453068692755905)
      ·
        refine ⟨275971397501589801519566929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367961863335453068692755905 275971397501589801519566929)
        ·
          refine ⟨206978548126192351139675197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275971397501589801519566929 206978548126192351139675197)
          ·
            refine ⟨77616955547322131677378199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206978548126192351139675197 77616955547322131677378199)
            ·
              refine ⟨116425433320983197516067299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77616955547322131677378199 116425433320983197516067299)
              ·
                refine ⟨174638149981474796274100949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116425433320983197516067299 174638149981474796274100949)
                ·
                  refine ⟨4093081640190815537674241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 174638149981474796274100949 4093081640190815537674241)
                  ·
                    refine ⟨3069811230143111653255681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4093081640190815537674241 3069811230143111653255681)
                    ·
                      refine ⟨2302358422607333739941761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069811230143111653255681 2302358422607333739941761)
                      ·
                        rfl

theorem cell23_4483827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 2, 2].length) (baseStart_4483827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483827 prefixEnd_4483827 := by exact prefixLift 4483827
  have htrace : WordTrace (prefixWord ++ tailWord_4483827) baseStart_4483827 baseEnd_4483827 := by
    simpa [prefixWord, tailWord_4483827, baseEnd_4483827] using wordTrace_append hprefix tailTrace_4483827
  have hstable : (prefixWord ++ tailWord_4483827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483827).length < 2 ^ (prefixWord ++ tailWord_4483827).sum := by decide
  have hdescent : baseEnd_4483827 < baseStart_4483827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483828 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 6]
def baseStart_4483828 : Nat := 118140960795 + 4483828 * 2 ^ 59
def prefixEnd_4483828 : Nat := 4983230072969 + 3 ^ 40 * 4483828 * 2
def baseEnd_4483828 : Nat := 255817659565332026225473

theorem tailTrace_4483828 : CollatzResearch.WordTrace tailWord_4483828 prefixEnd_4483828 255817659565332026225473 := by
  unfold tailWord_4483828
  simp only [CollatzResearch.WordTrace]
  refine ⟨81769321199932203850450069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109025761599909605133933425 81769321199932203850450069)
  ·
    refine ⟨3832936931246822055489847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81769321199932203850450069 3832936931246822055489847)
    ·
      refine ⟨5749405396870233083234771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3832936931246822055489847 5749405396870233083234771)
      ·
        refine ⟨8624108095305349624852157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749405396870233083234771 8624108095305349624852157)
        ·
          refine ⟨3234040535739506109319559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8624108095305349624852157 3234040535739506109319559)
          ·
            refine ⟨4851060803609259163979339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234040535739506109319559 4851060803609259163979339)
            ·
              refine ⟨7276591205413888745969009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851060803609259163979339 7276591205413888745969009)
              ·
                refine ⟨5457443404060416559476757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7276591205413888745969009 5457443404060416559476757)
                ·
                  refine ⟨255817659565332026225473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5457443404060416559476757 255817659565332026225473)
                  ·
                    rfl

theorem cell23_4483828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_4483828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483828 prefixEnd_4483828 := by exact prefixLift 4483828
  have htrace : WordTrace (prefixWord ++ tailWord_4483828) baseStart_4483828 baseEnd_4483828 := by
    simpa [prefixWord, tailWord_4483828, baseEnd_4483828] using wordTrace_append hprefix tailTrace_4483828
  have hstable : (prefixWord ++ tailWord_4483828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483828).length < 2 ^ (prefixWord ++ tailWord_4483828).sum := by decide
  have hdescent : baseEnd_4483828 < baseStart_4483828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483843 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7]
def baseStart_4483843 : Nat := 118140960795 + 4483843 * 2 ^ 59
def prefixEnd_4483843 : Nat := 4983230072969 + 3 ^ 40 * 4483843 * 2
def baseEnd_4483843 : Nat := 2302366638297805677341687

theorem tailTrace_4483843 : CollatzResearch.WordTrace tailWord_4483843 prefixEnd_4483843 2302366638297805677341687 := by
  unfold tailWord_4483843
  simp only [CollatzResearch.WordTrace]
  refine ⟨163539189494810065262696183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109026126329873376841797455 163539189494810065262696183)
  ·
    refine ⟨245308784242215097894044275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163539189494810065262696183 245308784242215097894044275)
    ·
      refine ⟨367963176363322646841066413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245308784242215097894044275 367963176363322646841066413)
      ·
        refine ⟨137986191136245992565399905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367963176363322646841066413 137986191136245992565399905)
        ·
          refine ⟨103489643352184494424049929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137986191136245992565399905 103489643352184494424049929)
          ·
            refine ⟨77617232514138370818037447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103489643352184494424049929 77617232514138370818037447)
            ·
              refine ⟨116425848771207556227056171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77617232514138370818037447 116425848771207556227056171)
              ·
                refine ⟨174638773156811334340584257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116425848771207556227056171 174638773156811334340584257)
                ·
                  refine ⟨130979079867608500755438193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174638773156811334340584257 130979079867608500755438193)
                  ·
                    refine ⟨98234309900706375566578645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130979079867608500755438193 98234309900706375566578645)
                    ·
                      refine ⟨2302366638297805677341687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98234309900706375566578645 2302366638297805677341687)
                      ·
                        rfl

theorem cell23_4483843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_4483843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483843 prefixEnd_4483843 := by exact prefixLift 4483843
  have htrace : WordTrace (prefixWord ++ tailWord_4483843) baseStart_4483843 baseEnd_4483843 := by
    simpa [prefixWord, tailWord_4483843, baseEnd_4483843] using wordTrace_append hprefix tailTrace_4483843
  have hstable : (prefixWord ++ tailWord_4483843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483843).length < 2 ^ (prefixWord ++ tailWord_4483843).sum := by decide
  have hdescent : baseEnd_4483843 < baseStart_4483843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483847 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4483847 : Nat := 118140960795 + 4483847 * 2 ^ 59
def prefixEnd_4483847 : Nat := 4983230072969 + 3 ^ 40 * 4483847 * 2
def baseEnd_4483847 : Nat := 2302368692220423661691669

theorem tailTrace_4483847 : CollatzResearch.WordTrace tailWord_4483847 prefixEnd_4483847 2302368692220423661691669 := by
  unfold tailWord_4483847
  simp only [CollatzResearch.WordTrace]
  refine ⟨163539335386795573945841795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109026223591197049297227863 163539335386795573945841795)
  ·
    refine ⟨245309003080193360918762693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163539335386795573945841795 245309003080193360918762693)
    ·
      refine ⟨45995438077536255172268005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245309003080193360918762693 45995438077536255172268005)
      ·
        refine ⟨8624144639538047844800251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45995438077536255172268005 8624144639538047844800251)
        ·
          refine ⟨12936216959307071767200377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624144639538047844800251 12936216959307071767200377)
          ·
            refine ⟨9702162719480303825400283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12936216959307071767200377 9702162719480303825400283)
            ·
              refine ⟨14553244079220455738100425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702162719480303825400283 14553244079220455738100425)
              ·
                refine ⟨10914933059415341803575319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14553244079220455738100425 10914933059415341803575319)
                ·
                  refine ⟨16372399589123012705362979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10914933059415341803575319 16372399589123012705362979)
                  ·
                    refine ⟨24558599383684519058044469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16372399589123012705362979 24558599383684519058044469)
                    ·
                      refine ⟨2302368692220423661691669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24558599383684519058044469 2302368692220423661691669)
                      ·
                        rfl

theorem cell23_4483847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4483847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483847 prefixEnd_4483847 := by exact prefixLift 4483847
  have htrace : WordTrace (prefixWord ++ tailWord_4483847) baseStart_4483847 baseEnd_4483847 := by
    simpa [prefixWord, tailWord_4483847, baseEnd_4483847] using wordTrace_append hprefix tailTrace_4483847
  have hstable : (prefixWord ++ tailWord_4483847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483847).length < 2 ^ (prefixWord ++ tailWord_4483847).sum := by decide
  have hdescent : baseEnd_4483847 < baseStart_4483847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483877 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_4483877 : Nat := 118140960795 + 4483877 * 2 ^ 59
def prefixEnd_4483877 : Nat := 4983230072969 + 3 ^ 40 * 4483877 * 2
def baseEnd_4483877 : Nat := 2302384096640058544316531

theorem tailTrace_4483877 : CollatzResearch.WordTrace tailWord_4483877 prefixEnd_4483877 2302384096640058544316531 := by
  unfold tailWord_4483877
  simp only [CollatzResearch.WordTrace]
  refine ⟨163540429576686889069433885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109026953051124592712955923 163540429576686889069433885)
  ·
    refine ⟨61327661091257583401037707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163540429576686889069433885 61327661091257583401037707)
    ·
      refine ⟨91991491636886375101556561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61327661091257583401037707 91991491636886375101556561)
      ·
        refine ⟨68993618727664781326167421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91991491636886375101556561 68993618727664781326167421)
        ·
          refine ⟨25872607022874292997312783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68993618727664781326167421 25872607022874292997312783)
          ·
            refine ⟨38808910534311439495969175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25872607022874292997312783 38808910534311439495969175)
            ·
              refine ⟨58213365801467159243953763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38808910534311439495969175 58213365801467159243953763)
              ·
                refine ⟨87320048702200738865930645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58213365801467159243953763 87320048702200738865930645)
                ·
                  refine ⟨4093127282915659634340499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87320048702200738865930645 4093127282915659634340499)
                  ·
                    refine ⟨6139690924373489451510749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4093127282915659634340499 6139690924373489451510749)
                    ·
                      refine ⟨2302384096640058544316531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139690924373489451510749 2302384096640058544316531)
                      ·
                        rfl

theorem cell23_4483877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_4483877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483877 prefixEnd_4483877 := by exact prefixLift 4483877
  have htrace : WordTrace (prefixWord ++ tailWord_4483877) baseStart_4483877 baseEnd_4483877 := by
    simpa [prefixWord, tailWord_4483877, baseEnd_4483877] using wordTrace_append hprefix tailTrace_4483877
  have hstable : (prefixWord ++ tailWord_4483877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483877).length < 2 ^ (prefixWord ++ tailWord_4483877).sum := by decide
  have hdescent : baseEnd_4483877 < baseStart_4483877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483890 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_4483890 : Nat := 118140960795 + 4483890 * 2 ^ 59
def prefixEnd_4483890 : Nat := 4983230072969 + 3 ^ 40 * 4483890 * 2
def baseEnd_4483890 : Nat := 2302390771888566993453971

theorem tailTrace_4483890 : CollatzResearch.WordTrace tailWord_4483890 prefixEnd_4483890 2302390771888566993453971 := by
  unfold tailWord_4483890
  simp only [CollatzResearch.WordTrace]
  refine ⟨40885225931409948072414281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109027269150426528193104749 40885225931409948072414281)
  ·
    refine ⟨30663919448557461054310711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40885225931409948072414281 30663919448557461054310711)
    ·
      refine ⟨45995879172836191581466067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30663919448557461054310711 45995879172836191581466067)
      ·
        refine ⟨68993818759254287372199101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45995879172836191581466067 68993818759254287372199101)
        ·
          refine ⟨25872682034720357764574663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68993818759254287372199101 25872682034720357764574663)
          ·
            refine ⟨38809023052080536646861995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25872682034720357764574663 38809023052080536646861995)
            ·
              refine ⟨58213534578120804970292993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38809023052080536646861995 58213534578120804970292993)
              ·
                refine ⟨43660150933590603727719745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58213534578120804970292993 43660150933590603727719745)
                ·
                  refine ⟨32745113200192952795789809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43660150933590603727719745 32745113200192952795789809)
                  ·
                    refine ⟨24558834900144714596842357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32745113200192952795789809 24558834900144714596842357)
                    ·
                      refine ⟨2302390771888566993453971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24558834900144714596842357 2302390771888566993453971)
                      ·
                        rfl

theorem cell23_4483890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_4483890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483890 prefixEnd_4483890 := by exact prefixLift 4483890
  have htrace : WordTrace (prefixWord ++ tailWord_4483890) baseStart_4483890 baseEnd_4483890 := by
    simpa [prefixWord, tailWord_4483890, baseEnd_4483890] using wordTrace_append hprefix tailTrace_4483890
  have hstable : (prefixWord ++ tailWord_4483890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483890).length < 2 ^ (prefixWord ++ tailWord_4483890).sum := by decide
  have hdescent : baseEnd_4483890 < baseStart_4483890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483900 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_4483900 : Nat := 118140960795 + 4483900 * 2 ^ 59
def prefixEnd_4483900 : Nat := 4983230072969 + 3 ^ 40 * 4483900 * 2
def baseEnd_4483900 : Nat := 2302395906695111954328925

theorem tailTrace_4483900 : CollatzResearch.WordTrace tailWord_4483900 prefixEnd_4483900 2302395906695111954328925 := by
  unfold tailWord_4483900
  simp only [CollatzResearch.WordTrace]
  refine ⟨81770634227801781998760577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109027512303735709331680769 81770634227801781998760577)
  ·
    refine ⟨61327975670851336499070433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81770634227801781998760577 61327975670851336499070433)
    ·
      refine ⟨45995981753138502374302825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61327975670851336499070433 45995981753138502374302825)
      ·
        refine ⟨34496986314853876780727119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45995981753138502374302825 34496986314853876780727119)
        ·
          refine ⟨51745479472280815171090679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34496986314853876780727119 51745479472280815171090679)
          ·
            refine ⟨77618219208421222756636019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51745479472280815171090679 77618219208421222756636019)
            ·
              refine ⟨116427328812631834134954029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77618219208421222756636019 116427328812631834134954029)
              ·
                refine ⟨43660248304736937800607761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116427328812631834134954029 43660248304736937800607761)
                ·
                  refine ⟨32745186228552703350455821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43660248304736937800607761 32745186228552703350455821)
                  ·
                    refine ⟨12279444835707263756420933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32745186228552703350455821 12279444835707263756420933)
                    ·
                      refine ⟨2302395906695111954328925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12279444835707263756420933 2302395906695111954328925)
                      ·
                        rfl

theorem cell23_4483900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_4483900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483900 prefixEnd_4483900 := by exact prefixLift 4483900
  have htrace : WordTrace (prefixWord ++ tailWord_4483900) baseStart_4483900 baseEnd_4483900 := by
    simpa [prefixWord, tailWord_4483900, baseEnd_4483900] using wordTrace_append hprefix tailTrace_4483900
  have hstable : (prefixWord ++ tailWord_4483900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483900).length < 2 ^ (prefixWord ++ tailWord_4483900).sum := by decide
  have hdescent : baseEnd_4483900 < baseStart_4483900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483905 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 2, 4]
def baseStart_4483905 : Nat := 118140960795 + 4483905 * 2 ^ 59
def prefixEnd_4483905 : Nat := 4983230072969 + 3 ^ 40 * 4483905 * 2
def baseEnd_4483905 : Nat := 767466158032794811588801

theorem tailTrace_4483905 : CollatzResearch.WordTrace tailWord_4483905 prefixEnd_4483905 767466158032794811588801 := by
  unfold tailWord_4483905
  simp only [CollatzResearch.WordTrace]
  refine ⟨163541450820585449851453169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109027633880390299900968779 163541450820585449851453169)
  ·
    refine ⟨122656088115439087388589877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163541450820585449851453169 122656088115439087388589877)
    ·
      refine ⟨11499008260822414442680301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122656088115439087388589877 11499008260822414442680301)
      ·
        refine ⟨4312128097808405416005113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11499008260822414442680301 4312128097808405416005113)
        ·
          refine ⟨3234096073356304062003835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4312128097808405416005113 3234096073356304062003835)
          ·
            refine ⟨4851144110034456093005753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234096073356304062003835 4851144110034456093005753)
            ·
              refine ⟨3638358082525842069754315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4851144110034456093005753 3638358082525842069754315)
              ·
                refine ⟨5457537123788763104631473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638358082525842069754315 5457537123788763104631473)
                ·
                  refine ⟨4093152842841572328473605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5457537123788763104631473 4093152842841572328473605)
                  ·
                    refine ⟨767466158032794811588801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093152842841572328473605 767466158032794811588801)
                    ·
                      rfl

theorem cell23_4483905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_4483905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483905 prefixEnd_4483905 := by exact prefixLift 4483905
  have htrace : WordTrace (prefixWord ++ tailWord_4483905) baseStart_4483905 baseEnd_4483905 := by
    simpa [prefixWord, tailWord_4483905, baseEnd_4483905] using wordTrace_append hprefix tailTrace_4483905
  have hstable : (prefixWord ++ tailWord_4483905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483905).length < 2 ^ (prefixWord ++ tailWord_4483905).sum := by decide
  have hdescent : baseEnd_4483905 < baseStart_4483905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483920 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_4483920 : Nat := 118140960795 + 4483920 * 2 ^ 59
def prefixEnd_4483920 : Nat := 4983230072969 + 3 ^ 40 * 4483920 * 2
def baseEnd_4483920 : Nat := 2302406176308201876078833

theorem tailTrace_4483920 : CollatzResearch.WordTrace tailWord_4483920 prefixEnd_4483920 2302406176308201876078833 := by
  unfold tailWord_4483920
  simp only [CollatzResearch.WordTrace]
  refine ⟨81770998957765553706624607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109027998610354071608832809 81770998957765553706624607)
  ·
    refine ⟨122656498436648330559936911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81770998957765553706624607 122656498436648330559936911)
    ·
      refine ⟨183984747654972495839905367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122656498436648330559936911 183984747654972495839905367)
      ·
        refine ⟨275977121482458743759858051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183984747654972495839905367 275977121482458743759858051)
        ·
          refine ⟨413965682223688115639787077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275977121482458743759858051 413965682223688115639787077)
          ·
            refine ⟨77618565416941521682460077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 413965682223688115639787077 77618565416941521682460077)
            ·
              refine ⟨29106962031353070630922529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77618565416941521682460077 29106962031353070630922529)
              ·
                refine ⟨21830221523514802973191897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29106962031353070630922529 21830221523514802973191897)
                ·
                  refine ⟨16372666142636102229893923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21830221523514802973191897 16372666142636102229893923)
                  ·
                    refine ⟨24558999213954153344840885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16372666142636102229893923 24558999213954153344840885)
                    ·
                      refine ⟨2302406176308201876078833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24558999213954153344840885 2302406176308201876078833)
                      ·
                        rfl

theorem cell23_4483920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_4483920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483920 prefixEnd_4483920 := by exact prefixLift 4483920
  have htrace : WordTrace (prefixWord ++ tailWord_4483920) baseStart_4483920 baseEnd_4483920 := by
    simpa [prefixWord, tailWord_4483920, baseEnd_4483920] using wordTrace_append hprefix tailTrace_4483920
  have hstable : (prefixWord ++ tailWord_4483920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483920).length < 2 ^ (prefixWord ++ tailWord_4483920).sum := by decide
  have hdescent : baseEnd_4483920 < baseStart_4483920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4483980 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_4483980 : Nat := 118140960795 + 4483980 * 2 ^ 59
def prefixEnd_4483980 : Nat := 4983230072969 + 3 ^ 40 * 4483980 * 2
def baseEnd_4483980 : Nat := 2302436985147471641328557

theorem tailTrace_4483980 : CollatzResearch.WordTrace tailWord_4483980 prefixEnd_4483980 2302436985147471641328557 := by
  unfold tailWord_4483980
  simp only [CollatzResearch.WordTrace]
  refine ⟨81772093147656868830216697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109029457530209158440288929 81772093147656868830216697)
  ·
    refine ⟨61329069860742651622662523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81772093147656868830216697 61329069860742651622662523)
    ·
      refine ⟨91993604791113977433993785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61329069860742651622662523 91993604791113977433993785)
      ·
        refine ⟨68995203593335483075495339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91993604791113977433993785 68995203593335483075495339)
        ·
          refine ⟨103492805390003224613243009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68995203593335483075495339 103492805390003224613243009)
          ·
            refine ⟨77619604042502418459932257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103492805390003224613243009 77619604042502418459932257)
            ·
              refine ⟨58214703031876813844949193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77619604042502418459932257 58214703031876813844949193)
              ·
                refine ⟨43661027273907610383711895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58214703031876813844949193 43661027273907610383711895)
                ·
                  refine ⟨65491540910861415575567843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43661027273907610383711895 65491540910861415575567843)
                  ·
                    refine ⟨98237311366292123363351765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65491540910861415575567843 98237311366292123363351765)
                    ·
                      refine ⟨2302436985147471641328557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98237311366292123363351765 2302436985147471641328557)
                      ·
                        rfl

theorem cell23_4483980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_4483980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4483980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4483980 prefixEnd_4483980 := by exact prefixLift 4483980
  have htrace : WordTrace (prefixWord ++ tailWord_4483980) baseStart_4483980 baseEnd_4483980 := by
    simpa [prefixWord, tailWord_4483980, baseEnd_4483980] using wordTrace_append hprefix tailTrace_4483980
  have hstable : (prefixWord ++ tailWord_4483980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4483980).length < 2 ^ (prefixWord ++ tailWord_4483980).sum := by decide
  have hdescent : baseEnd_4483980 < baseStart_4483980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4483980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484024 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 2, 4, 2]
def baseStart_4484024 : Nat := 118140960795 + 4484024 * 2 ^ 59
def prefixEnd_4484024 : Nat := 4983230072969 + 3 ^ 40 * 4484024 * 2
def baseEnd_4484024 : Nat := 2302459578296269469178355

theorem tailTrace_4484024 : CollatzResearch.WordTrace tailWord_4484024 prefixEnd_4484024 2302459578296269469178355 := by
  unfold tailWord_4484024
  simp only [CollatzResearch.WordTrace]
  refine ⟨81772895553577166587517563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109030527404769555450023417 81772895553577166587517563)
  ·
    refine ⟨122659343330365749881276345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81772895553577166587517563 122659343330365749881276345)
    ·
      refine ⟨91994507497774312410957259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122659343330365749881276345 91994507497774312410957259)
      ·
        refine ⟨137991761246661468616435889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91994507497774312410957259 137991761246661468616435889)
        ·
          refine ⟨103493820934996101462326917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137991761246661468616435889 103493820934996101462326917)
          ·
            refine ⟨19405091425311769024186297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103493820934996101462326917 19405091425311769024186297)
            ·
              refine ⟨14553818568983826768139723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19405091425311769024186297 14553818568983826768139723)
              ·
                refine ⟨21830727853475740152209585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14553818568983826768139723 21830727853475740152209585)
                ·
                  refine ⟨16373045890106805114157189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21830727853475740152209585 16373045890106805114157189)
                  ·
                    refine ⟨3069946104395025958904473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16373045890106805114157189 3069946104395025958904473)
                    ·
                      refine ⟨2302459578296269469178355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069946104395025958904473 2302459578296269469178355)
                      ·
                        rfl

theorem cell23_4484024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_4484024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484024 prefixEnd_4484024 := by exact prefixLift 4484024
  have htrace : WordTrace (prefixWord ++ tailWord_4484024) baseStart_4484024 baseEnd_4484024 := by
    simpa [prefixWord, tailWord_4484024, baseEnd_4484024] using wordTrace_append hprefix tailTrace_4484024
  have hstable : (prefixWord ++ tailWord_4484024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484024).length < 2 ^ (prefixWord ++ tailWord_4484024).sum := by decide
  have hdescent : baseEnd_4484024 < baseStart_4484024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484044 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4484044 : Nat := 118140960795 + 4484044 * 2 ^ 59
def prefixEnd_4484044 : Nat := 4983230072969 + 3 ^ 40 * 4484044 * 2
def baseEnd_4484044 : Nat := 2302469847909359390928263

theorem tailTrace_4484044 : CollatzResearch.WordTrace tailWord_4484044 prefixEnd_4484044 2302469847909359390928263 := by
  unfold tailWord_4484044
  simp only [CollatzResearch.WordTrace]
  refine ⟨81773260283540938295381593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109031013711387917727175457 81773260283540938295381593)
  ·
    refine ⟨61329945212655703721536195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81773260283540938295381593 61329945212655703721536195)
    ·
      refine ⟨91994917818983555582304293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61329945212655703721536195 91994917818983555582304293)
      ·
        refine ⟨17249047091059416671682055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91994917818983555582304293 17249047091059416671682055)
        ·
          refine ⟨25873570636589125007523083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17249047091059416671682055 25873570636589125007523083)
          ·
            refine ⟨38810355954883687511284625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25873570636589125007523083 38810355954883687511284625)
            ·
              refine ⟨29107766966162765633463469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38810355954883687511284625 29107766966162765633463469)
              ·
                refine ⟨10915412612311037112548801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29107766966162765633463469 10915412612311037112548801)
                ·
                  refine ⟨8186559459233277834411601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10915412612311037112548801 8186559459233277834411601)
                  ·
                    refine ⟨6139919594424958375808701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8186559459233277834411601 6139919594424958375808701)
                    ·
                      refine ⟨2302469847909359390928263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139919594424958375808701 2302469847909359390928263)
                      ·
                        rfl

theorem cell23_4484044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4484044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484044 prefixEnd_4484044 := by exact prefixLift 4484044
  have htrace : WordTrace (prefixWord ++ tailWord_4484044) baseStart_4484044 baseEnd_4484044 := by
    simpa [prefixWord, tailWord_4484044, baseEnd_4484044] using wordTrace_append hprefix tailTrace_4484044
  have hstable : (prefixWord ++ tailWord_4484044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484044).length < 2 ^ (prefixWord ++ tailWord_4484044).sum := by decide
  have hdescent : baseEnd_4484044 < baseStart_4484044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484061 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_4484061 : Nat := 118140960795 + 4484061 * 2 ^ 59
def prefixEnd_4484061 : Nat := 4983230072969 + 3 ^ 40 * 4484061 * 2
def baseEnd_4484061 : Nat := 2302478577080485824415685

theorem tailTrace_4484061 : CollatzResearch.WordTrace tailWord_4484061 prefixEnd_4484061 2302478577080485824415685 := by
  unfold tailWord_4484061
  simp only [CollatzResearch.WordTrace]
  refine ⟨163547140608020288494132037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109031427072013525662754691 163547140608020288494132037)
  ·
    refine ⟨30665088864003804092649757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163547140608020288494132037 30665088864003804092649757)
    ·
      refine ⟨11499408324001426534743659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30665088864003804092649757 11499408324001426534743659)
      ·
        refine ⟨17249112486002139802115489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11499408324001426534743659 17249112486002139802115489)
        ·
          refine ⟨12936834364501604851586617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17249112486002139802115489 12936834364501604851586617)
          ·
            refine ⟨9702625773376203638689963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12936834364501604851586617 9702625773376203638689963)
            ·
              refine ⟨14553938660064305458034945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702625773376203638689963 14553938660064305458034945)
              ·
                refine ⟨10915453995048229093526209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14553938660064305458034945 10915453995048229093526209)
                ·
                  refine ⟨8186590496286171820144657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10915453995048229093526209 8186590496286171820144657)
                  ·
                    refine ⟨6139942872214628865108493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8186590496286171820144657 6139942872214628865108493)
                    ·
                      refine ⟨2302478577080485824415685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6139942872214628865108493 2302478577080485824415685)
                      ·
                        rfl

theorem cell23_4484061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_4484061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484061 prefixEnd_4484061 := by exact prefixLift 4484061
  have htrace : WordTrace (prefixWord ++ tailWord_4484061) baseStart_4484061 baseEnd_4484061 := by
    simpa [prefixWord, tailWord_4484061, baseEnd_4484061] using wordTrace_append hprefix tailTrace_4484061
  have hstable : (prefixWord ++ tailWord_4484061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484061).length < 2 ^ (prefixWord ++ tailWord_4484061).sum := by decide
  have hdescent : baseEnd_4484061 < baseStart_4484061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484081 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 6]
def baseStart_4484081 : Nat := 118140960795 + 4484081 * 2 ^ 59
def prefixEnd_4484081 : Nat := 4983230072969 + 3 ^ 40 * 4484081 * 2
def baseEnd_4484081 : Nat := 255832094077063971796177

theorem tailTrace_4484081 : CollatzResearch.WordTrace tailWord_4484081 prefixEnd_4484081 255832094077063971796177 := by
  unfold tailWord_4484081
  simp only [CollatzResearch.WordTrace]
  refine ⟨163547870067947831909860097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109031913378631887939906731 163547870067947831909860097)
  ·
    refine ⟨122660902550960873932395073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163547870067947831909860097 122660902550960873932395073)
    ·
      refine ⟨91995676913220655449296305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122660902550960873932395073 91995676913220655449296305)
      ·
        refine ⟨68996757684915491586972229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91995676913220655449296305 68996757684915491586972229)
        ·
          refine ⟨12936892065921654672557293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68996757684915491586972229 12936892065921654672557293)
          ·
            refine ⟨4851334524720620502208985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12936892065921654672557293 4851334524720620502208985)
            ·
              refine ⟨3638500893540465376656739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4851334524720620502208985 3638500893540465376656739)
              ·
                refine ⟨5457751340310698064985109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638500893540465376656739 5457751340310698064985109)
                ·
                  refine ⟨255832094077063971796177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5457751340310698064985109 255832094077063971796177)
                  ·
                    rfl

theorem cell23_4484081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 6].length) (baseStart_4484081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484081 prefixEnd_4484081 := by exact prefixLift 4484081
  have htrace : WordTrace (prefixWord ++ tailWord_4484081) baseStart_4484081 baseEnd_4484081 := by
    simpa [prefixWord, tailWord_4484081, baseEnd_4484081] using wordTrace_append hprefix tailTrace_4484081
  have hstable : (prefixWord ++ tailWord_4484081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484081).length < 2 ^ (prefixWord ++ tailWord_4484081).sum := by decide
  have hdescent : baseEnd_4484081 < baseStart_4484081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484101 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 2, 3, 2]
def baseStart_4484101 : Nat := 118140960795 + 4484101 * 2 ^ 59
def prefixEnd_4484101 : Nat := 4983230072969 + 3 ^ 40 * 4484101 * 2
def baseEnd_4484101 : Nat := 2302499116306665667915501

theorem tailTrace_4484101 : CollatzResearch.WordTrace tailWord_4484101 prefixEnd_4484101 2302499116306665667915501 := by
  unfold tailWord_4484101
  simp only [CollatzResearch.WordTrace]
  refine ⟨163548599527875375325588157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109032399685250250217058771 163548599527875375325588157)
  ·
    refine ⟨61330724822953265747095559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163548599527875375325588157 61330724822953265747095559)
    ·
      refine ⟨91996087234429898620643339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61330724822953265747095559 91996087234429898620643339)
      ·
        refine ⟨137994130851644847930965009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91996087234429898620643339 137994130851644847930965009)
        ·
          refine ⟨103495598138733635948223757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137994130851644847930965009 103495598138733635948223757)
          ·
            refine ⟨38810849302025113480583909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103495598138733635948223757 38810849302025113480583909)
            ·
              refine ⟨7277034244129708777609483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38810849302025113480583909 7277034244129708777609483)
              ·
                refine ⟨10915551366194563166414225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277034244129708777609483 10915551366194563166414225)
                ·
                  refine ⟨8186663524645922374810669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10915551366194563166414225 8186663524645922374810669)
                  ·
                    refine ⟨3069998821742220890554001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8186663524645922374810669 3069998821742220890554001)
                    ·
                      refine ⟨2302499116306665667915501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3069998821742220890554001 2302499116306665667915501)
                      ·
                        rfl

theorem cell23_4484101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_4484101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484101 prefixEnd_4484101 := by exact prefixLift 4484101
  have htrace : WordTrace (prefixWord ++ tailWord_4484101) baseStart_4484101 baseEnd_4484101 := by
    simpa [prefixWord, tailWord_4484101, baseEnd_4484101] using wordTrace_append hprefix tailTrace_4484101
  have hstable : (prefixWord ++ tailWord_4484101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484101).length < 2 ^ (prefixWord ++ tailWord_4484101).sum := by decide
  have hdescent : baseEnd_4484101 < baseStart_4484101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484107 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 3, 6]
def baseStart_4484107 : Nat := 118140960795 + 4484107 * 2 ^ 59
def prefixEnd_4484107 : Nat := 4983230072969 + 3 ^ 40 * 4484107 * 2
def baseEnd_4484107 : Nat := 767500732396864214813491

theorem tailTrace_4484107 : CollatzResearch.WordTrace tailWord_4484107 prefixEnd_4484107 767500732396864214813491 := by
  unfold tailWord_4484107
  simp only [CollatzResearch.WordTrace]
  refine ⟨163548818365853638350306575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109032545577235758900204383 163548818365853638350306575)
  ·
    refine ⟨245323227548780457525459863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163548818365853638350306575 245323227548780457525459863)
    ·
      refine ⟨367984841323170686288189795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245323227548780457525459863 367984841323170686288189795)
      ·
        refine ⟨551977261984756029432284693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367984841323170686288189795 551977261984756029432284693)
        ·
          refine ⟨25873934155535438879638345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 551977261984756029432284693 25873934155535438879638345)
          ·
            refine ⟨19405450616651579159728759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25873934155535438879638345 19405450616651579159728759)
            ·
              refine ⟨29108175924977368739593139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19405450616651579159728759 29108175924977368739593139)
              ·
                refine ⟨43662263887466053109389709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29108175924977368739593139 43662263887466053109389709)
                ·
                  refine ⟨16373348957799769916021141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43662263887466053109389709 16373348957799769916021141)
                  ·
                    refine ⟨767500732396864214813491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16373348957799769916021141 767500732396864214813491)
                    ·
                      rfl

theorem cell23_4484107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 6].length) (baseStart_4484107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484107 prefixEnd_4484107 := by exact prefixLift 4484107
  have htrace : WordTrace (prefixWord ++ tailWord_4484107) baseStart_4484107 baseEnd_4484107 := by
    simpa [prefixWord, tailWord_4484107, baseEnd_4484107] using wordTrace_append hprefix tailTrace_4484107
  have hstable : (prefixWord ++ tailWord_4484107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484107).length < 2 ^ (prefixWord ++ tailWord_4484107).sum := by decide
  have hdescent : baseEnd_4484107 < baseStart_4484107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484125 : List Nat := [1, 4, 2, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_4484125 : Nat := 118140960795 + 4484125 * 2 ^ 59
def prefixEnd_4484125 : Nat := 4983230072969 + 3 ^ 40 * 4484125 * 2
def baseEnd_4484125 : Nat := 2302511439842373574015391

theorem tailTrace_4484125 : CollatzResearch.WordTrace tailWord_4484125 prefixEnd_4484125 2302511439842373574015391 := by
  unfold tailWord_4484125
  simp only [CollatzResearch.WordTrace]
  refine ⟨163549474879788427424461829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109032983253192284949641219 163549474879788427424461829)
  ·
    refine ⟨30665526539960330142086593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163549474879788427424461829 30665526539960330142086593)
    ·
      refine ⟨22999144904970247606564945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30665526539960330142086593 22999144904970247606564945)
      ·
        refine ⟨17249358678727685704923709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22999144904970247606564945 17249358678727685704923709)
        ·
          refine ⟨6468509504522882139346391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17249358678727685704923709 6468509504522882139346391)
          ·
            refine ⟨9702764256784323209019587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6468509504522882139346391 9702764256784323209019587)
            ·
              refine ⟨14554146385176484813529381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702764256784323209019587 14554146385176484813529381)
              ·
                refine ⟨2728902447220590902536759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14554146385176484813529381 2728902447220590902536759)
                ·
                  refine ⟨4093353670830886353805139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728902447220590902536759 4093353670830886353805139)
                  ·
                    refine ⟨6140030506246329530707709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4093353670830886353805139 6140030506246329530707709)
                    ·
                      refine ⟨2302511439842373574015391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6140030506246329530707709 2302511439842373574015391)
                      ·
                        rfl

theorem cell23_4484125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_4484125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484125 prefixEnd_4484125 := by exact prefixLift 4484125
  have htrace : WordTrace (prefixWord ++ tailWord_4484125) baseStart_4484125 baseEnd_4484125 := by
    simpa [prefixWord, tailWord_4484125, baseEnd_4484125] using wordTrace_append hprefix tailTrace_4484125
  have hstable : (prefixWord ++ tailWord_4484125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484125).length < 2 ^ (prefixWord ++ tailWord_4484125).sum := by decide
  have hdescent : baseEnd_4484125 < baseStart_4484125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484144 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4]
def baseStart_4484144 : Nat := 118140960795 + 4484144 * 2 ^ 59
def prefixEnd_4484144 : Nat := 4983230072969 + 3 ^ 40 * 4484144 * 2
def baseEnd_4484144 : Nat := 2302521195974808999677803

theorem tailTrace_4484144 : CollatzResearch.WordTrace tailWord_4484144 prefixEnd_4484144 2302521195974808999677803 := by
  unfold tailWord_4484144
  simp only [CollatzResearch.WordTrace]
  refine ⟨81775083933359796834701743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109033445244479729112935657 81775083933359796834701743)
  ·
    refine ⟨122662625900039695252052615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81775083933359796834701743 122662625900039695252052615)
    ·
      refine ⟨183993938850059542878078923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122662625900039695252052615 183993938850059542878078923)
      ·
        refine ⟨275990908275089314317118385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183993938850059542878078923 275990908275089314317118385)
        ·
          refine ⟨206993181206316985737838789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275990908275089314317118385 206993181206316985737838789)
          ·
            refine ⟨38811221476184434825844773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206993181206316985737838789 38811221476184434825844773)
            ·
              refine ⟨7277104026784581529845895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38811221476184434825844773 7277104026784581529845895)
              ·
                refine ⟨10915656040176872294768843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277104026784581529845895 10915656040176872294768843)
                ·
                  refine ⟨16373484060265308442153265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10915656040176872294768843 16373484060265308442153265)
                  ·
                    refine ⟨12280113045198981331614949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16373484060265308442153265 12280113045198981331614949)
                    ·
                      refine ⟨2302521195974808999677803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12280113045198981331614949 2302521195974808999677803)
                      ·
                        rfl

theorem cell23_4484144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_4484144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484144 prefixEnd_4484144 := by exact prefixLift 4484144
  have htrace : WordTrace (prefixWord ++ tailWord_4484144) baseStart_4484144 baseEnd_4484144 := by
    simpa [prefixWord, tailWord_4484144, baseEnd_4484144] using wordTrace_append hprefix tailTrace_4484144
  have hstable : (prefixWord ++ tailWord_4484144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484144).length < 2 ^ (prefixWord ++ tailWord_4484144).sum := by decide
  have hdescent : baseEnd_4484144 < baseStart_4484144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484181 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_4484181 : Nat := 118140960795 + 4484181 * 2 ^ 59
def prefixEnd_4484181 : Nat := 4983230072969 + 3 ^ 40 * 4484181 * 2
def baseEnd_4484181 : Nat := 2302540194759025354915133

theorem tailTrace_4484181 : CollatzResearch.WordTrace tailWord_4484181 prefixEnd_4484181 2302540194759025354915133 := by
  unfold tailWord_4484181
  simp only [CollatzResearch.WordTrace]
  refine ⟨163551517367585548988500397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109034344911723699325666931 163551517367585548988500397)
  ·
    refine ⟨61331819012844580870687649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163551517367585548988500397 61331819012844580870687649)
    ·
      refine ⟨45998864259633435653015737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61331819012844580870687649 45998864259633435653015737)
      ·
        refine ⟨34499148194725076739761803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45998864259633435653015737 34499148194725076739761803)
        ·
          refine ⟨51748722292087615109642705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34499148194725076739761803 51748722292087615109642705)
          ·
            refine ⟨38811541719065711332232029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51748722292087615109642705 38811541719065711332232029)
            ·
              refine ⟨14554328144649641749587011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38811541719065711332232029 14554328144649641749587011)
              ·
                refine ⟨21831492216974462624380517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14554328144649641749587011 21831492216974462624380517)
                ·
                  refine ⟨4093404790682711742071347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21831492216974462624380517 4093404790682711742071347)
                  ·
                    refine ⟨6140107186024067613107021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4093404790682711742071347 6140107186024067613107021)
                    ·
                      refine ⟨2302540194759025354915133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6140107186024067613107021 2302540194759025354915133)
                      ·
                        rfl

theorem cell23_4484181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_4484181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484181 prefixEnd_4484181 := by exact prefixLift 4484181
  have htrace : WordTrace (prefixWord ++ tailWord_4484181) baseStart_4484181 baseEnd_4484181 := by
    simpa [prefixWord, tailWord_4484181, baseEnd_4484181] using wordTrace_append hprefix tailTrace_4484181
  have hstable : (prefixWord ++ tailWord_4484181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484181).length < 2 ^ (prefixWord ++ tailWord_4484181).sum := by decide
  have hdescent : baseEnd_4484181 < baseStart_4484181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484208 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 1, 3, 2]
def baseStart_4484208 : Nat := 118140960795 + 4484208 * 2 ^ 59
def prefixEnd_4484208 : Nat := 4983230072969 + 3 ^ 40 * 4484208 * 2
def baseEnd_4484208 : Nat := 2302554058736696749277509

theorem tailTrace_4484208 : CollatzResearch.WordTrace tailWord_4484208 prefixEnd_4484208 2302554058736696749277509 := by
  unfold tailWord_4484208
  simp only [CollatzResearch.WordTrace]
  refine ⟨81776251069243866299866639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109035001425658488399822185 81776251069243866299866639)
  ·
    refine ⟨122664376603865799449799959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81776251069243866299866639 122664376603865799449799959)
    ·
      refine ⟨183996564905798699174699939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122664376603865799449799959 183996564905798699174699939)
      ·
        refine ⟨275994847358698048762049909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183996564905798699174699939 275994847358698048762049909)
        ·
          refine ⟨25874516939877942071442179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 275994847358698048762049909 25874516939877942071442179)
          ·
            refine ⟨38811775409816913107163269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25874516939877942071442179 38811775409816913107163269)
            ·
              refine ⟨7277207889340671207593113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38811775409816913107163269 7277207889340671207593113)
              ·
                refine ⟨5457905917005503405694835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7277207889340671207593113 5457905917005503405694835)
                ·
                  refine ⟨8186858875508255108542253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5457905917005503405694835 8186858875508255108542253)
                  ·
                    refine ⟨3070072078315595665703345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8186858875508255108542253 3070072078315595665703345)
                    ·
                      refine ⟨2302554058736696749277509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070072078315595665703345 2302554058736696749277509)
                      ·
                        rfl

theorem cell23_4484208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 3, 2].length) (baseStart_4484208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484208 prefixEnd_4484208 := by exact prefixLift 4484208
  have htrace : WordTrace (prefixWord ++ tailWord_4484208) baseStart_4484208 baseEnd_4484208 := by
    simpa [prefixWord, tailWord_4484208, baseEnd_4484208] using wordTrace_append hprefix tailTrace_4484208
  have hstable : (prefixWord ++ tailWord_4484208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484208).length < 2 ^ (prefixWord ++ tailWord_4484208).sum := by decide
  have hdescent : baseEnd_4484208 < baseStart_4484208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484221 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_4484221 : Nat := 118140960795 + 4484221 * 2 ^ 59
def prefixEnd_4484221 : Nat := 4983230072969 + 3 ^ 40 * 4484221 * 2
def baseEnd_4484221 : Nat := 2302560733985205198414949

theorem tailTrace_4484221 : CollatzResearch.WordTrace tailWord_4484221 prefixEnd_4484221 2302560733985205198414949 := by
  unfold tailWord_4484221
  simp only [CollatzResearch.WordTrace]
  refine ⟨163552976287440635819956517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109035317524960423879971011 163552976287440635819956517)
  ·
    refine ⟨30666183053895119216241847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163552976287440635819956517 30666183053895119216241847)
    ·
      refine ⟨45999274580842678824362771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30666183053895119216241847 45999274580842678824362771)
      ·
        refine ⟨68998911871264018236544157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45999274580842678824362771 68998911871264018236544157)
        ·
          refine ⟨25874591951724006838704059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68998911871264018236544157 25874591951724006838704059)
          ·
            refine ⟨38811887927586010258056089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25874591951724006838704059 38811887927586010258056089)
            ·
              refine ⟨29108915945689507693542067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38811887927586010258056089 29108915945689507693542067)
              ·
                refine ⟨43663373918534261540313101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29108915945689507693542067 43663373918534261540313101)
                ·
                  refine ⟨16373765219450348077617413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43663373918534261540313101 16373765219450348077617413)
                  ·
                    refine ⟨3070080978646940264553265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16373765219450348077617413 3070080978646940264553265)
                    ·
                      refine ⟨2302560733985205198414949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070080978646940264553265 2302560733985205198414949)
                      ·
                        rfl

theorem cell23_4484221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_4484221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484221 prefixEnd_4484221 := by exact prefixLift 4484221
  have htrace : WordTrace (prefixWord ++ tailWord_4484221) baseStart_4484221 baseEnd_4484221 := by
    simpa [prefixWord, tailWord_4484221, baseEnd_4484221] using wordTrace_append hprefix tailTrace_4484221
  have hstable : (prefixWord ++ tailWord_4484221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484221).length < 2 ^ (prefixWord ++ tailWord_4484221).sum := by decide
  have hdescent : baseEnd_4484221 < baseStart_4484221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484311 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 1, 6, 2]
def baseStart_4484311 : Nat := 118140960795 + 4484311 * 2 ^ 59
def prefixEnd_4484311 : Nat := 4983230072969 + 3 ^ 40 * 4484311 * 2
def baseEnd_4484311 : Nat := 2302606947244109846289535

theorem tailTrace_4484311 : CollatzResearch.WordTrace tailWord_4484311 prefixEnd_4484311 2302606947244109846289535 := by
  unfold tailWord_4484311
  simp only [CollatzResearch.WordTrace]
  refine ⟨163556258857114581190732787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109037505904743054127155191 163556258857114581190732787)
  ·
    refine ⟨245334388285671871786099181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163556258857114581190732787 245334388285671871786099181)
    ·
      refine ⟨92000395607126951919787193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245334388285671871786099181 92000395607126951919787193)
      ·
        refine ⟨69000296705345213939840395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92000395607126951919787193 69000296705345213939840395)
        ·
          refine ⟨103500445058017820909760593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69000296705345213939840395 103500445058017820909760593)
          ·
            refine ⟨77625333793513365682320445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103500445058017820909760593 77625333793513365682320445)
            ·
              refine ⟨29109500172567512130870167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77625333793513365682320445 29109500172567512130870167)
              ·
                refine ⟨43664250258851268196305251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29109500172567512130870167 43664250258851268196305251)
                ·
                  refine ⟨65496375388276902294457877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43664250258851268196305251 65496375388276902294457877)
                  ·
                    refine ⟨3070142596325479795052713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65496375388276902294457877 3070142596325479795052713)
                    ·
                      refine ⟨2302606947244109846289535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070142596325479795052713 2302606947244109846289535)
                      ·
                        rfl

theorem cell23_4484311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_4484311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484311 prefixEnd_4484311 := by exact prefixLift 4484311
  have htrace : WordTrace (prefixWord ++ tailWord_4484311) baseStart_4484311 baseEnd_4484311 := by
    simpa [prefixWord, tailWord_4484311, baseEnd_4484311] using wordTrace_append hprefix tailTrace_4484311
  have hstable : (prefixWord ++ tailWord_4484311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484311).length < 2 ^ (prefixWord ++ tailWord_4484311).sum := by decide
  have hdescent : baseEnd_4484311 < baseStart_4484311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484321 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 5, 4]
def baseStart_4484321 : Nat := 118140960795 + 4484321 * 2 ^ 59
def prefixEnd_4484321 : Nat := 4983230072969 + 3 ^ 40 * 4484321 * 2
def baseEnd_4484321 : Nat := 767537360683551602388163

theorem tailTrace_4484321 : CollatzResearch.WordTrace tailWord_4484321 prefixEnd_4484321 767537360683551602388163 := by
  unfold tailWord_4484321
  simp only [CollatzResearch.WordTrace]
  refine ⟨163556623587078352898596817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109037749058052235265731211 163556623587078352898596817)
  ·
    refine ⟨122667467690308764673947613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163556623587078352898596817 122667467690308764673947613)
    ·
      refine ⟨46000300383865786752730355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122667467690308764673947613 46000300383865786752730355)
      ·
        refine ⟨69000450575798680129095533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46000300383865786752730355 69000450575798680129095533)
        ·
          refine ⟨25875168965924505048410825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69000450575798680129095533 25875168965924505048410825)
          ·
            refine ⟨19406376724443378786308119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25875168965924505048410825 19406376724443378786308119)
            ·
              refine ⟨29109565086665068179462179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19406376724443378786308119 29109565086665068179462179)
              ·
                refine ⟨43664347629997602269193269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29109565086665068179462179 43664347629997602269193269)
                ·
                  refine ⟨4093532590312275212736869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43664347629997602269193269 4093532590312275212736869)
                  ·
                    refine ⟨767537360683551602388163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093532590312275212736869 767537360683551602388163)
                    ·
                      rfl

theorem cell23_4484321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_4484321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484321 prefixEnd_4484321 := by exact prefixLift 4484321
  have htrace : WordTrace (prefixWord ++ tailWord_4484321) baseStart_4484321 baseEnd_4484321 := by
    simpa [prefixWord, tailWord_4484321, baseEnd_4484321] using wordTrace_append hprefix tailTrace_4484321
  have hstable : (prefixWord ++ tailWord_4484321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484321).length < 2 ^ (prefixWord ++ tailWord_4484321).sum := by decide
  have hdescent : baseEnd_4484321 < baseStart_4484321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484325 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_4484325 : Nat := 118140960795 + 4484325 * 2 ^ 59
def prefixEnd_4484325 : Nat := 4983230072969 + 3 ^ 40 * 4484325 * 2
def baseEnd_4484325 : Nat := 767538045324424263838157

theorem tailTrace_4484325 : CollatzResearch.WordTrace tailWord_4484325 prefixEnd_4484325 767538045324424263838157 := by
  unfold tailWord_4484325
  simp only [CollatzResearch.WordTrace]
  refine ⟨163556769479063861581742429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109037846319375907721161619 163556769479063861581742429)
  ·
    refine ⟨61333788554648948093153411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163556769479063861581742429 61333788554648948093153411)
    ·
      refine ⟨92000682831973422139730117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61333788554648948093153411 92000682831973422139730117)
      ·
        refine ⟨17250128030995016651199397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92000682831973422139730117 17250128030995016651199397)
        ·
          refine ⟨3234399005811565622099887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17250128030995016651199397 3234399005811565622099887)
          ·
            refine ⟨4851598508717348433149831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234399005811565622099887 4851598508717348433149831)
            ·
              refine ⟨7277397763076022649724747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851598508717348433149831 7277397763076022649724747)
              ·
                refine ⟨10916096644614033974587121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277397763076022649724747 10916096644614033974587121)
                ·
                  refine ⟨8187072483460525480940341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10916096644614033974587121 8187072483460525480940341)
                  ·
                    refine ⟨767538045324424263838157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8187072483460525480940341 767538045324424263838157)
                    ·
                      rfl

theorem cell23_4484325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_4484325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484325 prefixEnd_4484325 := by exact prefixLift 4484325
  have htrace : WordTrace (prefixWord ++ tailWord_4484325) baseStart_4484325 baseEnd_4484325 := by
    simpa [prefixWord, tailWord_4484325, baseEnd_4484325] using wordTrace_append hprefix tailTrace_4484325
  have hstable : (prefixWord ++ tailWord_4484325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484325).length < 2 ^ (prefixWord ++ tailWord_4484325).sum := by decide
  have hdescent : baseEnd_4484325 < baseStart_4484325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484331 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 3]
def baseStart_4484331 : Nat := 118140960795 + 4484331 * 2 ^ 59
def prefixEnd_4484331 : Nat := 4983230072969 + 3 ^ 40 * 4484331 * 2
def baseEnd_4484331 : Nat := 2302617216857199768039443

theorem tailTrace_4484331 : CollatzResearch.WordTrace tailWord_4484331 prefixEnd_4484331 2302617216857199768039443 := by
  unfold tailWord_4484331
  simp only [CollatzResearch.WordTrace]
  refine ⟨163556988317042124606460847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109037992211361416404307231 163556988317042124606460847)
  ·
    refine ⟨245335482475563186909691271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163556988317042124606460847 245335482475563186909691271)
    ·
      refine ⟨368003223713344780364536907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245335482475563186909691271 368003223713344780364536907)
      ·
        refine ⟨552004835570017170546805361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368003223713344780364536907 552004835570017170546805361)
        ·
          refine ⟨414003626677512877910104021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552004835570017170546805361 414003626677512877910104021)
          ·
            refine ⟨9703210000254208076018063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 414003626677512877910104021 9703210000254208076018063)
            ·
              refine ⟨14554815000381312114027095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9703210000254208076018063 14554815000381312114027095)
              ·
                refine ⟨21832222500571968171040643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14554815000381312114027095 21832222500571968171040643)
                ·
                  refine ⟨32748333750857952256560965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21832222500571968171040643 32748333750857952256560965)
                  ·
                    refine ⟨6140312578285866048105181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32748333750857952256560965 6140312578285866048105181)
                    ·
                      refine ⟨2302617216857199768039443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6140312578285866048105181 2302617216857199768039443)
                      ·
                        rfl

theorem cell23_4484331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 3].length) (baseStart_4484331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484331 prefixEnd_4484331 := by exact prefixLift 4484331
  have htrace : WordTrace (prefixWord ++ tailWord_4484331) baseStart_4484331 baseEnd_4484331 := by
    simpa [prefixWord, tailWord_4484331, baseEnd_4484331] using wordTrace_append hprefix tailTrace_4484331
  have hstable : (prefixWord ++ tailWord_4484331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484331).length < 2 ^ (prefixWord ++ tailWord_4484331).sum := by decide
  have hdescent : baseEnd_4484331 < baseStart_4484331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484351 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 6]
def baseStart_4484351 : Nat := 118140960795 + 4484351 * 2 ^ 59
def prefixEnd_4484351 : Nat := 4983230072969 + 3 ^ 40 * 4484351 * 2
def baseEnd_4484351 : Nat := 255847498496698854421039

theorem tailTrace_4484351 : CollatzResearch.WordTrace tailWord_4484351 prefixEnd_4484351 255847498496698854421039 := by
  unfold tailWord_4484351
  simp only [CollatzResearch.WordTrace]
  refine ⟨163557717776969668022188907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109038478517979778681459271 163557717776969668022188907)
  ·
    refine ⟨245336576665454502033283361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163557717776969668022188907 245336576665454502033283361)
    ·
      refine ⟨184002432499090876524962521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245336576665454502033283361 184002432499090876524962521)
      ·
        refine ⟨138001824374318157393721891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184002432499090876524962521 138001824374318157393721891)
        ·
          refine ⟨207002736561477236090582837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138001824374318157393721891 207002736561477236090582837)
          ·
            refine ⟨19406506552638490883492141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207002736561477236090582837 19406506552638490883492141)
            ·
              refine ⟨7277439957239434081309553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19406506552638490883492141 7277439957239434081309553)
              ·
                refine ⟨5458079967929575560982165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7277439957239434081309553 5458079967929575560982165)
                ·
                  refine ⟨255847498496698854421039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5458079967929575560982165 255847498496698854421039)
                  ·
                    rfl

theorem cell23_4484351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 6].length) (baseStart_4484351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484351 prefixEnd_4484351 := by exact prefixLift 4484351
  have htrace : WordTrace (prefixWord ++ tailWord_4484351) baseStart_4484351 baseEnd_4484351 := by
    simpa [prefixWord, tailWord_4484351, baseEnd_4484351] using wordTrace_append hprefix tailTrace_4484351
  have hstable : (prefixWord ++ tailWord_4484351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484351).length < 2 ^ (prefixWord ++ tailWord_4484351).sum := by decide
  have hdescent : baseEnd_4484351 < baseStart_4484351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484388 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_4484388 : Nat := 118140960795 + 4484388 * 2 ^ 59
def prefixEnd_4484388 : Nat := 4983230072969 + 3 ^ 40 * 4484388 * 2
def baseEnd_4484388 : Nat := 2302646485254506045026681

theorem tailTrace_4484388 : CollatzResearch.WordTrace tailWord_4484388 prefixEnd_4484388 2302646485254506045026681 := by
  unfold tailWord_4484388
  simp only [CollatzResearch.WordTrace]
  refine ⟨81779533638917811670642909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109039378185223748894190545 81779533638917811670642909)
  ·
    refine ⟨30667325114594179376491091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81779533638917811670642909 30667325114594179376491091)
    ·
      refine ⟨46000987671891269064736637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30667325114594179376491091 46000987671891269064736637)
      ·
        refine ⟨17250370376959225899276239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46000987671891269064736637 17250370376959225899276239)
        ·
          refine ⟨25875555565438838848914359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17250370376959225899276239 25875555565438838848914359)
          ·
            refine ⟨38813333348158258273371539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25875555565438838848914359 38813333348158258273371539)
            ·
              refine ⟨58220000022237387410057309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38813333348158258273371539 58220000022237387410057309)
              ·
                refine ⟨21832500008339020278771491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58220000022237387410057309 21832500008339020278771491)
                ·
                  refine ⟨32748750012508530418157237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21832500008339020278771491 32748750012508530418157237)
                  ·
                    refine ⟨3070195313672674726702241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32748750012508530418157237 3070195313672674726702241)
                    ·
                      refine ⟨2302646485254506045026681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070195313672674726702241 2302646485254506045026681)
                      ·
                        rfl

theorem cell23_4484388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_4484388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484388 prefixEnd_4484388 := by exact prefixLift 4484388
  have htrace : WordTrace (prefixWord ++ tailWord_4484388) baseStart_4484388 baseEnd_4484388 := by
    simpa [prefixWord, tailWord_4484388, baseEnd_4484388] using wordTrace_append hprefix tailTrace_4484388
  have hstable : (prefixWord ++ tailWord_4484388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484388).length < 2 ^ (prefixWord ++ tailWord_4484388).sum := by decide
  have hdescent : baseEnd_4484388 < baseStart_4484388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484405 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_4484405 : Nat := 118140960795 + 4484405 * 2 ^ 59
def prefixEnd_4484405 : Nat := 4983230072969 + 3 ^ 40 * 4484405 * 2
def baseEnd_4484405 : Nat := 2302655214425632478514103

theorem tailTrace_4484405 : CollatzResearch.WordTrace tailWord_4484405 prefixEnd_4484405 2302655214425632478514103 := by
  unfold tailWord_4484405
  simp only [CollatzResearch.WordTrace]
  refine ⟨163559687318774035244654669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109039791545849356829769779 163559687318774035244654669)
  ·
    refine ⟨61334882744540263216745501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163559687318774035244654669 61334882744540263216745501)
    ·
      refine ⟨23000581029202598706279563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61334882744540263216745501 23000581029202598706279563)
      ·
        refine ⟨34500871543803898059419345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23000581029202598706279563 34500871543803898059419345)
        ·
          refine ⟨25875653657852923544564509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34500871543803898059419345 25875653657852923544564509)
          ·
            refine ⟨9703370121694846329211691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25875653657852923544564509 9703370121694846329211691)
            ·
              refine ⟨14555055182542269493817537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9703370121694846329211691 14555055182542269493817537)
              ·
                refine ⟨10916291386906702120363153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14555055182542269493817537 10916291386906702120363153)
                ·
                  refine ⟨8187218540180026590272365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10916291386906702120363153 8187218540180026590272365)
                  ·
                    refine ⟨3070206952567509971352137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8187218540180026590272365 3070206952567509971352137)
                    ·
                      refine ⟨2302655214425632478514103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070206952567509971352137 2302655214425632478514103)
                      ·
                        rfl

theorem cell23_4484405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_4484405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484405 prefixEnd_4484405 := by exact prefixLift 4484405
  have htrace : WordTrace (prefixWord ++ tailWord_4484405) baseStart_4484405 baseEnd_4484405 := by
    simpa [prefixWord, tailWord_4484405, baseEnd_4484405] using wordTrace_append hprefix tailTrace_4484405
  have hstable : (prefixWord ++ tailWord_4484405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484405).length < 2 ^ (prefixWord ++ tailWord_4484405).sum := by decide
  have hdescent : baseEnd_4484405 < baseStart_4484405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484406 : List Nat := [5, 1, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_4484406 : Nat := 118140960795 + 4484406 * 2 ^ 59
def prefixEnd_4484406 : Nat := 4983230072969 + 3 ^ 40 * 4484406 * 2
def baseEnd_4484406 : Nat := 767551909302095658200533

theorem tailTrace_4484406 : CollatzResearch.WordTrace tailWord_4484406 prefixEnd_4484406 767551909302095658200533 := by
  unfold tailWord_4484406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10222482736985650775965067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109039815861180274943627381 10222482736985650775965067)
  ·
    refine ⟨15333724105478476163947601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10222482736985650775965067 15333724105478476163947601)
    ·
      refine ⟨11500293079108857122960701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15333724105478476163947601 11500293079108857122960701)
      ·
        refine ⟨4312609904665821421110263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11500293079108857122960701 4312609904665821421110263)
        ·
          refine ⟨6468914856998732131665395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4312609904665821421110263 6468914856998732131665395)
          ·
            refine ⟨9703372285498098197498093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6468914856998732131665395 9703372285498098197498093)
            ·
              refine ⟨3638764607061786824061785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9703372285498098197498093 3638764607061786824061785)
              ·
                refine ⟨2729073455296340118046339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3638764607061786824061785 2729073455296340118046339)
                ·
                  refine ⟨4093610182944510177069509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729073455296340118046339 4093610182944510177069509)
                  ·
                    refine ⟨767551909302095658200533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093610182944510177069509 767551909302095658200533)
                    ·
                      rfl

theorem cell23_4484406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_4484406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484406 prefixEnd_4484406 := by exact prefixLift 4484406
  have htrace : WordTrace (prefixWord ++ tailWord_4484406) baseStart_4484406 baseEnd_4484406 := by
    simpa [prefixWord, tailWord_4484406, baseEnd_4484406] using wordTrace_append hprefix tailTrace_4484406
  have hstable : (prefixWord ++ tailWord_4484406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484406).length < 2 ^ (prefixWord ++ tailWord_4484406).sum := by decide
  have hdescent : baseEnd_4484406 < baseStart_4484406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484448 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_4484448 : Nat := 118140960795 + 4484448 * 2 ^ 59
def prefixEnd_4484448 : Nat := 4983230072969 + 3 ^ 40 * 4484448 * 2
def baseEnd_4484448 : Nat := 2302677294093775810276405

theorem tailTrace_4484448 : CollatzResearch.WordTrace tailWord_4484448 prefixEnd_4484448 2302677294093775810276405 := by
  unfold tailWord_4484448
  simp only [CollatzResearch.WordTrace]
  refine ⟨81780627828809126794234999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109040837105078835725646665 81780627828809126794234999)
  ·
    refine ⟨122670941743213690191352499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81780627828809126794234999 122670941743213690191352499)
    ·
      refine ⟨184006412614820535287028749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122670941743213690191352499 184006412614820535287028749)
      ·
        refine ⟨69002404730557700732635781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184006412614820535287028749 69002404730557700732635781)
        ·
          refine ⟨12937950886979568887369209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69002404730557700732635781 12937950886979568887369209)
          ·
            refine ⟨9703463165234676665526907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12937950886979568887369209 9703463165234676665526907)
            ·
              refine ⟨14555194747852014998290361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9703463165234676665526907 14555194747852014998290361)
              ·
                refine ⟨10916396060889011248717771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14555194747852014998290361 10916396060889011248717771)
                ·
                  refine ⟨16374594091333516873076657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10916396060889011248717771 16374594091333516873076657)
                  ·
                    refine ⟨12280945568500137654807493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16374594091333516873076657 12280945568500137654807493)
                    ·
                      refine ⟨2302677294093775810276405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12280945568500137654807493 2302677294093775810276405)
                      ·
                        rfl

theorem cell23_4484448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_4484448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484448 prefixEnd_4484448 := by exact prefixLift 4484448
  have htrace : WordTrace (prefixWord ++ tailWord_4484448) baseStart_4484448 baseEnd_4484448 := by
    simpa [prefixWord, tailWord_4484448, baseEnd_4484448] using wordTrace_append hprefix tailTrace_4484448
  have hstable : (prefixWord ++ tailWord_4484448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484448).length < 2 ^ (prefixWord ++ tailWord_4484448).sum := by decide
  have hdescent : baseEnd_4484448 < baseStart_4484448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484455 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_4484455 : Nat := 118140960795 + 4484455 * 2 ^ 59
def prefixEnd_4484455 : Nat := 4983230072969 + 3 ^ 40 * 4484455 * 2
def baseEnd_4484455 : Nat := 2302680888458357282888873

theorem tailTrace_4484455 : CollatzResearch.WordTrace tailWord_4484455 prefixEnd_4484455 2302680888458357282888873 := by
  unfold tailWord_4484455
  simp only [CollatzResearch.WordTrace]
  refine ⟨163561510968592893783974819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109041007312395262522649879 163561510968592893783974819)
  ·
    refine ⟨245342266452889340675962229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163561510968592893783974819 245342266452889340675962229)
    ·
      refine ⟨23000837479958375688371459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245342266452889340675962229 23000837479958375688371459)
      ·
        refine ⟨34501256219937563532557189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23000837479958375688371459 34501256219937563532557189)
        ·
          refine ⟨6468985541238293162354473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34501256219937563532557189 6468985541238293162354473)
          ·
            refine ⟨4851739155928719871765855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6468985541238293162354473 4851739155928719871765855)
            ·
              refine ⟨7277608733893079807648783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851739155928719871765855 7277608733893079807648783)
              ·
                refine ⟨10916413100839619711473175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277608733893079807648783 10916413100839619711473175)
                ·
                  refine ⟨16374619651259429567209763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10916413100839619711473175 16374619651259429567209763)
                  ·
                    refine ⟨24561929476889144350814645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16374619651259429567209763 24561929476889144350814645)
                    ·
                      refine ⟨2302680888458357282888873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24561929476889144350814645 2302680888458357282888873)
                      ·
                        rfl

theorem cell23_4484455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_4484455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484455 prefixEnd_4484455 := by exact prefixLift 4484455
  have htrace : WordTrace (prefixWord ++ tailWord_4484455) baseStart_4484455 baseEnd_4484455 := by
    simpa [prefixWord, tailWord_4484455, baseEnd_4484455] using wordTrace_append hprefix tailTrace_4484455
  have hstable : (prefixWord ++ tailWord_4484455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484455).length < 2 ^ (prefixWord ++ tailWord_4484455).sum := by decide
  have hdescent : baseEnd_4484455 < baseStart_4484455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484458 : List Nat := [3, 1, 3, 3, 3, 10]
def baseStart_4484458 : Nat := 118140960795 + 4484458 * 2 ^ 59
def prefixEnd_4484458 : Nat := 4983230072969 + 3 ^ 40 * 4484458 * 2
def baseEnd_4484458 : Nat := 9476059378190620457413

theorem tailTrace_4484458 : CollatzResearch.WordTrace tailWord_4484458 prefixEnd_4484458 9476059378190620457413 := by
  unfold tailWord_4484458
  simp only [CollatzResearch.WordTrace]
  refine ⟨40890405096895506324083507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109041080258388016864222685 40890405096895506324083507)
  ·
    refine ⟨61335607645343259486125261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40890405096895506324083507 61335607645343259486125261)
    ·
      refine ⟨23000852867003722307296973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61335607645343259486125261 23000852867003722307296973)
      ·
        refine ⟨8625319825126395865236365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23000852867003722307296973 8625319825126395865236365)
        ·
          refine ⟨3234494934422398449463637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8625319825126395865236365 3234494934422398449463637)
          ·
            refine ⟨9476059378190620457413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3234494934422398449463637 9476059378190620457413)
            ·
              rfl

theorem cell23_4484458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 10].length) (baseStart_4484458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484458 prefixEnd_4484458 := by exact prefixLift 4484458
  have htrace : WordTrace (prefixWord ++ tailWord_4484458) baseStart_4484458 baseEnd_4484458 := by
    simpa [prefixWord, tailWord_4484458, baseEnd_4484458] using wordTrace_append hprefix tailTrace_4484458
  have hstable : (prefixWord ++ tailWord_4484458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484458).length < 2 ^ (prefixWord ++ tailWord_4484458).sum := by decide
  have hdescent : baseEnd_4484458 < baseStart_4484458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484482 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4484482 : Nat := 118140960795 + 4484482 * 2 ^ 59
def prefixEnd_4484482 : Nat := 4983230072969 + 3 ^ 40 * 4484482 * 2
def baseEnd_4484482 : Nat := 2302694752436028677251249

theorem tailTrace_4484482 : CollatzResearch.WordTrace tailWord_4484482 prefixEnd_4484482 2302694752436028677251249 := by
  unfold tailWord_4484482
  simp only [CollatzResearch.WordTrace]
  refine ⟨40890623934873769348801925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109041663826330051596805133 40890623934873769348801925)
  ·
    refine ⟨7666991987788831752900361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40890623934873769348801925 7666991987788831752900361)
    ·
      refine ⟨5750243990841623814675271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7666991987788831752900361 5750243990841623814675271)
      ·
        refine ⟨8625365986262435722012907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5750243990841623814675271 8625365986262435722012907)
        ·
          refine ⟨12938048979393653583019361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8625365986262435722012907 12938048979393653583019361)
          ·
            refine ⟨9703536734545240187264521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12938048979393653583019361 9703536734545240187264521)
            ·
              refine ⟨7277652550908930140448391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9703536734545240187264521 7277652550908930140448391)
              ·
                refine ⟨10916478826363395210672587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277652550908930140448391 10916478826363395210672587)
                ·
                  refine ⟨16374718239545092816008881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10916478826363395210672587 16374718239545092816008881)
                  ·
                    refine ⟨12281038679658819612006661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16374718239545092816008881 12281038679658819612006661)
                    ·
                      refine ⟨2302694752436028677251249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12281038679658819612006661 2302694752436028677251249)
                      ·
                        rfl

theorem cell23_4484482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4484482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484482 prefixEnd_4484482 := by exact prefixLift 4484482
  have htrace : WordTrace (prefixWord ++ tailWord_4484482) baseStart_4484482 baseEnd_4484482 := by
    simpa [prefixWord, tailWord_4484482, baseEnd_4484482] using wordTrace_append hprefix tailTrace_4484482
  have hstable : (prefixWord ++ tailWord_4484482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484482).length < 2 ^ (prefixWord ++ tailWord_4484482).sum := by decide
  have hdescent : baseEnd_4484482 < baseStart_4484482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484485 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_4484485 : Nat := 118140960795 + 4484485 * 2 ^ 59
def prefixEnd_4484485 : Nat := 4983230072969 + 3 ^ 40 * 4484485 * 2
def baseEnd_4484485 : Nat := 2302696292877992165513735

theorem tailTrace_4484485 : CollatzResearch.WordTrace tailWord_4484485 prefixEnd_4484485 2302696292877992165513735 := by
  unfold tailWord_4484485
  simp only [CollatzResearch.WordTrace]
  refine ⟨163562605158484208907566909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109041736772322805938377939 163562605158484208907566909)
  ·
    refine ⟨61335976934431578340337591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163562605158484208907566909 61335976934431578340337591)
    ·
      refine ⟨92003965401647367510506387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61335976934431578340337591 92003965401647367510506387)
      ·
        refine ⟨138005948102471051265759581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92003965401647367510506387 138005948102471051265759581)
        ·
          refine ⟨51752230538426644224659843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138005948102471051265759581 51752230538426644224659843)
          ·
            refine ⟨77628345807639966336989765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51752230538426644224659843 77628345807639966336989765)
            ·
              refine ⟨14555314838932493688185581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77628345807639966336989765 14555314838932493688185581)
              ·
                refine ⟨5458243064599685133069593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14555314838932493688185581 5458243064599685133069593)
                ·
                  refine ⟨4093682298449763849802195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5458243064599685133069593 4093682298449763849802195)
                  ·
                    refine ⟨6140523447674645774703293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4093682298449763849802195 6140523447674645774703293)
                    ·
                      refine ⟨2302696292877992165513735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6140523447674645774703293 2302696292877992165513735)
                      ·
                        rfl

theorem cell23_4484485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_4484485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484485 prefixEnd_4484485 := by exact prefixLift 4484485
  have htrace : WordTrace (prefixWord ++ tailWord_4484485) baseStart_4484485 baseEnd_4484485 := by
    simpa [prefixWord, tailWord_4484485, baseEnd_4484485] using wordTrace_append hprefix tailTrace_4484485
  have hstable : (prefixWord ++ tailWord_4484485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484485).length < 2 ^ (prefixWord ++ tailWord_4484485).sum := by decide
  have hdescent : baseEnd_4484485 < baseStart_4484485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484491 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4]
def baseStart_4484491 : Nat := 118140960795 + 4484491 * 2 ^ 59
def prefixEnd_4484491 : Nat := 4983230072969 + 3 ^ 40 * 4484491 * 2
def baseEnd_4484491 : Nat := 2302699373761919142038707

theorem tailTrace_4484491 : CollatzResearch.WordTrace tailWord_4484491 prefixEnd_4484491 2302699373761919142038707 := by
  unfold tailWord_4484491
  simp only [CollatzResearch.WordTrace]
  refine ⟨163562823996462471932285327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109041882664308314621523551 163562823996462471932285327)
  ·
    refine ⟨245344235994693707898427991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163562823996462471932285327 245344235994693707898427991)
    ·
      refine ⟨368016353992040561847641987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245344235994693707898427991 368016353992040561847641987)
      ·
        refine ⟨552024530988060842771462981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368016353992040561847641987 552024530988060842771462981)
        ·
          refine ⟨103504599560261408019649309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 552024530988060842771462981 103504599560261408019649309)
          ·
            refine ⟨38814224835098028007368491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103504599560261408019649309 38814224835098028007368491)
            ·
              refine ⟨58221337252647042011052737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38814224835098028007368491 58221337252647042011052737)
              ·
                refine ⟨43666002939485281508289553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58221337252647042011052737 43666002939485281508289553)
                ·
                  refine ⟨32749502204613961131217165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43666002939485281508289553 32749502204613961131217165)
                  ·
                    refine ⟨12281063326730235424206437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32749502204613961131217165 12281063326730235424206437)
                    ·
                      refine ⟨2302699373761919142038707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12281063326730235424206437 2302699373761919142038707)
                      ·
                        rfl

theorem cell23_4484491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_4484491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484491 prefixEnd_4484491 := by exact prefixLift 4484491
  have htrace : WordTrace (prefixWord ++ tailWord_4484491) baseStart_4484491 baseEnd_4484491 := by
    simpa [prefixWord, tailWord_4484491, baseEnd_4484491] using wordTrace_append hprefix tailTrace_4484491
  have hstable : (prefixWord ++ tailWord_4484491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484491).length < 2 ^ (prefixWord ++ tailWord_4484491).sum := by decide
  have hdescent : baseEnd_4484491 < baseStart_4484491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484558 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_4484558 : Nat := 118140960795 + 4484558 * 2 ^ 59
def prefixEnd_4484558 : Nat := 4983230072969 + 3 ^ 40 * 4484558 * 2
def baseEnd_4484558 : Nat := 2302733776965770379900899

theorem tailTrace_4484558 : CollatzResearch.WordTrace tailWord_4484558 prefixEnd_4484558 2302733776965770379900899 := by
  unfold tailWord_4484558
  simp only [CollatzResearch.WordTrace]
  refine ⟨20445658460902467796871791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109043511791479828249982885 20445658460902467796871791)
  ·
    refine ⟨30668487691353701695307687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20445658460902467796871791 30668487691353701695307687)
    ·
      refine ⟨46002731537030552542961531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30668487691353701695307687 46002731537030552542961531)
      ·
        refine ⟨69004097305545828814442297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46002731537030552542961531 69004097305545828814442297)
        ·
          refine ⟨51753072979159371610831723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69004097305545828814442297 51753072979159371610831723)
          ·
            refine ⟨77629609468739057416247585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51753072979159371610831723 77629609468739057416247585)
            ·
              refine ⟨58222207101554293062185689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77629609468739057416247585 58222207101554293062185689)
              ·
                refine ⟨43666655326165719796639267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58222207101554293062185689 43666655326165719796639267)
                ·
                  refine ⟨65499982989248579694958901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43666655326165719796639267 65499982989248579694958901)
                  ·
                    refine ⟨6140623405242054346402397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65499982989248579694958901 6140623405242054346402397)
                    ·
                      refine ⟨2302733776965770379900899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6140623405242054346402397 2302733776965770379900899)
                      ·
                        rfl

theorem cell23_4484558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_4484558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484558 prefixEnd_4484558 := by exact prefixLift 4484558
  have htrace : WordTrace (prefixWord ++ tailWord_4484558) baseStart_4484558 baseEnd_4484558 := by
    simpa [prefixWord, tailWord_4484558, baseEnd_4484558] using wordTrace_append hprefix tailTrace_4484558
  have hstable : (prefixWord ++ tailWord_4484558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484558).length < 2 ^ (prefixWord ++ tailWord_4484558).sum := by decide
  have hdescent : baseEnd_4484558 < baseStart_4484558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484571 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5]
def baseStart_4484571 : Nat := 118140960795 + 4484571 * 2 ^ 59
def prefixEnd_4484571 : Nat := 4983230072969 + 3 ^ 40 * 4484571 * 2
def baseEnd_4484571 : Nat := 2302740452214278829038339

theorem tailTrace_4484571 : CollatzResearch.WordTrace tailWord_4484571 prefixEnd_4484571 2302740452214278829038339 := by
  unfold tailWord_4484571
  simp only [CollatzResearch.WordTrace]
  refine ⟨163565741836172645595197567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109043827890781763730131711 163565741836172645595197567)
  ·
    refine ⟨245348612754258968392796351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163565741836172645595197567 245348612754258968392796351)
    ·
      refine ⟨368022919131388452589194527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245348612754258968392796351 368022919131388452589194527)
      ·
        refine ⟨552034378697082678883791791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368022919131388452589194527 552034378697082678883791791)
        ·
          refine ⟨828051568045624018325687687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552034378697082678883791791 828051568045624018325687687)
          ·
            refine ⟨1242077352068436027488531531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828051568045624018325687687 1242077352068436027488531531)
            ·
              refine ⟨1863116028102654041232797297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242077352068436027488531531 1863116028102654041232797297)
              ·
                refine ⟨1397337021076990530924597973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863116028102654041232797297 1397337021076990530924597973)
                ·
                  refine ⟨32750086431491965568545265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1397337021076990530924597973 32750086431491965568545265)
                  ·
                    refine ⟨24562564823618974176408949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32750086431491965568545265 24562564823618974176408949)
                    ·
                      refine ⟨2302740452214278829038339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24562564823618974176408949 2302740452214278829038339)
                      ·
                        rfl

theorem cell23_4484571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_4484571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484571 prefixEnd_4484571 := by exact prefixLift 4484571
  have htrace : WordTrace (prefixWord ++ tailWord_4484571) baseStart_4484571 baseEnd_4484571 := by
    simpa [prefixWord, tailWord_4484571, baseEnd_4484571] using wordTrace_append hprefix tailTrace_4484571
  have hstable : (prefixWord ++ tailWord_4484571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484571).length < 2 ^ (prefixWord ++ tailWord_4484571).sum := by decide
  have hdescent : baseEnd_4484571 < baseStart_4484571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484612 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_4484612 : Nat := 118140960795 + 4484612 * 2 ^ 59
def prefixEnd_4484612 : Nat := 4983230072969 + 3 ^ 40 * 4484612 * 2
def baseEnd_4484612 : Nat := 767587168307037722875217

theorem tailTrace_4484612 : CollatzResearch.WordTrace tailWord_4484612 prefixEnd_4484612 767587168307037722875217 := by
  unfold tailWord_4484612
  simp only [CollatzResearch.WordTrace]
  refine ⟨81783618614512054798720045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109044824819349406398293393 81783618614512054798720045)
  ·
    refine ⟨30668856980442020549520017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81783618614512054798720045 30668856980442020549520017)
    ·
      refine ⟨23001642735331515412140013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30668856980442020549520017 23001642735331515412140013)
      ·
        refine ⟨8625616025749318279552505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23001642735331515412140013 8625616025749318279552505)
        ·
          refine ⟨6469212019311988709664379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8625616025749318279552505 6469212019311988709664379)
          ·
            refine ⟨9703818028967983064496569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469212019311988709664379 9703818028967983064496569)
            ·
              refine ⟨7277863521725987298372427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9703818028967983064496569 7277863521725987298372427)
              ·
                refine ⟨10916795282588980947558641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277863521725987298372427 10916795282588980947558641)
                ·
                  refine ⟨8187596461941735710668981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10916795282588980947558641 8187596461941735710668981)
                  ·
                    refine ⟨767587168307037722875217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8187596461941735710668981 767587168307037722875217)
                    ·
                      rfl

theorem cell23_4484612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_4484612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484612 prefixEnd_4484612 := by exact prefixLift 4484612
  have htrace : WordTrace (prefixWord ++ tailWord_4484612) baseStart_4484612 baseEnd_4484612 := by
    simpa [prefixWord, tailWord_4484612, baseEnd_4484612] using wordTrace_append hprefix tailTrace_4484612
  have hstable : (prefixWord ++ tailWord_4484612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484612).length < 2 ^ (prefixWord ++ tailWord_4484612).sum := by decide
  have hdescent : baseEnd_4484612 < baseStart_4484612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484615 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4484615 : Nat := 118140960795 + 4484615 * 2 ^ 59
def prefixEnd_4484615 : Nat := 4983230072969 + 3 ^ 40 * 4484615 * 2
def baseEnd_4484615 : Nat := 2302763045363076656888137

theorem tailTrace_4484615 : CollatzResearch.WordTrace tailWord_4484615 prefixEnd_4484615 2302763045363076656888137 := by
  unfold tailWord_4484615
  simp only [CollatzResearch.WordTrace]
  refine ⟨163567346648013241109799299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109044897765342160739866199 163567346648013241109799299)
  ·
    refine ⟨245351019972019861664698949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163567346648013241109799299 245351019972019861664698949)
    ·
      refine ⟨46003316244753724062131053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245351019972019861664698949 46003316244753724062131053)
      ·
        refine ⟨17251243591782646523299145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46003316244753724062131053 17251243591782646523299145)
        ·
          refine ⟨12938432693836984892474359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17251243591782646523299145 12938432693836984892474359)
          ·
            refine ⟨19407649040755477338711539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12938432693836984892474359 19407649040755477338711539)
            ·
              refine ⟨29111473561133216008067309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19407649040755477338711539 29111473561133216008067309)
              ·
                refine ⟨10916802585424956003025241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29111473561133216008067309 10916802585424956003025241)
                ·
                  refine ⟨8187601939068717002268931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10916802585424956003025241 8187601939068717002268931)
                  ·
                    refine ⟨12281402908603075503403397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8187601939068717002268931 12281402908603075503403397)
                    ·
                      refine ⟨2302763045363076656888137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12281402908603075503403397 2302763045363076656888137)
                      ·
                        rfl

theorem cell23_4484615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4484615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484615 prefixEnd_4484615 := by exact prefixLift 4484615
  have htrace : WordTrace (prefixWord ++ tailWord_4484615) baseStart_4484615 baseEnd_4484615 := by
    simpa [prefixWord, tailWord_4484615, baseEnd_4484615] using wordTrace_append hprefix tailTrace_4484615
  have hstable : (prefixWord ++ tailWord_4484615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484615).length < 2 ^ (prefixWord ++ tailWord_4484615).sum := by decide
  have hdescent : baseEnd_4484615 < baseStart_4484615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484669 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4484669 : Nat := 118140960795 + 4484669 * 2 ^ 59
def prefixEnd_4484669 : Nat := 4983230072969 + 3 ^ 40 * 4484669 * 2
def baseEnd_4484669 : Nat := 2302790773318419445612889

theorem tailTrace_4484669 : CollatzResearch.WordTrace tailWord_4484669 prefixEnd_4484669 2302790773318419445612889 := by
  unfold tailWord_4484669
  simp only [CollatzResearch.WordTrace]
  refine ⟨163569316189817608332265061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109046210793211738888176707 163569316189817608332265061)
  ·
    refine ⟨30669246785590801562299699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163569316189817608332265061 30669246785590801562299699)
    ·
      refine ⟨46003870178386202343449549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30669246785590801562299699 46003870178386202343449549)
      ·
        refine ⟨17251451316894825878793581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46003870178386202343449549 17251451316894825878793581)
        ·
          refine ⟨6469294243835559704547593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17251451316894825878793581 6469294243835559704547593)
          ·
            refine ⟨4851970682876669778410695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6469294243835559704547593 4851970682876669778410695)
            ·
              refine ⟨7277956024315004667616043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851970682876669778410695 7277956024315004667616043)
              ·
                refine ⟨10916934036472507001424065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277956024315004667616043 10916934036472507001424065)
                ·
                  refine ⟨8187700527354380251068049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10916934036472507001424065 8187700527354380251068049)
                  ·
                    refine ⟨6140775395515785188301037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8187700527354380251068049 6140775395515785188301037)
                    ·
                      refine ⟨2302790773318419445612889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6140775395515785188301037 2302790773318419445612889)
                      ·
                        rfl

theorem cell23_4484669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4484669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484669 prefixEnd_4484669 := by exact prefixLift 4484669
  have htrace : WordTrace (prefixWord ++ tailWord_4484669) baseStart_4484669 baseEnd_4484669 := by
    simpa [prefixWord, tailWord_4484669, baseEnd_4484669] using wordTrace_append hprefix tailTrace_4484669
  have hstable : (prefixWord ++ tailWord_4484669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484669).length < 2 ^ (prefixWord ++ tailWord_4484669).sum := by decide
  have hdescent : baseEnd_4484669 < baseStart_4484669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484692 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_4484692 : Nat := 118140960795 + 4484692 * 2 ^ 59
def prefixEnd_4484692 : Nat := 4983230072969 + 3 ^ 40 * 4484692 * 2
def baseEnd_4484692 : Nat := 2302802583373472855625283

theorem tailTrace_4484692 : CollatzResearch.WordTrace tailWord_4484692 prefixEnd_4484692 2302802583373472855625283 := by
  unfold tailWord_4484692
  simp only [CollatzResearch.WordTrace]
  refine ⟨81785077534367141630176165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109046770045822855506901553 81785077534367141630176165)
  ·
    refine ⟨15334702037693839055658031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81785077534367141630176165 15334702037693839055658031)
    ·
      refine ⟨23002053056540758583487047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15334702037693839055658031 23002053056540758583487047)
      ·
        refine ⟨34503079584811137875230571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23002053056540758583487047 34503079584811137875230571)
        ·
          refine ⟨51754619377216706812845857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34503079584811137875230571 51754619377216706812845857)
          ·
            refine ⟨38815964532912530109634393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51754619377216706812845857 38815964532912530109634393)
            ·
              refine ⟨29111973399684397582225795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38815964532912530109634393 29111973399684397582225795)
              ·
                refine ⟨43667960099526596373338693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29111973399684397582225795 43667960099526596373338693)
                ·
                  refine ⟨8187742518661236820001005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43667960099526596373338693 8187742518661236820001005)
                  ·
                    refine ⟨3070403444497963807500377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8187742518661236820001005 3070403444497963807500377)
                    ·
                      refine ⟨2302802583373472855625283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070403444497963807500377 2302802583373472855625283)
                      ·
                        rfl

theorem cell23_4484692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_4484692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484692 prefixEnd_4484692 := by exact prefixLift 4484692
  have htrace : WordTrace (prefixWord ++ tailWord_4484692) baseStart_4484692 baseEnd_4484692 := by
    simpa [prefixWord, tailWord_4484692, baseEnd_4484692] using wordTrace_append hprefix tailTrace_4484692
  have hstable : (prefixWord ++ tailWord_4484692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484692).length < 2 ^ (prefixWord ++ tailWord_4484692).sum := by decide
  have hdescent : baseEnd_4484692 < baseStart_4484692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484698 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_4484698 : Nat := 118140960795 + 4484698 * 2 ^ 59
def prefixEnd_4484698 : Nat := 4983230072969 + 3 ^ 40 * 4484698 * 2
def baseEnd_4484698 : Nat := 767601888085799944050085

theorem tailTrace_4484698 : CollatzResearch.WordTrace tailWord_4484698 prefixEnd_4484698 767601888085799944050085 := by
  unfold tailWord_4484698
  simp only [CollatzResearch.WordTrace]
  refine ⟨40892593476678136571267687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109046915937808364190047165 40892593476678136571267687)
  ·
    refine ⟨61338890215017204856901531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40892593476678136571267687 61338890215017204856901531)
    ·
      refine ⟨92008335322525807285352297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61338890215017204856901531 92008335322525807285352297)
      ·
        refine ⟨69006251491894355464014223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92008335322525807285352297 69006251491894355464014223)
        ·
          refine ⟨103509377237841533196021335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69006251491894355464014223 103509377237841533196021335)
          ·
            refine ⟨155264065856762299794032003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103509377237841533196021335 155264065856762299794032003)
            ·
              refine ⟨232896098785143449691048005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155264065856762299794032003 232896098785143449691048005)
              ·
                refine ⟨43668018522214396817071501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232896098785143449691048005 43668018522214396817071501)
                ·
                  refine ⟨16375506945830398806401813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43668018522214396817071501 16375506945830398806401813)
                  ·
                    refine ⟨767601888085799944050085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16375506945830398806401813 767601888085799944050085)
                    ·
                      rfl

theorem cell23_4484698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_4484698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484698 prefixEnd_4484698 := by exact prefixLift 4484698
  have htrace : WordTrace (prefixWord ++ tailWord_4484698) baseStart_4484698 baseEnd_4484698 := by
    simpa [prefixWord, tailWord_4484698, baseEnd_4484698] using wordTrace_append hprefix tailTrace_4484698
  have hstable : (prefixWord ++ tailWord_4484698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484698).length < 2 ^ (prefixWord ++ tailWord_4484698).sum := by decide
  have hdescent : baseEnd_4484698 < baseStart_4484698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484722 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_4484722 : Nat := 118140960795 + 4484722 * 2 ^ 59
def prefixEnd_4484722 : Nat := 4983230072969 + 3 ^ 40 * 4484722 * 2
def baseEnd_4484722 : Nat := 2302817987793107738250145

theorem tailTrace_4484722 : CollatzResearch.WordTrace tailWord_4484722 prefixEnd_4484722 2302817987793107738250145 := by
  unfold tailWord_4484722
  simp only [CollatzResearch.WordTrace]
  refine ⟨40892812314656399595986105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109047499505750398922629613 40892812314656399595986105)
  ·
    refine ⟨30669609235992299696989579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40892812314656399595986105 30669609235992299696989579)
    ·
      refine ⟨46004413853988449545484369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30669609235992299696989579 46004413853988449545484369)
      ·
        refine ⟨34503310390491337159113277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46004413853988449545484369 34503310390491337159113277)
        ·
          refine ⟨12938741396434251434667479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34503310390491337159113277 12938741396434251434667479)
          ·
            refine ⟨19408112094651377152001219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12938741396434251434667479 19408112094651377152001219)
            ·
              refine ⟨29112168141977065728001829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19408112094651377152001219 29112168141977065728001829)
              ·
                refine ⟨5458531526620699824000343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29112168141977065728001829 5458531526620699824000343)
                ·
                  refine ⟨8187797289931049736000515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5458531526620699824000343 8187797289931049736000515)
                  ·
                    refine ⟨12281695934896574604000773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8187797289931049736000515 12281695934896574604000773)
                    ·
                      refine ⟨2302817987793107738250145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12281695934896574604000773 2302817987793107738250145)
                      ·
                        rfl

theorem cell23_4484722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_4484722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484722 prefixEnd_4484722 := by exact prefixLift 4484722
  have htrace : WordTrace (prefixWord ++ tailWord_4484722) baseStart_4484722 baseEnd_4484722 := by
    simpa [prefixWord, tailWord_4484722, baseEnd_4484722] using wordTrace_append hprefix tailTrace_4484722
  have hstable : (prefixWord ++ tailWord_4484722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484722).length < 2 ^ (prefixWord ++ tailWord_4484722).sum := by decide
  have hdescent : baseEnd_4484722 < baseStart_4484722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484766 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_4484766 : Nat := 118140960795 + 4484766 * 2 ^ 59
def prefixEnd_4484766 : Nat := 4983230072969 + 3 ^ 40 * 4484766 * 2
def baseEnd_4484766 : Nat := 767613526980635188699981

theorem tailTrace_4484766 : CollatzResearch.WordTrace tailWord_4484766 prefixEnd_4484766 767613526980635188699981 := by
  unfold tailWord_4484766
  simp only [CollatzResearch.WordTrace]
  refine ⟨20446606758808274237318269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109048569380310795932364101 20446606758808274237318269)
  ·
    refine ⟨7667477534553102838994351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20446606758808274237318269 7667477534553102838994351)
    ·
      refine ⟨11501216301829654258491527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7667477534553102838994351 11501216301829654258491527)
      ·
        refine ⟨17251824452744481387737291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11501216301829654258491527 17251824452744481387737291)
        ·
          refine ⟨25877736679116722081605937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17251824452744481387737291 25877736679116722081605937)
          ·
            refine ⟨19408302509337541561204453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25877736679116722081605937 19408302509337541561204453)
            ·
              refine ⟨3639056720500789042725835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19408302509337541561204453 3639056720500789042725835)
              ·
                refine ⟨5458585080751183564088753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639056720500789042725835 5458585080751183564088753)
                ·
                  refine ⟨4093938810563387673066565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5458585080751183564088753 4093938810563387673066565)
                  ·
                    refine ⟨767613526980635188699981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4093938810563387673066565 767613526980635188699981)
                    ·
                      rfl

theorem cell23_4484766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_4484766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484766 prefixEnd_4484766 := by exact prefixLift 4484766
  have htrace : WordTrace (prefixWord ++ tailWord_4484766) baseStart_4484766 baseEnd_4484766 := by
    simpa [prefixWord, tailWord_4484766, baseEnd_4484766] using wordTrace_append hprefix tailTrace_4484766
  have hstable : (prefixWord ++ tailWord_4484766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484766).length < 2 ^ (prefixWord ++ tailWord_4484766).sum := by decide
  have hdescent : baseEnd_4484766 < baseStart_4484766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484789 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_4484789 : Nat := 118140960795 + 4484789 * 2 ^ 59
def prefixEnd_4484789 : Nat := 4983230072969 + 3 ^ 40 * 4484789 * 2
def baseEnd_4484789 : Nat := 2302852390996958976112337

theorem tailTrace_4484789 : CollatzResearch.WordTrace tailWord_4484789 prefixEnd_4484789 2302852390996958976112337 := by
  unfold tailWord_4484789
  simp only [CollatzResearch.WordTrace]
  refine ⟨163573692949382868826633421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109049128632921912551088947 163573692949382868826633421)
  ·
    refine ⟨61340134856018575809987533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163573692949382868826633421 61340134856018575809987533)
    ·
      refine ⟨23002550571006965928745325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61340134856018575809987533 23002550571006965928745325)
      ·
        refine ⟨8625956464127612223279497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23002550571006965928745325 8625956464127612223279497)
        ·
          refine ⟨6469467348095709167459623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8625956464127612223279497 6469467348095709167459623)
          ·
            refine ⟨9704201022143563751189435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469467348095709167459623 9704201022143563751189435)
            ·
              refine ⟨14556301533215345626784153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9704201022143563751189435 14556301533215345626784153)
              ·
                refine ⟨10917226149911509220088115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14556301533215345626784153 10917226149911509220088115)
                ·
                  refine ⟨16375839224867263830132173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10917226149911509220088115 16375839224867263830132173)
                  ·
                    refine ⟨6140939709325223936299565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16375839224867263830132173 6140939709325223936299565)
                    ·
                      refine ⟨2302852390996958976112337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6140939709325223936299565 2302852390996958976112337)
                      ·
                        rfl

theorem cell23_4484789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_4484789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484789 prefixEnd_4484789 := by exact prefixLift 4484789
  have htrace : WordTrace (prefixWord ++ tailWord_4484789) baseStart_4484789 baseEnd_4484789 := by
    simpa [prefixWord, tailWord_4484789, baseEnd_4484789] using wordTrace_append hprefix tailTrace_4484789
  have hstable : (prefixWord ++ tailWord_4484789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484789).length < 2 ^ (prefixWord ++ tailWord_4484789).sum := by decide
  have hdescent : baseEnd_4484789 < baseStart_4484789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484825 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_4484825 : Nat := 118140960795 + 4484825 * 2 ^ 59
def prefixEnd_4484825 : Nat := 4983230072969 + 3 ^ 40 * 4484825 * 2
def baseEnd_4484825 : Nat := 2302870876300520835262171

theorem tailTrace_4484825 : CollatzResearch.WordTrace tailWord_4484825 prefixEnd_4484825 2302870876300520835262171 := by
  unfold tailWord_4484825
  simp only [CollatzResearch.WordTrace]
  refine ⟨163575005977252446974943929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109050003984834964649962619 163575005977252446974943929)
  ·
    refine ⟨122681254482939335231207947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163575005977252446974943929 122681254482939335231207947)
    ·
      refine ⟨184021881724409002846811921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122681254482939335231207947 184021881724409002846811921)
      ·
        refine ⟨138016411293306752135108941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184021881724409002846811921 138016411293306752135108941)
        ·
          refine ⟨51756154234990032050665853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138016411293306752135108941 51756154234990032050665853)
          ·
            refine ⟨19408557838121262018999695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51756154234990032050665853 19408557838121262018999695)
            ·
              refine ⟨29112836757181893028499543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19408557838121262018999695 29112836757181893028499543)
              ·
                refine ⟨43669255135772839542749315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29112836757181893028499543 43669255135772839542749315)
                ·
                  refine ⟨65503882703659259314123973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43669255135772839542749315 65503882703659259314123973)
                  ·
                    refine ⟨12281978006936111121398245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65503882703659259314123973 12281978006936111121398245)
                    ·
                      refine ⟨2302870876300520835262171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12281978006936111121398245 2302870876300520835262171)
                      ·
                        rfl

theorem cell23_4484825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_4484825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484825 prefixEnd_4484825 := by exact prefixLift 4484825
  have htrace : WordTrace (prefixWord ++ tailWord_4484825) baseStart_4484825 baseEnd_4484825 := by
    simpa [prefixWord, tailWord_4484825, baseEnd_4484825] using wordTrace_append hprefix tailTrace_4484825
  have hstable : (prefixWord ++ tailWord_4484825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484825).length < 2 ^ (prefixWord ++ tailWord_4484825).sum := by decide
  have hdescent : baseEnd_4484825 < baseStart_4484825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484875 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5]
def baseStart_4484875 : Nat := 118140960795 + 4484875 * 2 ^ 59
def prefixEnd_4484875 : Nat := 4983230072969 + 3 ^ 40 * 4484875 * 2
def baseEnd_4484875 : Nat := 2302896550333245639636941

theorem tailTrace_4484875 : CollatzResearch.WordTrace tailWord_4484875 prefixEnd_4484875 2302896550333245639636941 := by
  unfold tailWord_4484875
  simp only [CollatzResearch.WordTrace]
  refine ⟨163576829627071305514264079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109051219751380870342842719 163576829627071305514264079)
  ·
    refine ⟨245365244440606958271396119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163576829627071305514264079 245365244440606958271396119)
    ·
      refine ⟨368047866660910437407094179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245365244440606958271396119 368047866660910437407094179)
      ·
        refine ⟨552071799991365656110641269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368047866660910437407094179 552071799991365656110641269)
        ·
          refine ⟨51756731249190530260372619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 552071799991365656110641269 51756731249190530260372619)
          ·
            refine ⟨77635096873785795390558929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51756731249190530260372619 77635096873785795390558929)
            ·
              refine ⟨58226322655339346542919197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77635096873785795390558929 58226322655339346542919197)
              ·
                refine ⟨21834870995752254953594699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58226322655339346542919197 21834870995752254953594699)
                ·
                  refine ⟨32752306493628382430392049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21834870995752254953594699 32752306493628382430392049)
                  ·
                    refine ⟨24564229870221286822794037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32752306493628382430392049 24564229870221286822794037)
                    ·
                      refine ⟨2302896550333245639636941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24564229870221286822794037 2302896550333245639636941)
                      ·
                        rfl

theorem cell23_4484875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_4484875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484875 prefixEnd_4484875 := by exact prefixLift 4484875
  have htrace : WordTrace (prefixWord ++ tailWord_4484875) baseStart_4484875 baseEnd_4484875 := by
    simpa [prefixWord, tailWord_4484875, baseEnd_4484875] using wordTrace_append hprefix tailTrace_4484875
  have hstable : (prefixWord ++ tailWord_4484875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484875).length < 2 ^ (prefixWord ++ tailWord_4484875).sum := by decide
  have hdescent : baseEnd_4484875 < baseStart_4484875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484895 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 2, 8]
def baseStart_4484895 : Nat := 118140960795 + 4484895 * 2 ^ 59
def prefixEnd_4484895 : Nat := 4983230072969 + 3 ^ 40 * 4484895 * 2
def baseEnd_4484895 : Nat := 767635606648778520462283

theorem tailTrace_4484895 : CollatzResearch.WordTrace tailWord_4484895 prefixEnd_4484895 767635606648778520462283 := by
  unfold tailWord_4484895
  simp only [CollatzResearch.WordTrace]
  refine ⟨163577559086998848929992139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109051706057999232619994759 163577559086998848929992139)
  ·
    refine ⟨245366338630498273394988209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163577559086998848929992139 245366338630498273394988209)
    ·
      refine ⟨184024753972873705046241157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245366338630498273394988209 184024753972873705046241157)
      ·
        refine ⟨34504641369913819696170217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184024753972873705046241157 34504641369913819696170217)
        ·
          refine ⟨25878481027435364772127663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34504641369913819696170217 25878481027435364772127663)
          ·
            refine ⟨38817721541153047158191495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25878481027435364772127663 38817721541153047158191495)
            ·
              refine ⟨58226582311729570737287243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38817721541153047158191495 58226582311729570737287243)
              ·
                refine ⟨87339873467594356105930865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58226582311729570737287243 87339873467594356105930865)
                ·
                  refine ⟨65504905100695767079448149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87339873467594356105930865 65504905100695767079448149)
                  ·
                    refine ⟨767635606648778520462283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65504905100695767079448149 767635606648778520462283)
                    ·
                      rfl

theorem cell23_4484895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_4484895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484895 prefixEnd_4484895 := by exact prefixLift 4484895
  have htrace : WordTrace (prefixWord ++ tailWord_4484895) baseStart_4484895 baseEnd_4484895 := by
    simpa [prefixWord, tailWord_4484895, baseEnd_4484895] using wordTrace_append hprefix tailTrace_4484895
  have hstable : (prefixWord ++ tailWord_4484895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484895).length < 2 ^ (prefixWord ++ tailWord_4484895).sum := by decide
  have hdescent : baseEnd_4484895 < baseStart_4484895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4484992 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_4484992 : Nat := 118140960795 + 4484992 * 2 ^ 59
def prefixEnd_4484992 : Nat := 4983230072969 + 3 ^ 40 * 4484992 * 2
def baseEnd_4484992 : Nat := 2302956627569821681873903

theorem tailTrace_4484992 : CollatzResearch.WordTrace tailWord_4484992 prefixEnd_4484992 2302956627569821681873903 := by
  unfold tailWord_4484992
  simp only [CollatzResearch.WordTrace]
  refine ⟨81790548483823717248136615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109054064645098289664182153 81790548483823717248136615)
  ·
    refine ⟨122685822725735575872204923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81790548483823717248136615 122685822725735575872204923)
    ·
      refine ⟨184028734088603363808307385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122685822725735575872204923 184028734088603363808307385)
      ·
        refine ⟨138021550566452522856230539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184028734088603363808307385 138021550566452522856230539)
        ·
          refine ⟨207032325849678784284345809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138021550566452522856230539 207032325849678784284345809)
          ·
            refine ⟨155274244387259088213259357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207032325849678784284345809 155274244387259088213259357)
            ·
              refine ⟨58227841645222158079972259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155274244387259088213259357 58227841645222158079972259)
              ·
                refine ⟨87341762467833237119958389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58227841645222158079972259 87341762467833237119958389)
                ·
                  refine ⟨8188290231359365979996099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87341762467833237119958389 8188290231359365979996099)
                  ·
                    refine ⟨12282435347039048969994149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8188290231359365979996099 12282435347039048969994149)
                    ·
                      refine ⟨2302956627569821681873903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12282435347039048969994149 2302956627569821681873903)
                      ·
                        rfl

theorem cell23_4484992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_4484992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4484992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4484992 prefixEnd_4484992 := by exact prefixLift 4484992
  have htrace : WordTrace (prefixWord ++ tailWord_4484992) baseStart_4484992 baseEnd_4484992 := by
    simpa [prefixWord, tailWord_4484992, baseEnd_4484992] using wordTrace_append hprefix tailTrace_4484992
  have hstable : (prefixWord ++ tailWord_4484992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4484992).length < 2 ^ (prefixWord ++ tailWord_4484992).sum := by decide
  have hdescent : baseEnd_4484992 < baseStart_4484992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4484992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485020 : List Nat := [2, 2, 3, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4485020 : Nat := 118140960795 + 4485020 * 2 ^ 59
def prefixEnd_4485020 : Nat := 4983230072969 + 3 ^ 40 * 4485020 * 2
def baseEnd_4485020 : Nat := 2302971005028147572323775

theorem tailTrace_4485020 : CollatzResearch.WordTrace tailWord_4485020 prefixEnd_4485020 2302971005028147572323775 := by
  unfold tailWord_4485020
  simp only [CollatzResearch.WordTrace]
  refine ⟨81791059105772997639146257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109054745474363996852195009 81791059105772997639146257)
  ·
    refine ⟨61343294329329748229359693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81791059105772997639146257 61343294329329748229359693)
    ·
      refine ⟨23003735373498655586009885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61343294329329748229359693 23003735373498655586009885)
      ·
        refine ⟨8626400765061995844753707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23003735373498655586009885 8626400765061995844753707)
        ·
          refine ⟨12939601147592993767130561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8626400765061995844753707 12939601147592993767130561)
          ·
            refine ⟨9704700860694745325347921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12939601147592993767130561 9704700860694745325347921)
            ·
              refine ⟨7278525645521058994010941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9704700860694745325347921 7278525645521058994010941)
              ·
                refine ⟨2729447117070397122754103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7278525645521058994010941 2729447117070397122754103)
                ·
                  refine ⟨4094170675605595684131155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729447117070397122754103 4094170675605595684131155)
                  ·
                    refine ⟨6141256013408393526196733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094170675605595684131155 6141256013408393526196733)
                    ·
                      refine ⟨2302971005028147572323775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6141256013408393526196733 2302971005028147572323775)
                      ·
                        rfl

theorem cell23_4485020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4485020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485020 prefixEnd_4485020 := by exact prefixLift 4485020
  have htrace : WordTrace (prefixWord ++ tailWord_4485020) baseStart_4485020 baseEnd_4485020 := by
    simpa [prefixWord, tailWord_4485020, baseEnd_4485020] using wordTrace_append hprefix tailTrace_4485020
  have hstable : (prefixWord ++ tailWord_4485020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485020).length < 2 ^ (prefixWord ++ tailWord_4485020).sum := by decide
  have hdescent : baseEnd_4485020 < baseStart_4485020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485023 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 1, 5]
def baseStart_4485023 : Nat := 118140960795 + 4485023 * 2 ^ 59
def prefixEnd_4485023 : Nat := 4983230072969 + 3 ^ 40 * 4485023 * 2
def baseEnd_4485023 : Nat := 767657515156703686862087

theorem tailTrace_4485023 : CollatzResearch.WordTrace tailWord_4485023 prefixEnd_4485023 767657515156703686862087 := by
  unfold tailWord_4485023
  simp only [CollatzResearch.WordTrace]
  refine ⟨163582227630535126790651723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109054818420356751193767815 163582227630535126790651723)
  ·
    refine ⟨245373341445802690185977585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163582227630535126790651723 245373341445802690185977585)
    ·
      refine ⟨184030006084352017639483189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245373341445802690185977585 184030006084352017639483189)
      ·
        refine ⟨17252813070408001653701549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 184030006084352017639483189 17252813070408001653701549)
        ·
          refine ⟨6469804901403000620138081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17252813070408001653701549 6469804901403000620138081)
          ·
            refine ⟨4852353676052250465103561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6469804901403000620138081 4852353676052250465103561)
            ·
              refine ⟨3639265257039187848827671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4852353676052250465103561 3639265257039187848827671)
              ·
                refine ⟨5458897885558781773241507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639265257039187848827671 5458897885558781773241507)
                ·
                  refine ⟨8188346828338172659862261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5458897885558781773241507 8188346828338172659862261)
                  ·
                    refine ⟨767657515156703686862087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8188346828338172659862261 767657515156703686862087)
                    ·
                      rfl

theorem cell23_4485023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 5].length) (baseStart_4485023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485023 prefixEnd_4485023 := by exact prefixLift 4485023
  have htrace : WordTrace (prefixWord ++ tailWord_4485023) baseStart_4485023 baseEnd_4485023 := by
    simpa [prefixWord, tailWord_4485023, baseEnd_4485023] using wordTrace_append hprefix tailTrace_4485023
  have hstable : (prefixWord ++ tailWord_4485023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485023).length < 2 ^ (prefixWord ++ tailWord_4485023).sum := by decide
  have hdescent : baseEnd_4485023 < baseStart_4485023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485043 : List Nat := [1, 1, 1, 2, 3, 1, 3, 6, 1, 2, 2]
def baseStart_4485043 : Nat := 118140960795 + 4485043 * 2 ^ 59
def prefixEnd_4485043 : Nat := 4983230072969 + 3 ^ 40 * 4485043 * 2
def baseEnd_4485043 : Nat := 2302982815083200982336169

theorem tailTrace_4485043 : CollatzResearch.WordTrace tailWord_4485043 prefixEnd_4485043 2302982815083200982336169 := by
  unfold tailWord_4485043
  simp only [CollatzResearch.WordTrace]
  refine ⟨163582957090462670206379783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109055304726975113470919855 163582957090462670206379783)
  ·
    refine ⟨245374435635694005309569675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163582957090462670206379783 245374435635694005309569675)
    ·
      refine ⟨368061653453541007964354513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245374435635694005309569675 368061653453541007964354513)
      ·
        refine ⟨276046240090155755973265885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368061653453541007964354513 276046240090155755973265885)
        ·
          refine ⟨103517340033808408489974707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276046240090155755973265885 103517340033808408489974707)
          ·
            refine ⟨155276010050712612734962061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103517340033808408489974707 155276010050712612734962061)
            ·
              refine ⟨58228503769017229775610773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155276010050712612734962061 58228503769017229775610773)
              ·
                refine ⟨2729461114172682645731755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58228503769017229775610773 2729461114172682645731755)
                ·
                  refine ⟨4094191671259023968597633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729461114172682645731755 4094191671259023968597633)
                  ·
                    refine ⟨3070643753444267976448225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094191671259023968597633 3070643753444267976448225)
                    ·
                      refine ⟨2302982815083200982336169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070643753444267976448225 2302982815083200982336169)
                      ·
                        rfl

theorem cell23_4485043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 2, 2].length) (baseStart_4485043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485043 prefixEnd_4485043 := by exact prefixLift 4485043
  have htrace : WordTrace (prefixWord ++ tailWord_4485043) baseStart_4485043 baseEnd_4485043 := by
    simpa [prefixWord, tailWord_4485043, baseEnd_4485043] using wordTrace_append hprefix tailTrace_4485043
  have hstable : (prefixWord ++ tailWord_4485043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485043).length < 2 ^ (prefixWord ++ tailWord_4485043).sum := by decide
  have hdescent : baseEnd_4485043 < baseStart_4485043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485053 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_4485053 : Nat := 118140960795 + 4485053 * 2 ^ 59
def prefixEnd_4485053 : Nat := 4983230072969 + 3 ^ 40 * 4485053 * 2
def baseEnd_4485053 : Nat := 767662649963248647737041

theorem tailTrace_4485053 : CollatzResearch.WordTrace tailWord_4485053 prefixEnd_4485053 767662649963248647737041 := by
  unfold tailWord_4485053
  simp only [CollatzResearch.WordTrace]
  refine ⟨163583321820426441914243813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109055547880284294609495875 163583321820426441914243813)
  ·
    refine ⟨30671872841329957858920715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163583321820426441914243813 30671872841329957858920715)
    ·
      refine ⟨46007809261994936788381073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30671872841329957858920715 46007809261994936788381073)
      ·
        refine ⟨34505856946496202591285805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46007809261994936788381073 34505856946496202591285805)
        ·
          refine ⟨12939696354936075971732177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34505856946496202591285805 12939696354936075971732177)
          ·
            refine ⟨9704772266202056978799133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12939696354936075971732177 9704772266202056978799133)
            ·
              refine ⟨3639289599825771367049675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9704772266202056978799133 3639289599825771367049675)
              ·
                refine ⟨5458934399738657050574513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639289599825771367049675 5458934399738657050574513)
                ·
                  refine ⟨4094200799803992787930885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5458934399738657050574513 4094200799803992787930885)
                  ·
                    refine ⟨767662649963248647737041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4094200799803992787930885 767662649963248647737041)
                    ·
                      rfl

theorem cell23_4485053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_4485053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485053 prefixEnd_4485053 := by exact prefixLift 4485053
  have htrace : WordTrace (prefixWord ++ tailWord_4485053) baseStart_4485053 baseEnd_4485053 := by
    simpa [prefixWord, tailWord_4485053, baseEnd_4485053] using wordTrace_append hprefix tailTrace_4485053
  have hstable : (prefixWord ++ tailWord_4485053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485053).length < 2 ^ (prefixWord ++ tailWord_4485053).sum := by decide
  have hdescent : baseEnd_4485053 < baseStart_4485053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485059 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 3]
def baseStart_4485059 : Nat := 118140960795 + 4485059 * 2 ^ 59
def prefixEnd_4485059 : Nat := 4983230072969 + 3 ^ 40 * 4485059 * 2
def baseEnd_4485059 : Nat := 2302991030773672919736095

theorem tailTrace_4485059 : CollatzResearch.WordTrace tailWord_4485059 prefixEnd_4485059 2302991030773672919736095 := by
  unfold tailWord_4485059
  simp only [CollatzResearch.WordTrace]
  refine ⟨163583540658404704938962231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109055693772269803292641487 163583540658404704938962231)
  ·
    refine ⟨245375310987607057408443347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163583540658404704938962231 245375310987607057408443347)
    ·
      refine ⟨368062966481410586112665021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245375310987607057408443347 368062966481410586112665021)
      ·
        refine ⟨138023612430528969792249383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368062966481410586112665021 138023612430528969792249383)
        ·
          refine ⟨207035418645793454688374075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138023612430528969792249383 207035418645793454688374075)
          ·
            refine ⟨310553127968690182032561113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207035418645793454688374075 310553127968690182032561113)
            ·
              refine ⟨232914845976517636524420835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310553127968690182032561113 232914845976517636524420835)
              ·
                refine ⟨349372268964776454786631253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232914845976517636524420835 349372268964776454786631253)
                ·
                  refine ⟨4094206276930974079530835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 349372268964776454786631253 4094206276930974079530835)
                  ·
                    refine ⟨6141309415396461119296253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094206276930974079530835 6141309415396461119296253)
                    ·
                      refine ⟨2302991030773672919736095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6141309415396461119296253 2302991030773672919736095)
                      ·
                        rfl

theorem cell23_4485059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_4485059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485059 prefixEnd_4485059 := by exact prefixLift 4485059
  have htrace : WordTrace (prefixWord ++ tailWord_4485059) baseStart_4485059 baseEnd_4485059 := by
    simpa [prefixWord, tailWord_4485059, baseEnd_4485059] using wordTrace_append hprefix tailTrace_4485059
  have hstable : (prefixWord ++ tailWord_4485059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485059).length < 2 ^ (prefixWord ++ tailWord_4485059).sum := by decide
  have hdescent : baseEnd_4485059 < baseStart_4485059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485072 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_4485072 : Nat := 118140960795 + 4485072 * 2 ^ 59
def prefixEnd_4485072 : Nat := 4983230072969 + 3 ^ 40 * 4485072 * 2
def baseEnd_4485072 : Nat := 2302997706022181368873535

theorem tailTrace_4485072 : CollatzResearch.WordTrace tailWord_4485072 prefixEnd_4485072 2302997706022181368873535 := by
  unfold tailWord_4485072
  simp only [CollatzResearch.WordTrace]
  refine ⟨81792007403678804079592735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109056009871571738772790313 81792007403678804079592735)
  ·
    refine ⟨122688011105518206119389103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81792007403678804079592735 122688011105518206119389103)
    ·
      refine ⟨184032016658277309179083655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122688011105518206119389103 184032016658277309179083655)
      ·
        refine ⟨276048024987415963768625483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184032016658277309179083655 276048024987415963768625483)
        ·
          refine ⟨414072037481123945652938225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276048024987415963768625483 414072037481123945652938225)
          ·
            refine ⟨310554028110842959239703669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414072037481123945652938225 310554028110842959239703669)
            ·
              refine ⟨29114440135391527428722219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 310554028110842959239703669 29114440135391527428722219)
              ·
                refine ⟨43671660203087291143083329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29114440135391527428722219 43671660203087291143083329)
                ·
                  refine ⟨32753745152315468357312497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43671660203087291143083329 32753745152315468357312497)
                  ·
                    refine ⟨24565308864236601267984373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32753745152315468357312497 24565308864236601267984373)
                    ·
                      refine ⟨2302997706022181368873535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24565308864236601267984373 2302997706022181368873535)
                      ·
                        rfl

theorem cell23_4485072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_4485072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485072 prefixEnd_4485072 := by exact prefixLift 4485072
  have htrace : WordTrace (prefixWord ++ tailWord_4485072) baseStart_4485072 baseEnd_4485072 := by
    simpa [prefixWord, tailWord_4485072, baseEnd_4485072] using wordTrace_append hprefix tailTrace_4485072
  have hstable : (prefixWord ++ tailWord_4485072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485072).length < 2 ^ (prefixWord ++ tailWord_4485072).sum := by decide
  have hdescent : baseEnd_4485072 < baseStart_4485072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485076 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_4485076 : Nat := 118140960795 + 4485076 * 2 ^ 59
def prefixEnd_4485076 : Nat := 4983230072969 + 3 ^ 40 * 4485076 * 2
def baseEnd_4485076 : Nat := 2302999759944799353223517

theorem tailTrace_4485076 : CollatzResearch.WordTrace tailWord_4485076 prefixEnd_4485076 2302999759944799353223517 := by
  unfold tailWord_4485076
  simp only [CollatzResearch.WordTrace]
  refine ⟨81792080349671558421165541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109056107132895411228220721 81792080349671558421165541)
  ·
    refine ⟨15336015065563417203968539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81792080349671558421165541 15336015065563417203968539)
    ·
      refine ⟨23004022598345125805952809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15336015065563417203968539 23004022598345125805952809)
      ·
        refine ⟨17253016948758844354464607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23004022598345125805952809 17253016948758844354464607)
        ·
          refine ⟨25879525423138266531696911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17253016948758844354464607 25879525423138266531696911)
          ·
            refine ⟨38819288134707399797545367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25879525423138266531696911 38819288134707399797545367)
            ·
              refine ⟨58228932202061099696318051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38819288134707399797545367 58228932202061099696318051)
              ·
                refine ⟨87343398303091649544477077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58228932202061099696318051 87343398303091649544477077)
                ·
                  refine ⟨4094221795457421072397363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87343398303091649544477077 4094221795457421072397363)
                  ·
                    refine ⟨6141332693186131608596045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094221795457421072397363 6141332693186131608596045)
                    ·
                      refine ⟨2302999759944799353223517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6141332693186131608596045 2302999759944799353223517)
                      ·
                        rfl

theorem cell23_4485076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_4485076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485076 prefixEnd_4485076 := by exact prefixLift 4485076
  have htrace : WordTrace (prefixWord ++ tailWord_4485076) baseStart_4485076 baseEnd_4485076 := by
    simpa [prefixWord, tailWord_4485076, baseEnd_4485076] using wordTrace_append hprefix tailTrace_4485076
  have hstable : (prefixWord ++ tailWord_4485076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485076).length < 2 ^ (prefixWord ++ tailWord_4485076).sum := by decide
  have hdescent : baseEnd_4485076 < baseStart_4485076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485077 : List Nat := [1, 3, 2, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_4485077 : Nat := 118140960795 + 4485077 * 2 ^ 59
def prefixEnd_4485077 : Nat := 4983230072969 + 3 ^ 40 * 4485077 * 2
def baseEnd_4485077 : Nat := 2303000273425453849311013

theorem tailTrace_4485077 : CollatzResearch.WordTrace tailWord_4485077 prefixEnd_4485077 2303000273425453849311013 := by
  unfold tailWord_4485077
  simp only [CollatzResearch.WordTrace]
  refine ⟨163584197172339494013117485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109056131448226329342078323 163584197172339494013117485)
  ·
    refine ⟨61344073939627310254919057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163584197172339494013117485 61344073939627310254919057)
    ·
      refine ⟨46008055454720482691189293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61344073939627310254919057 46008055454720482691189293)
      ·
        refine ⟨17253020795520181009195985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46008055454720482691189293 17253020795520181009195985)
        ·
          refine ⟨12939765596640135756896989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17253020795520181009195985 12939765596640135756896989)
          ·
            refine ⟨4852412098740050908836371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12939765596640135756896989 4852412098740050908836371)
            ·
              refine ⟨7278618148110076363254557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852412098740050908836371 7278618148110076363254557)
              ·
                refine ⟨2729481805541278636220459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7278618148110076363254557 2729481805541278636220459)
                ·
                  refine ⟨4094222708311917954330689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729481805541278636220459 4094222708311917954330689)
                  ·
                    refine ⟨3070667031233938465748017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094222708311917954330689 3070667031233938465748017)
                    ·
                      refine ⟨2303000273425453849311013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070667031233938465748017 2303000273425453849311013)
                      ·
                        rfl

theorem cell23_4485077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_4485077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485077 prefixEnd_4485077 := by exact prefixLift 4485077
  have htrace : WordTrace (prefixWord ++ tailWord_4485077) baseStart_4485077 baseEnd_4485077 := by
    simpa [prefixWord, tailWord_4485077, baseEnd_4485077] using wordTrace_append hprefix tailTrace_4485077
  have hstable : (prefixWord ++ tailWord_4485077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485077).length < 2 ^ (prefixWord ++ tailWord_4485077).sum := by decide
  have hdescent : baseEnd_4485077 < baseStart_4485077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485110 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_4485110 : Nat := 118140960795 + 4485110 * 2 ^ 59
def prefixEnd_4485110 : Nat := 4983230072969 + 3 ^ 40 * 4485110 * 2
def baseEnd_4485110 : Nat := 2303017218287052220198361

theorem tailTrace_4485110 : CollatzResearch.WordTrace tailWord_4485110 prefixEnd_4485110 2303017218287052220198361 := by
  unfold tailWord_4485110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224087548826246290566799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109056933854146627099379189 10224087548826246290566799)
  ·
    refine ⟨15336131323239369435850199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10224087548826246290566799 15336131323239369435850199)
    ·
      refine ⟨23004196984859054153775299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15336131323239369435850199 23004196984859054153775299)
      ·
        refine ⟨34506295477288581230662949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23004196984859054153775299 34506295477288581230662949)
        ·
          refine ⟨6469930401991608980749303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34506295477288581230662949 6469930401991608980749303)
          ·
            refine ⟨9704895602987413471123955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469930401991608980749303 9704895602987413471123955)
            ·
              refine ⟨14557343404481120206685933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9704895602987413471123955 14557343404481120206685933)
              ·
                refine ⟨5459003776680420077507225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14557343404481120206685933 5459003776680420077507225)
                ·
                  refine ⟨4094252832510315058130419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5459003776680420077507225 4094252832510315058130419)
                  ·
                    refine ⟨6141379248765472587195629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094252832510315058130419 6141379248765472587195629)
                    ·
                      refine ⟨2303017218287052220198361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6141379248765472587195629 2303017218287052220198361)
                      ·
                        rfl

theorem cell23_4485110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_4485110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485110 prefixEnd_4485110 := by exact prefixLift 4485110
  have htrace : WordTrace (prefixWord ++ tailWord_4485110) baseStart_4485110 baseEnd_4485110 := by
    simpa [prefixWord, tailWord_4485110, baseEnd_4485110] using wordTrace_append hprefix tailTrace_4485110
  have hstable : (prefixWord ++ tailWord_4485110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485110).length < 2 ^ (prefixWord ++ tailWord_4485110).sum := by decide
  have hdescent : baseEnd_4485110 < baseStart_4485110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485116 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_4485116 : Nat := 118140960795 + 4485116 * 2 ^ 59
def prefixEnd_4485116 : Nat := 4983230072969 + 3 ^ 40 * 4485116 * 2
def baseEnd_4485116 : Nat := 2303020299170979196723333

theorem tailTrace_4485116 : CollatzResearch.WordTrace tailWord_4485116 prefixEnd_4485116 2303020299170979196723333 := by
  unfold tailWord_4485116
  simp only [CollatzResearch.WordTrace]
  refine ⟨81792809809599101836893601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109057079746132135782524801 81792809809599101836893601)
  ·
    refine ⟨61344607357199326377670201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81792809809599101836893601 61344607357199326377670201)
    ·
      refine ⟨46008455517899494783252651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61344607357199326377670201 46008455517899494783252651)
      ·
        refine ⟨69012683276849242174878977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46008455517899494783252651 69012683276849242174878977)
        ·
          refine ⟨51759512457636931631159233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69012683276849242174878977 51759512457636931631159233)
          ·
            refine ⟨38819634343227698723369425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51759512457636931631159233 38819634343227698723369425)
            ·
              refine ⟨29114725757420774042527069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38819634343227698723369425 29114725757420774042527069)
              ·
                refine ⟨10918022159032790265947651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29114725757420774042527069 10918022159032790265947651)
                ·
                  refine ⟨16377033238549185398921477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10918022159032790265947651 16377033238549185398921477)
                  ·
                    refine ⟨3070693732227972262297777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16377033238549185398921477 3070693732227972262297777)
                    ·
                      refine ⟨2303020299170979196723333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070693732227972262297777 2303020299170979196723333)
                      ·
                        rfl

theorem cell23_4485116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_4485116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485116 prefixEnd_4485116 := by exact prefixLift 4485116
  have htrace : WordTrace (prefixWord ++ tailWord_4485116) baseStart_4485116 baseEnd_4485116 := by
    simpa [prefixWord, tailWord_4485116, baseEnd_4485116] using wordTrace_append hprefix tailTrace_4485116
  have hstable : (prefixWord ++ tailWord_4485116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485116).length < 2 ^ (prefixWord ++ tailWord_4485116).sum := by decide
  have hdescent : baseEnd_4485116 < baseStart_4485116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485166 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_4485166 : Nat := 118140960795 + 4485166 * 2 ^ 59
def prefixEnd_4485166 : Nat := 4983230072969 + 3 ^ 40 * 4485166 * 2
def baseEnd_4485166 : Nat := 2303045973203704001098103

theorem tailTrace_4485166 : CollatzResearch.WordTrace tailWord_4485166 prefixEnd_4485166 2303045973203704001098103 := by
  unfold tailWord_4485166
  simp only [CollatzResearch.WordTrace]
  refine ⟨20448430408627132776638419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109058295512678041475404901 20448430408627132776638419)
  ·
    refine ⟨30672645612940699164957629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20448430408627132776638419 30672645612940699164957629)
    ·
      refine ⟨11502242104852762186859111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30672645612940699164957629 11502242104852762186859111)
      ·
        refine ⟨17253363157279143280288667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11502242104852762186859111 17253363157279143280288667)
        ·
          refine ⟨25880044735918714920433001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17253363157279143280288667 25880044735918714920433001)
          ·
            refine ⟨19410033551939036190324751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25880044735918714920433001 19410033551939036190324751)
            ·
              refine ⟨29115050327908554285487127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19410033551939036190324751 29115050327908554285487127)
              ·
                refine ⟨43672575491862831428230691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29115050327908554285487127 43672575491862831428230691)
                ·
                  refine ⟨65508863237794247142346037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43672575491862831428230691 65508863237794247142346037)
                  ·
                    refine ⟨6141455928543210669594941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65508863237794247142346037 6141455928543210669594941)
                    ·
                      refine ⟨2303045973203704001098103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6141455928543210669594941 2303045973203704001098103)
                      ·
                        rfl

theorem cell23_4485166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_4485166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485166 prefixEnd_4485166 := by exact prefixLift 4485166
  have htrace : WordTrace (prefixWord ++ tailWord_4485166) baseStart_4485166 baseEnd_4485166 := by
    simpa [prefixWord, tailWord_4485166, baseEnd_4485166] using wordTrace_append hprefix tailTrace_4485166
  have hstable : (prefixWord ++ tailWord_4485166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485166).length < 2 ^ (prefixWord ++ tailWord_4485166).sum := by decide
  have hdescent : baseEnd_4485166 < baseStart_4485166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485190 : List Nat := [6, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_4485190 : Nat := 118140960795 + 4485190 * 2 ^ 59
def prefixEnd_4485190 : Nat := 4983230072969 + 3 ^ 40 * 4485190 * 2
def baseEnd_4485190 : Nat := 255895366304379100799777

theorem tailTrace_4485190 : CollatzResearch.WordTrace tailWord_4485190 prefixEnd_4485190 255895366304379100799777 := by
  unfold tailWord_4485190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112134956904066072249407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109058879080620076207987349 5112134956904066072249407)
  ·
    refine ⟨7668202435356099108374111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5112134956904066072249407 7668202435356099108374111)
    ·
      refine ⟨11502303653034148662561167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7668202435356099108374111 11502303653034148662561167)
      ·
        refine ⟨17253455479551222993841751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11502303653034148662561167 17253455479551222993841751)
        ·
          refine ⟨25880183219326834490762627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17253455479551222993841751 25880183219326834490762627)
          ·
            refine ⟨38820274828990251736143941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25880183219326834490762627 38820274828990251736143941)
            ·
              refine ⟨7278801530435672200526989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38820274828990251736143941 7278801530435672200526989)
              ·
                refine ⟨2729550573913377075197621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7278801530435672200526989 2729550573913377075197621)
                ·
                  refine ⟨255895366304379100799777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729550573913377075197621 255895366304379100799777)
                  ·
                    rfl

theorem cell23_4485190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_4485190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485190 prefixEnd_4485190 := by exact prefixLift 4485190
  have htrace : WordTrace (prefixWord ++ tailWord_4485190) baseStart_4485190 baseEnd_4485190 := by
    simpa [prefixWord, tailWord_4485190, baseEnd_4485190] using wordTrace_append hprefix tailTrace_4485190
  have hstable : (prefixWord ++ tailWord_4485190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485190).length < 2 ^ (prefixWord ++ tailWord_4485190).sum := by decide
  have hdescent : baseEnd_4485190 < baseStart_4485190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485216 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 3, 4]
def baseStart_4485216 : Nat := 118140960795 + 4485216 * 2 ^ 59
def prefixEnd_4485216 : Nat := 4983230072969 + 3 ^ 40 * 4485216 * 2
def baseEnd_4485216 : Nat := 767690549078809601824291

theorem tailTrace_4485216 : CollatzResearch.WordTrace tailWord_4485216 prefixEnd_4485216 767690549078809601824291 := by
  unfold tailWord_4485216
  simp only [CollatzResearch.WordTrace]
  refine ⟨81794633459417960376213751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109059511279223947168285001 81794633459417960376213751)
  ·
    refine ⟨122691950189126940564320627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81794633459417960376213751 122691950189126940564320627)
    ·
      refine ⟨184037925283690410846480941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122691950189126940564320627 184037925283690410846480941)
      ·
        refine ⟨69014221981383904067430353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184037925283690410846480941 69014221981383904067430353)
        ·
          refine ⟨51760666486037928050572765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69014221981383904067430353 51760666486037928050572765)
          ·
            refine ⟨19410249932264223018964787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51760666486037928050572765 19410249932264223018964787)
            ·
              refine ⟨29115374898396334528447181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19410249932264223018964787 29115374898396334528447181)
              ·
                refine ⟨10918265586898625448167693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29115374898396334528447181 10918265586898625448167693)
                ·
                  refine ⟨4094349595086984543062885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10918265586898625448167693 4094349595086984543062885)
                  ·
                    refine ⟨767690549078809601824291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4094349595086984543062885 767690549078809601824291)
                    ·
                      rfl

theorem cell23_4485216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_4485216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485216 prefixEnd_4485216 := by exact prefixLift 4485216
  have htrace : WordTrace (prefixWord ++ tailWord_4485216) baseStart_4485216 baseEnd_4485216 := by
    simpa [prefixWord, tailWord_4485216, baseEnd_4485216] using wordTrace_append hprefix tailTrace_4485216
  have hstable : (prefixWord ++ tailWord_4485216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485216).length < 2 ^ (prefixWord ++ tailWord_4485216).sum := by decide
  have hdescent : baseEnd_4485216 < baseStart_4485216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485259 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 7, 5]
def baseStart_4485259 : Nat := 118140960795 + 4485259 * 2 ^ 59
def prefixEnd_4485259 : Nat := 4983230072969 + 3 ^ 40 * 4485259 * 2
def baseEnd_4485259 : Nat := 767697908968190712411725

theorem tailTrace_4485259 : CollatzResearch.WordTrace tailWord_4485259 prefixEnd_4485259 767697908968190712411725 := by
  unfold tailWord_4485259
  simp only [CollatzResearch.WordTrace]
  refine ⟨163590835257680139096242831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109060556838453426064161887 163590835257680139096242831)
  ·
    refine ⟨245386252886520208644364247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163590835257680139096242831 245386252886520208644364247)
    ·
      refine ⟨368079379329780312966546371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245386252886520208644364247 368079379329780312966546371)
      ·
        refine ⟨552119068994670469449819557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368079379329780312966546371 552119068994670469449819557)
        ·
          refine ⟨103522325436500713021841167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 552119068994670469449819557 103522325436500713021841167)
          ·
            refine ⟨155283488154751069532761751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103522325436500713021841167 155283488154751069532761751)
            ·
              refine ⟨232925232232126604299142627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155283488154751069532761751 232925232232126604299142627)
              ·
                refine ⟨349387848348189906448713941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232925232232126604299142627 349387848348189906448713941)
                ·
                  refine ⟨8188777695660700932391733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 349387848348189906448713941 8188777695660700932391733)
                  ·
                    refine ⟨767697908968190712411725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8188777695660700932391733 767697908968190712411725)
                    ·
                      rfl

theorem cell23_4485259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 5].length) (baseStart_4485259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485259 prefixEnd_4485259 := by exact prefixLift 4485259
  have htrace : WordTrace (prefixWord ++ tailWord_4485259) baseStart_4485259 baseEnd_4485259 := by
    simpa [prefixWord, tailWord_4485259, baseEnd_4485259] using wordTrace_append hprefix tailTrace_4485259
  have hstable : (prefixWord ++ tailWord_4485259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485259).length < 2 ^ (prefixWord ++ tailWord_4485259).sum := by decide
  have hdescent : baseEnd_4485259 < baseStart_4485259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485276 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_4485276 : Nat := 118140960795 + 4485276 * 2 ^ 59
def prefixEnd_4485276 : Nat := 4983230072969 + 3 ^ 40 * 4485276 * 2
def baseEnd_4485276 : Nat := 767700818691899523574199

theorem tailTrace_4485276 : CollatzResearch.WordTrace tailWord_4485276 prefixEnd_4485276 767700818691899523574199 := by
  unfold tailWord_4485276
  simp only [CollatzResearch.WordTrace]
  refine ⟨81795727649309275499805841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109060970199079033999741121 81795727649309275499805841)
  ·
    refine ⟨61346795736981956624854381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81795727649309275499805841 61346795736981956624854381)
    ·
      refine ⟨23005048401368233734320393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61346795736981956624854381 23005048401368233734320393)
      ·
        refine ⟨17253786301026175300740295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23005048401368233734320393 17253786301026175300740295)
        ·
          refine ⟨25880679451539262951110443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17253786301026175300740295 25880679451539262951110443)
          ·
            refine ⟨38821019177308894426665665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25880679451539262951110443 38821019177308894426665665)
            ·
              refine ⟨29115764382981670819999249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38821019177308894426665665 29115764382981670819999249)
              ·
                refine ⟨21836823287236253114999437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29115764382981670819999249 21836823287236253114999437)
                ·
                  refine ⟨8188808732713594918124789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21836823287236253114999437 8188808732713594918124789)
                  ·
                    refine ⟨767700818691899523574199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8188808732713594918124789 767700818691899523574199)
                    ·
                      rfl

theorem cell23_4485276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_4485276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485276 prefixEnd_4485276 := by exact prefixLift 4485276
  have htrace : WordTrace (prefixWord ++ tailWord_4485276) baseStart_4485276 baseEnd_4485276 := by
    simpa [prefixWord, tailWord_4485276, baseEnd_4485276] using wordTrace_append hprefix tailTrace_4485276
  have hstable : (prefixWord ++ tailWord_4485276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485276).length < 2 ^ (prefixWord ++ tailWord_4485276).sum := by decide
  have hdescent : baseEnd_4485276 < baseStart_4485276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485293 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_4485293 : Nat := 118140960795 + 4485293 * 2 ^ 59
def prefixEnd_4485293 : Nat := 4983230072969 + 3 ^ 40 * 4485293 * 2
def baseEnd_4485293 : Nat := 767703728415608334736673

theorem tailTrace_4485293 : CollatzResearch.WordTrace tailWord_4485293 prefixEnd_4485293 767703728415608334736673 := by
  unfold tailWord_4485293
  simp only [CollatzResearch.WordTrace]
  refine ⟨163592075339556962902980533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109061383559704641935320355 163592075339556962902980533)
  ·
    refine ⟨15336757063083465272154425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163592075339556962902980533 15336757063083465272154425)
    ·
      refine ⟨11502567797312598954115819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15336757063083465272154425 11502567797312598954115819)
      ·
        refine ⟨17253851695968898431173729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11502567797312598954115819 17253851695968898431173729)
        ·
          refine ⟨12940388771976673823380297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17253851695968898431173729 12940388771976673823380297)
          ·
            refine ⟨9705291578982505367535223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12940388771976673823380297 9705291578982505367535223)
            ·
              refine ⟨14557937368473758051302835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705291578982505367535223 14557937368473758051302835)
              ·
                refine ⟨21836906052710637076954253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14557937368473758051302835 21836906052710637076954253)
                ·
                  refine ⟨8188839769766488903857845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21836906052710637076954253 8188839769766488903857845)
                  ·
                    refine ⟨767703728415608334736673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8188839769766488903857845 767703728415608334736673)
                    ·
                      rfl

theorem cell23_4485293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_4485293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485293 prefixEnd_4485293 := by exact prefixLift 4485293
  have htrace : WordTrace (prefixWord ++ tailWord_4485293) baseStart_4485293 baseEnd_4485293 := by
    simpa [prefixWord, tailWord_4485293, baseEnd_4485293] using wordTrace_append hprefix tailTrace_4485293
  have hstable : (prefixWord ++ tailWord_4485293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485293).length < 2 ^ (prefixWord ++ tailWord_4485293).sum := by decide
  have hdescent : baseEnd_4485293 < baseStart_4485293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485306 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_4485306 : Nat := 118140960795 + 4485306 * 2 ^ 59
def prefixEnd_4485306 : Nat := 4983230072969 + 3 ^ 40 * 4485306 * 2
def baseEnd_4485306 : Nat := 767705953498444484449153

theorem tailTrace_4485306 : CollatzResearch.WordTrace tailWord_4485306 prefixEnd_4485306 767705953498444484449153 := by
  unfold tailWord_4485306
  simp only [CollatzResearch.WordTrace]
  refine ⟨40898137372127466530800943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109061699659006577415469181 40898137372127466530800943)
  ·
    refine ⟨61347206058191199796201415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40898137372127466530800943 61347206058191199796201415)
    ·
      refine ⟨92020809087286799694302123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61347206058191199796201415 92020809087286799694302123)
      ·
        refine ⟨138031213630930199541453185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92020809087286799694302123 138031213630930199541453185)
        ·
          refine ⟨103523410223197649656089889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138031213630930199541453185 103523410223197649656089889)
          ·
            refine ⟨77642557667398237242067417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103523410223197649656089889 77642557667398237242067417)
            ·
              refine ⟨58231918250548677931550563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77642557667398237242067417 58231918250548677931550563)
              ·
                refine ⟨87347877375823016897325845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58231918250548677931550563 87347877375823016897325845)
                ·
                  refine ⟨4094431751991703917062149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87347877375823016897325845 4094431751991703917062149)
                  ·
                    refine ⟨767705953498444484449153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4094431751991703917062149 767705953498444484449153)
                    ·
                      rfl

theorem cell23_4485306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_4485306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485306 prefixEnd_4485306 := by exact prefixLift 4485306
  have htrace : WordTrace (prefixWord ++ tailWord_4485306) baseStart_4485306 baseEnd_4485306 := by
    simpa [prefixWord, tailWord_4485306, baseEnd_4485306] using wordTrace_append hprefix tailTrace_4485306
  have hstable : (prefixWord ++ tailWord_4485306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485306).length < 2 ^ (prefixWord ++ tailWord_4485306).sum := by decide
  have hdescent : baseEnd_4485306 < baseStart_4485306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485323 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 2, 4]
def baseStart_4485323 : Nat := 118140960795 + 4485323 * 2 ^ 59
def prefixEnd_4485323 : Nat := 4983230072969 + 3 ^ 40 * 4485323 * 2
def baseEnd_4485323 : Nat := 767708863222153295611627

theorem tailTrace_4485323 : CollatzResearch.WordTrace tailWord_4485323 prefixEnd_4485323 767708863222153295611627 := by
  unfold tailWord_4485323
  simp only [CollatzResearch.WordTrace]
  refine ⟨163593169529448278026572623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109062113019632185351048415 163593169529448278026572623)
  ·
    refine ⟨245389754294172417039858935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163593169529448278026572623 245389754294172417039858935)
    ·
      refine ⟨368084631441258625559788403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245389754294172417039858935 368084631441258625559788403)
      ·
        refine ⟨552126947161887938339682605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368084631441258625559788403 552126947161887938339682605)
        ·
          refine ⟨207047605185707976877380977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 552126947161887938339682605 207047605185707976877380977)
          ·
            refine ⟨155285703889280982658035733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207047605185707976877380977 155285703889280982658035733)
            ·
              refine ⟨7279017369810046062095425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155285703889280982658035733 7279017369810046062095425)
              ·
                refine ⟨5459263027357534546571569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7279017369810046062095425 5459263027357534546571569)
                ·
                  refine ⟨4094447270518150909928677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5459263027357534546571569 4094447270518150909928677)
                  ·
                    refine ⟨767708863222153295611627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4094447270518150909928677 767708863222153295611627)
                    ·
                      rfl

theorem cell23_4485323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 4].length) (baseStart_4485323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485323 prefixEnd_4485323 := by exact prefixLift 4485323
  have htrace : WordTrace (prefixWord ++ tailWord_4485323) baseStart_4485323 baseEnd_4485323 := by
    simpa [prefixWord, tailWord_4485323, baseEnd_4485323] using wordTrace_append hprefix tailTrace_4485323
  have hstable : (prefixWord ++ tailWord_4485323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485323).length < 2 ^ (prefixWord ++ tailWord_4485323).sum := by decide
  have hdescent : baseEnd_4485323 < baseStart_4485323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485324 : List Nat := [2, 2, 1, 6, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4485324 : Nat := 118140960795 + 4485324 * 2 ^ 59
def prefixEnd_4485324 : Nat := 4983230072969 + 3 ^ 40 * 4485324 * 2
def baseEnd_4485324 : Nat := 2303127103147114382922377

theorem tailTrace_4485324 : CollatzResearch.WordTrace tailWord_4485324 prefixEnd_4485324 2303127103147114382922377 := by
  unfold tailWord_4485324
  simp only [CollatzResearch.WordTrace]
  refine ⟨81796603001222327598679513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109062137334963103464906017 81796603001222327598679513)
  ·
    refine ⟨61347452250916745699009635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81796603001222327598679513 61347452250916745699009635)
    ·
      refine ⟨92021178376375118548514453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61347452250916745699009635 92021178376375118548514453)
      ·
        refine ⟨4313492736392583681961615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92021178376375118548514453 4313492736392583681961615)
        ·
          refine ⟨6470239104588875522942423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4313492736392583681961615 6470239104588875522942423)
          ·
            refine ⟨9705358656883313284413635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6470239104588875522942423 9705358656883313284413635)
            ·
              refine ⟨14558037985324969926620453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705358656883313284413635 14558037985324969926620453)
              ·
                refine ⟨2729632122248431861241335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14558037985324969926620453 2729632122248431861241335)
                ·
                  refine ⟨4094448183372647791862003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729632122248431861241335 4094448183372647791862003)
                  ·
                    refine ⟨6141672275058971687793005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094448183372647791862003 6141672275058971687793005)
                    ·
                      refine ⟨2303127103147114382922377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6141672275058971687793005 2303127103147114382922377)
                      ·
                        rfl

theorem cell23_4485324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4485324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485324 prefixEnd_4485324 := by exact prefixLift 4485324
  have htrace : WordTrace (prefixWord ++ tailWord_4485324) baseStart_4485324 baseEnd_4485324 := by
    simpa [prefixWord, tailWord_4485324, baseEnd_4485324] using wordTrace_append hprefix tailTrace_4485324
  have hstable : (prefixWord ++ tailWord_4485324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485324).length < 2 ^ (prefixWord ++ tailWord_4485324).sum := by decide
  have hdescent : baseEnd_4485324 < baseStart_4485324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485336 : List Nat := [2, 1, 2, 2, 4, 1, 3, 8]
def baseStart_4485336 : Nat := 118140960795 + 4485336 * 2 ^ 59
def prefixEnd_4485336 : Nat := 4983230072969 + 3 ^ 40 * 4485336 * 2
def baseEnd_4485336 : Nat := 85301232033887716147123

theorem tailTrace_4485336 : CollatzResearch.WordTrace tailWord_4485336 prefixEnd_4485336 85301232033887716147123 := by
  unfold tailWord_4485336
  simp only [CollatzResearch.WordTrace]
  refine ⟨81796821839200590623397931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109062429118934120831197241 81796821839200590623397931)
  ·
    refine ⟨122695232758800885935096897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81796821839200590623397931 122695232758800885935096897)
    ·
      refine ⟨92021424569100664451322673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122695232758800885935096897 92021424569100664451322673)
      ·
        refine ⟨69016068426825498338492005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92021424569100664451322673 69016068426825498338492005)
        ·
          refine ⟨12940512830029780938467251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69016068426825498338492005 12940512830029780938467251)
          ·
            refine ⟨19410769245044671407700877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12940512830029780938467251 19410769245044671407700877)
            ·
              refine ⟨7279038466891751777887829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19410769245044671407700877 7279038466891751777887829)
              ·
                refine ⟨85301232033887716147123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7279038466891751777887829 85301232033887716147123)
                ·
                  rfl

theorem cell23_4485336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 8].length) (baseStart_4485336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485336 prefixEnd_4485336 := by exact prefixLift 4485336
  have htrace : WordTrace (prefixWord ++ tailWord_4485336) baseStart_4485336 baseEnd_4485336 := by
    simpa [prefixWord, tailWord_4485336, baseEnd_4485336] using wordTrace_append hprefix tailTrace_4485336
  have hstable : (prefixWord ++ tailWord_4485336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485336).length < 2 ^ (prefixWord ++ tailWord_4485336).sum := by decide
  have hdescent : baseEnd_4485336 < baseStart_4485336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6]
def baseStart_4485339 : Nat := 118140960795 + 4485339 * 2 ^ 59
def prefixEnd_4485339 : Nat := 4983230072969 + 3 ^ 40 * 4485339 * 2
def baseEnd_4485339 : Nat := 2303134805356931824234807

theorem tailTrace_4485339 : CollatzResearch.WordTrace tailWord_4485339 prefixEnd_4485339 2303134805356931824234807 := by
  unfold tailWord_4485339
  simp only [CollatzResearch.WordTrace]
  refine ⟨163593753097390312759155071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109062502064926875172770047 163593753097390312759155071)
  ·
    refine ⟨245390629646085469138732607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163593753097390312759155071 245390629646085469138732607)
    ·
      refine ⟨368085944469128203708098911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245390629646085469138732607 368085944469128203708098911)
      ·
        refine ⟨552128916703692305562148367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368085944469128203708098911 552128916703692305562148367)
        ·
          refine ⟨828193375055538458343222551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552128916703692305562148367 828193375055538458343222551)
          ·
            refine ⟨1242290062583307687514833827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828193375055538458343222551 1242290062583307687514833827)
            ·
              refine ⟨1863435093874961531272250741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242290062583307687514833827 1863435093874961531272250741)
              ·
                refine ⟨174697040050777643556773507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1863435093874961531272250741 174697040050777643556773507)
                ·
                  refine ⟨262045560076166465335160261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174697040050777643556773507 262045560076166465335160261)
                  ·
                    refine ⟨49133542514281212250342549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 262045560076166465335160261 49133542514281212250342549)
                    ·
                      refine ⟨2303134805356931824234807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49133542514281212250342549 2303134805356931824234807)
                      ·
                        rfl

theorem cell23_4485339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_4485339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485339 prefixEnd_4485339 := by exact prefixLift 4485339
  have htrace : WordTrace (prefixWord ++ tailWord_4485339) baseStart_4485339 baseEnd_4485339 := by
    simpa [prefixWord, tailWord_4485339, baseEnd_4485339] using wordTrace_append hprefix tailTrace_4485339
  have hstable : (prefixWord ++ tailWord_4485339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485339).length < 2 ^ (prefixWord ++ tailWord_4485339).sum := by decide
  have hdescent : baseEnd_4485339 < baseStart_4485339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485363 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 3]
def baseStart_4485363 : Nat := 118140960795 + 4485363 * 2 ^ 59
def prefixEnd_4485363 : Nat := 4983230072969 + 3 ^ 40 * 4485363 * 2
def baseEnd_4485363 : Nat := 2303147128892639730334697

theorem tailTrace_4485363 : CollatzResearch.WordTrace tailWord_4485363 prefixEnd_4485363 2303147128892639730334697 := by
  unfold tailWord_4485363
  simp only [CollatzResearch.WordTrace]
  refine ⟨163594628449303364858028743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109063085632868909905352495 163594628449303364858028743)
  ·
    refine ⟨245391942673955047287043115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163594628449303364858028743 245391942673955047287043115)
    ·
      refine ⟨368087914010932570930564673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245391942673955047287043115 368087914010932570930564673)
      ·
        refine ⟨276065935508199428197923505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368087914010932570930564673 276065935508199428197923505)
        ·
          refine ⟨207049451631149571148442629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276065935508199428197923505 207049451631149571148442629)
          ·
            refine ⟨38821772180840544590332993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207049451631149571148442629 38821772180840544590332993)
            ·
              refine ⟨29116329135630408442749745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38821772180840544590332993 29116329135630408442749745)
              ·
                refine ⟨21837246851722806332062309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29116329135630408442749745 21837246851722806332062309)
                ·
                  refine ⟨4094483784698026187261683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21837246851722806332062309 4094483784698026187261683)
                  ·
                    refine ⟨6141725677047039280892525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094483784698026187261683 6141725677047039280892525)
                    ·
                      refine ⟨2303147128892639730334697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6141725677047039280892525 2303147128892639730334697)
                      ·
                        rfl

theorem cell23_4485363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 3].length) (baseStart_4485363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485363 prefixEnd_4485363 := by exact prefixLift 4485363
  have htrace : WordTrace (prefixWord ++ tailWord_4485363) baseStart_4485363 baseEnd_4485363 := by
    simpa [prefixWord, tailWord_4485363, baseEnd_4485363] using wordTrace_append hprefix tailTrace_4485363
  have hstable : (prefixWord ++ tailWord_4485363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485363).length < 2 ^ (prefixWord ++ tailWord_4485363).sum := by decide
  have hdescent : baseEnd_4485363 < baseStart_4485363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485386 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4485386 : Nat := 118140960795 + 4485386 * 2 ^ 59
def prefixEnd_4485386 : Nat := 4983230072969 + 3 ^ 40 * 4485386 * 2
def baseEnd_4485386 : Nat := 2303158938947693140347091

theorem tailTrace_4485386 : CollatzResearch.WordTrace tailWord_4485386 prefixEnd_4485386 2303158938947693140347091 := by
  unfold tailWord_4485386
  simp only [CollatzResearch.WordTrace]
  refine ⟨40898866832055009946529003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109063644885480026524077341 40898866832055009946529003)
  ·
    refine ⟨61348300248082514919793505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40898866832055009946529003 61348300248082514919793505)
    ·
      refine ⟨46011225186061886189845129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61348300248082514919793505 46011225186061886189845129)
      ·
        refine ⟨34508418889546414642383847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46011225186061886189845129 34508418889546414642383847)
        ·
          refine ⟨51762628334319621963575771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34508418889546414642383847 51762628334319621963575771)
          ·
            refine ⟨77643942501479432945363657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51762628334319621963575771 77643942501479432945363657)
            ·
              refine ⟨58232956876109574709022743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77643942501479432945363657 58232956876109574709022743)
              ·
                refine ⟨87349435314164362063534115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58232956876109574709022743 87349435314164362063534115)
                ·
                  refine ⟨131024152971246543095301173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87349435314164362063534115 131024152971246543095301173)
                  ·
                    refine ⟨12283514341054363415184485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131024152971246543095301173 12283514341054363415184485)
                    ·
                      refine ⟨2303158938947693140347091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12283514341054363415184485 2303158938947693140347091)
                      ·
                        rfl

theorem cell23_4485386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4485386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485386 prefixEnd_4485386 := by exact prefixLift 4485386
  have htrace : WordTrace (prefixWord ++ tailWord_4485386) baseStart_4485386 baseEnd_4485386 := by
    simpa [prefixWord, tailWord_4485386, baseEnd_4485386] using wordTrace_append hprefix tailTrace_4485386
  have hstable : (prefixWord ++ tailWord_4485386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485386).length < 2 ^ (prefixWord ++ tailWord_4485386).sum := by decide
  have hdescent : baseEnd_4485386 < baseStart_4485386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485407 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 1, 3, 2]
def baseStart_4485407 : Nat := 118140960795 + 4485407 * 2 ^ 59
def prefixEnd_4485407 : Nat := 4983230072969 + 3 ^ 40 * 4485407 * 2
def baseEnd_4485407 : Nat := 2303169722041437558184495

theorem tailTrace_4485407 : CollatzResearch.WordTrace tailWord_4485407 prefixEnd_4485407 2303169722041437558184495 := by
  unfold tailWord_4485407
  simp only [CollatzResearch.WordTrace]
  refine ⟨163596233261143960372630475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109064155507429306915086983 163596233261143960372630475)
  ·
    refine ⟨245394349891715940558945713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163596233261143960372630475 245394349891715940558945713)
    ·
      refine ⟨184045762418786955419209285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245394349891715940558945713 184045762418786955419209285)
      ·
        refine ⟨34508580453522554141101741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184045762418786955419209285 34508580453522554141101741)
        ·
          refine ⟨12940717670070957802913153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34508580453522554141101741 12940717670070957802913153)
          ·
            refine ⟨9705538252553218352184865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12940717670070957802913153 9705538252553218352184865)
            ·
              refine ⟨7279153689414913764138649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9705538252553218352184865 7279153689414913764138649)
              ·
                refine ⟨5459365267061185323103987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7279153689414913764138649 5459365267061185323103987)
                ·
                  refine ⟨8189047900591777984655981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5459365267061185323103987 8189047900591777984655981)
                  ·
                    refine ⟨3070892962721916744245993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8189047900591777984655981 3070892962721916744245993)
                    ·
                      refine ⟨2303169722041437558184495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070892962721916744245993 2303169722041437558184495)
                      ·
                        rfl

theorem cell23_4485407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_4485407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485407 prefixEnd_4485407 := by exact prefixLift 4485407
  have htrace : WordTrace (prefixWord ++ tailWord_4485407) baseStart_4485407 baseEnd_4485407 := by
    simpa [prefixWord, tailWord_4485407, baseEnd_4485407] using wordTrace_append hprefix tailTrace_4485407
  have hstable : (prefixWord ++ tailWord_4485407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485407).length < 2 ^ (prefixWord ++ tailWord_4485407).sum := by decide
  have hdescent : baseEnd_4485407 < baseStart_4485407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485415 : List Nat := [1, 1, 8, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4485415 : Nat := 118140960795 + 4485415 * 2 ^ 59
def prefixEnd_4485415 : Nat := 4983230072969 + 3 ^ 40 * 4485415 * 2
def baseEnd_4485415 : Nat := 2303173829886673526884459

theorem tailTrace_4485415 : CollatzResearch.WordTrace tailWord_4485415 prefixEnd_4485415 2303173829886673526884459 := by
  unfold tailWord_4485415
  simp only [CollatzResearch.WordTrace]
  refine ⟨163596525045114977738921699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109064350030076651825947799 163596525045114977738921699)
  ·
    refine ⟨245394787567672466608382549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163596525045114977738921699 245394787567672466608382549)
    ·
      refine ⟨2875720166808661718066983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 245394787567672466608382549 2875720166808661718066983)
      ·
        refine ⟨4313580250212992577100475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875720166808661718066983 4313580250212992577100475)
        ·
          refine ⟨6470370375319488865650713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4313580250212992577100475 6470370375319488865650713)
          ·
            refine ⟨4852777781489616649238035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6470370375319488865650713 4852777781489616649238035)
            ·
              refine ⟨7279166672234424973857053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852777781489616649238035 7279166672234424973857053)
              ·
                refine ⟨2729687502087909365196395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7279166672234424973857053 2729687502087909365196395)
                ·
                  refine ⟨4094531253131864047794593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729687502087909365196395 4094531253131864047794593)
                  ·
                    refine ⟨3070898439848898035845945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094531253131864047794593 3070898439848898035845945)
                    ·
                      refine ⟨2303173829886673526884459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070898439848898035845945 2303173829886673526884459)
                      ·
                        rfl

theorem cell23_4485415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4485415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485415 prefixEnd_4485415 := by exact prefixLift 4485415
  have htrace : WordTrace (prefixWord ++ tailWord_4485415) baseStart_4485415 baseEnd_4485415 := by
    simpa [prefixWord, tailWord_4485415, baseEnd_4485415] using wordTrace_append hprefix tailTrace_4485415
  have hstable : (prefixWord ++ tailWord_4485415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485415).length < 2 ^ (prefixWord ++ tailWord_4485415).sum := by decide
  have hdescent : baseEnd_4485415 < baseStart_4485415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485420 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 4, 2, 2]
def baseStart_4485420 : Nat := 118140960795 + 4485420 * 2 ^ 59
def prefixEnd_4485420 : Nat := 4983230072969 + 3 ^ 40 * 4485420 * 2
def baseEnd_4485420 : Nat := 2303176397289946007321935

theorem tailTrace_4485420 : CollatzResearch.WordTrace tailWord_4485420 prefixEnd_4485420 2303176397289946007321935 := by
  unfold tailWord_4485420
  simp only [CollatzResearch.WordTrace]
  refine ⟨81798353705048431796426857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109064471606731242395235809 81798353705048431796426857)
  ·
    refine ⟨61348765278786323847320143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81798353705048431796426857 61348765278786323847320143)
    ·
      refine ⟨92023147918179485770980215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61348765278786323847320143 92023147918179485770980215)
      ·
        refine ⟨138034721877269228656470323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92023147918179485770980215 138034721877269228656470323)
        ·
          refine ⟨207052082815903842984705485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138034721877269228656470323 207052082815903842984705485)
          ·
            refine ⟨77644531055963941119264557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207052082815903842984705485 77644531055963941119264557)
            ·
              refine ⟨29116699145986477919724209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77644531055963941119264557 29116699145986477919724209)
              ·
                refine ⟨21837524359489858439793157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29116699145986477919724209 21837524359489858439793157)
                ·
                  refine ⟨4094535817404348457461217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21837524359489858439793157 4094535817404348457461217)
                  ·
                    refine ⟨3070901863053261343095913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094535817404348457461217 3070901863053261343095913)
                    ·
                      refine ⟨2303176397289946007321935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3070901863053261343095913 2303176397289946007321935)
                      ·
                        rfl

theorem cell23_4485420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_4485420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485420 prefixEnd_4485420 := by exact prefixLift 4485420
  have htrace : WordTrace (prefixWord ++ tailWord_4485420) baseStart_4485420 baseEnd_4485420 := by
    simpa [prefixWord, tailWord_4485420, baseEnd_4485420] using wordTrace_append hprefix tailTrace_4485420
  have hstable : (prefixWord ++ tailWord_4485420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485420).length < 2 ^ (prefixWord ++ tailWord_4485420).sum := by decide
  have hdescent : baseEnd_4485420 < baseStart_4485420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485436 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_4485436 : Nat := 118140960795 + 4485436 * 2 ^ 59
def prefixEnd_4485436 : Nat := 4983230072969 + 3 ^ 40 * 4485436 * 2
def baseEnd_4485436 : Nat := 2303184612980417944721861

theorem tailTrace_4485436 : CollatzResearch.WordTrace tailWord_4485436 prefixEnd_4485436 2303184612980417944721861 := by
  unfold tailWord_4485436
  simp only [CollatzResearch.WordTrace]
  refine ⟨81798645489019449162718081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109064860652025932216957441 81798645489019449162718081)
  ·
    refine ⟨61348984116764586872038561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81798645489019449162718081 61348984116764586872038561)
    ·
      refine ⟨46011738087573440154028921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61348984116764586872038561 46011738087573440154028921)
      ·
        refine ⟨34508803565680080115521691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46011738087573440154028921 34508803565680080115521691)
        ·
          refine ⟨51763205348520120173282537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34508803565680080115521691 51763205348520120173282537)
          ·
            refine ⟨38822404011390090129961903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51763205348520120173282537 38822404011390090129961903)
            ·
              refine ⟨58233606017085135194942855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38822404011390090129961903 58233606017085135194942855)
              ·
                refine ⟨87350409025627702792414283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58233606017085135194942855 87350409025627702792414283)
                ·
                  refine ⟨131025613538441554188621425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87350409025627702792414283 131025613538441554188621425)
                  ·
                    refine ⟨98269210153831165641466069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131025613538441554188621425 98269210153831165641466069)
                    ·
                      refine ⟨2303184612980417944721861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98269210153831165641466069 2303184612980417944721861)
                      ·
                        rfl

theorem cell23_4485436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_4485436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485436 prefixEnd_4485436 := by exact prefixLift 4485436
  have htrace : WordTrace (prefixWord ++ tailWord_4485436) baseStart_4485436 baseEnd_4485436 := by
    simpa [prefixWord, tailWord_4485436, baseEnd_4485436] using wordTrace_append hprefix tailTrace_4485436
  have hstable : (prefixWord ++ tailWord_4485436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485436).length < 2 ^ (prefixWord ++ tailWord_4485436).sum := by decide
  have hdescent : baseEnd_4485436 < baseStart_4485436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485443 : List Nat := [1, 1, 1, 3, 1, 3, 2, 6, 5]
def baseStart_4485443 : Nat := 118140960795 + 4485443 * 2 ^ 59
def prefixEnd_4485443 : Nat := 4983230072969 + 3 ^ 40 * 4485443 * 2
def baseEnd_4485443 : Nat := 255909800816111046370481

theorem tailTrace_4485443 : CollatzResearch.WordTrace tailWord_4485443 prefixEnd_4485443 255909800816111046370481 := by
  unfold tailWord_4485443
  simp only [CollatzResearch.WordTrace]
  refine ⟨163597546289013538520940983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109065030859342359013960655 163597546289013538520940983)
  ·
    refine ⟨245396319433520307781411475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163597546289013538520940983 245396319433520307781411475)
    ·
      refine ⟨368094479150280461672117213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245396319433520307781411475 368094479150280461672117213)
      ·
        refine ⟨138035429681355173127043955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368094479150280461672117213 138035429681355173127043955)
        ·
          refine ⟨207053144522032759690565933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138035429681355173127043955 207053144522032759690565933)
          ·
            refine ⟨77644929195762284883962225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207053144522032759690565933 77644929195762284883962225)
            ·
              refine ⟨58233696896821713662971669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77644929195762284883962225 58233696896821713662971669)
              ·
                refine ⟨2729704542038517827951797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58233696896821713662971669 2729704542038517827951797)
                ·
                  refine ⟨255909800816111046370481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729704542038517827951797 255909800816111046370481)
                  ·
                    rfl

theorem cell23_4485443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 5].length) (baseStart_4485443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485443 prefixEnd_4485443 := by exact prefixLift 4485443
  have htrace : WordTrace (prefixWord ++ tailWord_4485443) baseStart_4485443 baseEnd_4485443 := by
    simpa [prefixWord, tailWord_4485443, baseEnd_4485443] using wordTrace_append hprefix tailTrace_4485443
  have hstable : (prefixWord ++ tailWord_4485443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485443).length < 2 ^ (prefixWord ++ tailWord_4485443).sum := by decide
  have hdescent : baseEnd_4485443 < baseStart_4485443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485466 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_4485466 : Nat := 118140960795 + 4485466 * 2 ^ 59
def prefixEnd_4485466 : Nat := 4983230072969 + 3 ^ 40 * 4485466 * 2
def baseEnd_4485466 : Nat := 2303200017400052827346723

theorem tailTrace_4485466 : CollatzResearch.WordTrace tailWord_4485466 prefixEnd_4485466 2303200017400052827346723 := by
  unfold tailWord_4485466
  simp only [CollatzResearch.WordTrace]
  refine ⟨40899596291982553362257063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109065590111953475632685501 40899596291982553362257063)
  ·
    refine ⟨61349394437973830043385595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40899596291982553362257063 61349394437973830043385595)
    ·
      refine ⟨92024091656960745065078393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61349394437973830043385595 92024091656960745065078393)
      ·
        refine ⟨69018068742720558798808795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92024091656960745065078393 69018068742720558798808795)
        ·
          refine ⟨103527103114080838198213193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69018068742720558798808795 103527103114080838198213193)
          ·
            refine ⟨77645327335560628648659895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103527103114080838198213193 77645327335560628648659895)
            ·
              refine ⟨116467991003340942972989843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77645327335560628648659895 116467991003340942972989843)
              ·
                refine ⟨174701986505011414459484765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116467991003340942972989843 174701986505011414459484765)
                ·
                  refine ⟨65513244939379280422306787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174701986505011414459484765 65513244939379280422306787)
                  ·
                    refine ⟨98269867409068920633460181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65513244939379280422306787 98269867409068920633460181)
                    ·
                      refine ⟨2303200017400052827346723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98269867409068920633460181 2303200017400052827346723)
                      ·
                        rfl

theorem cell23_4485466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_4485466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485466 prefixEnd_4485466 := by exact prefixLift 4485466
  have htrace : WordTrace (prefixWord ++ tailWord_4485466) baseStart_4485466 baseEnd_4485466 := by
    simpa [prefixWord, tailWord_4485466, baseEnd_4485466] using wordTrace_append hprefix tailTrace_4485466
  have hstable : (prefixWord ++ tailWord_4485466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485466).length < 2 ^ (prefixWord ++ tailWord_4485466).sum := by decide
  have hdescent : baseEnd_4485466 < baseStart_4485466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485494 : List Nat := [5, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_4485494 : Nat := 118140960795 + 4485494 * 2 ^ 59
def prefixEnd_4485494 : Nat := 4983230072969 + 3 ^ 40 * 4485494 * 2
def baseEnd_4485494 : Nat := 255912710539819857532955

theorem tailTrace_4485494 : CollatzResearch.WordTrace tailWord_4485494 prefixEnd_4485494 255912710539819857532955 := by
  unfold tailWord_4485494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224962900739298389440471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109066270941219182820698357 10224962900739298389440471)
  ·
    refine ⟨15337444351108947584160707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10224962900739298389440471 15337444351108947584160707)
    ·
      refine ⟨23006166526663421376241061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15337444351108947584160707 23006166526663421376241061)
      ·
        refine ⟨4313656223749391508045199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23006166526663421376241061 4313656223749391508045199)
        ·
          refine ⟨6470484335624087262067799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4313656223749391508045199 6470484335624087262067799)
          ·
            refine ⟨9705726503436130893101699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6470484335624087262067799 9705726503436130893101699)
            ·
              refine ⟨14558589755154196339652549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705726503436130893101699 14558589755154196339652549)
              ·
                refine ⟨2729735579091411813684853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14558589755154196339652549 2729735579091411813684853)
                ·
                  refine ⟨255912710539819857532955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729735579091411813684853 255912710539819857532955)
                  ·
                    rfl

theorem cell23_4485494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_4485494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485494 prefixEnd_4485494 := by exact prefixLift 4485494
  have htrace : WordTrace (prefixWord ++ tailWord_4485494) baseStart_4485494 baseEnd_4485494 := by
    simpa [prefixWord, tailWord_4485494, baseEnd_4485494] using wordTrace_append hprefix tailTrace_4485494
  have hstable : (prefixWord ++ tailWord_4485494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485494).length < 2 ^ (prefixWord ++ tailWord_4485494).sum := by decide
  have hdescent : baseEnd_4485494 < baseStart_4485494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485524 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_4485524 : Nat := 118140960795 + 4485524 * 2 ^ 59
def prefixEnd_4485524 : Nat := 4983230072969 + 3 ^ 40 * 4485524 * 2
def baseEnd_4485524 : Nat := 767743266426004533473819

theorem tailTrace_4485524 : CollatzResearch.WordTrace tailWord_4485524 prefixEnd_4485524 767743266426004533473819 := by
  unfold tailWord_4485524
  simp only [CollatzResearch.WordTrace]
  refine ⟨81800250300860044677319813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109067000401146726236426417 81800250300860044677319813)
  ·
    refine ⟨15337546931411258376997465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81800250300860044677319813 15337546931411258376997465)
    ·
      refine ⟨11503160198558443782748099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15337546931411258376997465 11503160198558443782748099)
      ·
        refine ⟨17254740297837665674122149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11503160198558443782748099 17254740297837665674122149)
        ·
          refine ⟨3235263805844562313897903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17254740297837665674122149 3235263805844562313897903)
          ·
            refine ⟨4852895708766843470846855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235263805844562313897903 4852895708766843470846855)
            ·
              refine ⟨7279343563150265206270283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852895708766843470846855 7279343563150265206270283)
              ·
                refine ⟨10919015344725397809405425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7279343563150265206270283 10919015344725397809405425)
                ·
                  refine ⟨8189261508544048357054069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10919015344725397809405425 8189261508544048357054069)
                  ·
                    refine ⟨767743266426004533473819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8189261508544048357054069 767743266426004533473819)
                    ·
                      rfl

theorem cell23_4485524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_4485524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485524 prefixEnd_4485524 := by exact prefixLift 4485524
  have htrace : WordTrace (prefixWord ++ tailWord_4485524) baseStart_4485524 baseEnd_4485524 := by
    simpa [prefixWord, tailWord_4485524, baseEnd_4485524] using wordTrace_append hprefix tailTrace_4485524
  have hstable : (prefixWord ++ tailWord_4485524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485524).length < 2 ^ (prefixWord ++ tailWord_4485524).sum := by decide
  have hdescent : baseEnd_4485524 < baseStart_4485524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485530 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_4485530 : Nat := 118140960795 + 4485530 * 2 ^ 59
def prefixEnd_4485530 : Nat := 4983230072969 + 3 ^ 40 * 4485530 * 2
def baseEnd_4485530 : Nat := 2303232880161940576946429

theorem tailTrace_4485530 : CollatzResearch.WordTrace tailWord_4485530 prefixEnd_4485530 2303232880161940576946429 := by
  unfold tailWord_4485530
  simp only [CollatzResearch.WordTrace]
  refine ⟨40900179859924588094839511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109067146293132234919572029 40900179859924588094839511)
  ·
    refine ⟨61350269789886882142259267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40900179859924588094839511 61350269789886882142259267)
    ·
      refine ⟨92025404684830323213388901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61350269789886882142259267 92025404684830323213388901)
      ·
        refine ⟨17254763378405685602510419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92025404684830323213388901 17254763378405685602510419)
        ·
          refine ⟨25882145067608528403765629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17254763378405685602510419 25882145067608528403765629)
          ·
            refine ⟨9705804400353198151412111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25882145067608528403765629 9705804400353198151412111)
            ·
              refine ⟨14558706600529797227118167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705804400353198151412111 14558706600529797227118167)
              ·
                refine ⟨21838059900794695840677251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14558706600529797227118167 21838059900794695840677251)
                ·
                  refine ⟨32757089851192043761015877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21838059900794695840677251 32757089851192043761015877)
                  ·
                    refine ⟨6141954347098508205190477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32757089851192043761015877 6141954347098508205190477)
                    ·
                      refine ⟨2303232880161940576946429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6141954347098508205190477 2303232880161940576946429)
                      ·
                        rfl

theorem cell23_4485530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_4485530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485530 prefixEnd_4485530 := by exact prefixLift 4485530
  have htrace : WordTrace (prefixWord ++ tailWord_4485530) baseStart_4485530 baseEnd_4485530 := by
    simpa [prefixWord, tailWord_4485530, baseEnd_4485530] using wordTrace_append hprefix tailTrace_4485530
  have hstable : (prefixWord ++ tailWord_4485530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485530).length < 2 ^ (prefixWord ++ tailWord_4485530).sum := by decide
  have hdescent : baseEnd_4485530 < baseStart_4485530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485553 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4485553 : Nat := 118140960795 + 4485553 * 2 ^ 59
def prefixEnd_4485553 : Nat := 4983230072969 + 3 ^ 40 * 4485553 * 2
def baseEnd_4485553 : Nat := 2303244690216993986958823

theorem tailTrace_4485553 : CollatzResearch.WordTrace tailWord_4485553 prefixEnd_4485553 2303244690216993986958823 := by
  unfold tailWord_4485553
  simp only [CollatzResearch.WordTrace]
  refine ⟨163601558318615027307445313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109067705545743351538296875 163601558318615027307445313)
  ·
    refine ⟨122701168738961270480583985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163601558318615027307445313 122701168738961270480583985)
    ·
      refine ⟨92025876554220952860437989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122701168738961270480583985 92025876554220952860437989)
      ·
        refine ⟨17254851853916428661332123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92025876554220952860437989 17254851853916428661332123)
        ·
          refine ⟨25882277780874642991998185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17254851853916428661332123 25882277780874642991998185)
          ·
            refine ⟨19411708335655982243998639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25882277780874642991998185 19411708335655982243998639)
            ·
              refine ⟨29117562503483973365997959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19411708335655982243998639 29117562503483973365997959)
              ·
                refine ⟨43676343755225960048996939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29117562503483973365997959 43676343755225960048996939)
                ·
                  refine ⟨65514515632838940073495409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43676343755225960048996939 65514515632838940073495409)
                  ·
                    refine ⟨49135886724629205055121557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65514515632838940073495409 49135886724629205055121557)
                    ·
                      refine ⟨2303244690216993986958823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49135886724629205055121557 2303244690216993986958823)
                      ·
                        rfl

theorem cell23_4485553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4485553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485553 prefixEnd_4485553 := by exact prefixLift 4485553
  have htrace : WordTrace (prefixWord ++ tailWord_4485553) baseStart_4485553 baseEnd_4485553 := by
    simpa [prefixWord, tailWord_4485553, baseEnd_4485553] using wordTrace_append hprefix tailTrace_4485553
  have hstable : (prefixWord ++ tailWord_4485553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485553).length < 2 ^ (prefixWord ++ tailWord_4485553).sum := by decide
  have hdescent : baseEnd_4485553 < baseStart_4485553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485593 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 3, 6]
def baseStart_4485593 : Nat := 118140960795 + 4485593 * 2 ^ 59
def prefixEnd_4485593 : Nat := 4983230072969 + 3 ^ 40 * 4485593 * 2
def baseEnd_4485593 : Nat := 767755076481057943486213

theorem tailTrace_4485593 : CollatzResearch.WordTrace tailWord_4485593 prefixEnd_4485593 767755076481057943486213 := by
  unfold tailWord_4485593
  simp only [CollatzResearch.WordTrace]
  refine ⟨163603017238470114138901433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109068678158980076092600955 163603017238470114138901433)
  ·
    refine ⟨122702262928852585604176075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163603017238470114138901433 122702262928852585604176075)
    ·
      refine ⟨184053394393278878406264113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122702262928852585604176075 184053394393278878406264113)
      ·
        refine ⟨138040045794959158804698085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184053394393278878406264113 138040045794959158804698085)
        ·
          refine ⟨25882508586554842275880891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138040045794959158804698085 25882508586554842275880891)
          ·
            refine ⟨38823762879832263413821337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25882508586554842275880891 38823762879832263413821337)
            ·
              refine ⟨29117822159874197560366003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38823762879832263413821337 29117822159874197560366003)
              ·
                refine ⟨43676733239811296340549005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29117822159874197560366003 43676733239811296340549005)
                ·
                  refine ⟨16378774964929236127705877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43676733239811296340549005 16378774964929236127705877)
                  ·
                    refine ⟨767755076481057943486213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16378774964929236127705877 767755076481057943486213)
                    ·
                      rfl

theorem cell23_4485593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_4485593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485593 prefixEnd_4485593 := by exact prefixLift 4485593
  have htrace : WordTrace (prefixWord ++ tailWord_4485593) baseStart_4485593 baseEnd_4485593 := by
    simpa [prefixWord, tailWord_4485593, baseEnd_4485593] using wordTrace_append hprefix tailTrace_4485593
  have hstable : (prefixWord ++ tailWord_4485593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485593).length < 2 ^ (prefixWord ++ tailWord_4485593).sum := by decide
  have hdescent : baseEnd_4485593 < baseStart_4485593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485600 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4]
def baseStart_4485600 : Nat := 118140960795 + 4485600 * 2 ^ 59
def prefixEnd_4485600 : Nat := 4983230072969 + 3 ^ 40 * 4485600 * 2
def baseEnd_4485600 : Nat := 2303268823807755303071107

theorem tailTrace_4485600 : CollatzResearch.WordTrace tailWord_4485600 prefixEnd_4485600 2303268823807755303071107 := by
  unfold tailWord_4485600
  simp only [CollatzResearch.WordTrace]
  refine ⟨81801636274722377167203127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109068848366296502889604169 81801636274722377167203127)
  ·
    refine ⟨122702454412083565750804691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81801636274722377167203127 122702454412083565750804691)
    ·
      refine ⟨184053681618125348626207037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122702454412083565750804691 184053681618125348626207037)
      ·
        refine ⟨69020130606797005734827639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184053681618125348626207037 69020130606797005734827639)
        ·
          refine ⟨103530195910195508602241459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69020130606797005734827639 103530195910195508602241459)
          ·
            refine ⟨155295293865293262903362189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103530195910195508602241459 155295293865293262903362189)
            ·
              refine ⟨58235735199484973588760821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155295293865293262903362189 58235735199484973588760821)
              ·
                refine ⟨5459600174951716273946327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58235735199484973588760821 5459600174951716273946327)
                ·
                  refine ⟨8189400262427574410919491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5459600174951716273946327 8189400262427574410919491)
                  ·
                    refine ⟨12284100393641361616379237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8189400262427574410919491 12284100393641361616379237)
                    ·
                      refine ⟨2303268823807755303071107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12284100393641361616379237 2303268823807755303071107)
                      ·
                        rfl

theorem cell23_4485600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_4485600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485600 prefixEnd_4485600 := by exact prefixLift 4485600
  have htrace : WordTrace (prefixWord ++ tailWord_4485600) baseStart_4485600 baseEnd_4485600 := by
    simpa [prefixWord, tailWord_4485600, baseEnd_4485600] using wordTrace_append hprefix tailTrace_4485600
  have hstable : (prefixWord ++ tailWord_4485600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485600).length < 2 ^ (prefixWord ++ tailWord_4485600).sum := by decide
  have hdescent : baseEnd_4485600 < baseStart_4485600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485634 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4485634 : Nat := 118140960795 + 4485634 * 2 ^ 59
def prefixEnd_4485634 : Nat := 4983230072969 + 3 ^ 40 * 4485634 * 2
def baseEnd_4485634 : Nat := 2303286282150008170045951

theorem tailTrace_4485634 : CollatzResearch.WordTrace tailWord_4485634 prefixEnd_4485634 2303286282150008170045951 := by
  unfold tailWord_4485634
  simp only [CollatzResearch.WordTrace]
  refine ⟨40901128157830394535285989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109069675087547718760762637 40901128157830394535285989)
  ·
    refine ⟨7668961529593198975366123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40901128157830394535285989 7668961529593198975366123)
    ·
      refine ⟨11503442294389798463049185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7668961529593198975366123 11503442294389798463049185)
      ·
        refine ⟨8627581720792348847286889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11503442294389798463049185 8627581720792348847286889)
        ·
          refine ⟨6470686290594261635465167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8627581720792348847286889 6470686290594261635465167)
          ·
            refine ⟨9706029435891392453197751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6470686290594261635465167 9706029435891392453197751)
            ·
              refine ⟨14559044153837088679796627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9706029435891392453197751 14559044153837088679796627)
              ·
                refine ⟨21838566230755633019694941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14559044153837088679796627 21838566230755633019694941)
                ·
                  refine ⟨8189462336533362382385603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21838566230755633019694941 8189462336533362382385603)
                  ·
                    refine ⟨12284193504800043573578405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8189462336533362382385603 12284193504800043573578405)
                    ·
                      refine ⟨2303286282150008170045951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12284193504800043573578405 2303286282150008170045951)
                      ·
                        rfl

theorem cell23_4485634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4485634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485634 prefixEnd_4485634 := by exact prefixLift 4485634
  have htrace : WordTrace (prefixWord ++ tailWord_4485634) baseStart_4485634 baseEnd_4485634 := by
    simpa [prefixWord, tailWord_4485634, baseEnd_4485634] using wordTrace_append hprefix tailTrace_4485634
  have hstable : (prefixWord ++ tailWord_4485634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485634).length < 2 ^ (prefixWord ++ tailWord_4485634).sum := by decide
  have hdescent : baseEnd_4485634 < baseStart_4485634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485637 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_4485637 : Nat := 118140960795 + 4485637 * 2 ^ 59
def prefixEnd_4485637 : Nat := 4983230072969 + 3 ^ 40 * 4485637 * 2
def baseEnd_4485637 : Nat := 2303287822591971658308437

theorem tailTrace_4485637 : CollatzResearch.WordTrace tailWord_4485637 prefixEnd_4485637 2303287822591971658308437 := by
  unfold tailWord_4485637
  simp only [CollatzResearch.WordTrace]
  refine ⟨163604622050310709653503165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109069748033540473102335443 163604622050310709653503165)
  ·
    refine ⟨61351733268866516120063687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163604622050310709653503165 61351733268866516120063687)
    ·
      refine ⟨92027599903299774180095531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61351733268866516120063687 92027599903299774180095531)
      ·
        refine ⟨138041399854949661270143297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92027599903299774180095531 138041399854949661270143297)
        ·
          refine ⟨103531049891212245952607473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138041399854949661270143297 103531049891212245952607473)
          ·
            refine ⟨77648287418409184464455605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103531049891212245952607473 77648287418409184464455605)
            ·
              refine ⟨7279526945475861043542713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77648287418409184464455605 7279526945475861043542713)
              ·
                refine ⟨5459645209106895782657035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7279526945475861043542713 5459645209106895782657035)
                ·
                  refine ⟨8189467813660343673985553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5459645209106895782657035 8189467813660343673985553)
                  ·
                    refine ⟨6142100860245257755489165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8189467813660343673985553 6142100860245257755489165)
                    ·
                      refine ⟨2303287822591971658308437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6142100860245257755489165 2303287822591971658308437)
                      ·
                        rfl

theorem cell23_4485637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_4485637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485637 prefixEnd_4485637 := by exact prefixLift 4485637
  have htrace : WordTrace (prefixWord ++ tailWord_4485637) baseStart_4485637 baseEnd_4485637 := by
    simpa [prefixWord, tailWord_4485637, baseEnd_4485637] using wordTrace_append hprefix tailTrace_4485637
  have hstable : (prefixWord ++ tailWord_4485637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485637).length < 2 ^ (prefixWord ++ tailWord_4485637).sum := by decide
  have hdescent : baseEnd_4485637 < baseStart_4485637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485638 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_4485638 : Nat := 118140960795 + 4485638 * 2 ^ 59
def prefixEnd_4485638 : Nat := 4983230072969 + 3 ^ 40 * 4485638 * 2
def baseEnd_4485638 : Nat := 2303288336072626154395933

theorem tailTrace_4485638 : CollatzResearch.WordTrace tailWord_4485638 prefixEnd_4485638 2303288336072626154395933 := by
  unfold tailWord_4485638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112645578853346463259049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109069772348871391216193045 5112645578853346463259049)
  ·
    refine ⟨3834484184140009847444287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5112645578853346463259049 3834484184140009847444287)
    ·
      refine ⟨5751726276210014771166431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3834484184140009847444287 5751726276210014771166431)
      ·
        refine ⟨8627589414315022156749647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5751726276210014771166431 8627589414315022156749647)
        ·
          refine ⟨12941384121472533235124471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8627589414315022156749647 12941384121472533235124471)
          ·
            refine ⟨19412076182208799852686707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12941384121472533235124471 19412076182208799852686707)
            ·
              refine ⟨29118114273313199779030061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19412076182208799852686707 29118114273313199779030061)
              ·
                refine ⟨10919292852492449917136273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29118114273313199779030061 10919292852492449917136273)
                ·
                  refine ⟨8189469639369337437852205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10919292852492449917136273 8189469639369337437852205)
                  ·
                    refine ⟨3071051114763501539194577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8189469639369337437852205 3071051114763501539194577)
                    ·
                      refine ⟨2303288336072626154395933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071051114763501539194577 2303288336072626154395933)
                      ·
                        rfl

theorem cell23_4485638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_4485638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485638 prefixEnd_4485638 := by exact prefixLift 4485638
  have htrace : WordTrace (prefixWord ++ tailWord_4485638) baseStart_4485638 baseEnd_4485638 := by
    simpa [prefixWord, tailWord_4485638, baseEnd_4485638] using wordTrace_append hprefix tailTrace_4485638
  have hstable : (prefixWord ++ tailWord_4485638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485638).length < 2 ^ (prefixWord ++ tailWord_4485638).sum := by decide
  have hdescent : baseEnd_4485638 < baseStart_4485638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485707 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 1, 4, 2]
def baseStart_4485707 : Nat := 118140960795 + 4485707 * 2 ^ 59
def prefixEnd_4485707 : Nat := 4983230072969 + 3 ^ 40 * 4485707 * 2
def baseEnd_4485707 : Nat := 2303323766237786384433115

theorem tailTrace_4485707 : CollatzResearch.WordTrace tailWord_4485707 prefixEnd_4485707 2303323766237786384433115 := by
  unfold tailWord_4485707
  simp only [CollatzResearch.WordTrace]
  refine ⟨163607175160057111608551375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109071450106704741072367583 163607175160057111608551375)
  ·
    refine ⟨245410762740085667412827063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163607175160057111608551375 245410762740085667412827063)
    ·
      refine ⟨368116144110128501119240595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245410762740085667412827063 368116144110128501119240595)
      ·
        refine ⟨552174216165192751678860893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368116144110128501119240595 552174216165192751678860893)
        ·
          refine ⟨207065331061947281879572835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 552174216165192751678860893 207065331061947281879572835)
          ·
            refine ⟨310597996592920922819359253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207065331061947281879572835 310597996592920922819359253)
            ·
              refine ⟨14559281090293168257157465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 310597996592920922819359253 14559281090293168257157465)
              ·
                refine ⟨10919460817719876192868099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14559281090293168257157465 10919460817719876192868099)
                ·
                  refine ⟨16379191226579814289302149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10919460817719876192868099 16379191226579814289302149)
                  ·
                    refine ⟨3071098354983715179244153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16379191226579814289302149 3071098354983715179244153)
                    ·
                      refine ⟨2303323766237786384433115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071098354983715179244153 2303323766237786384433115)
                      ·
                        rfl

theorem cell23_4485707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4, 2].length) (baseStart_4485707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485707 prefixEnd_4485707 := by exact prefixLift 4485707
  have htrace : WordTrace (prefixWord ++ tailWord_4485707) baseStart_4485707 baseEnd_4485707 := by
    simpa [prefixWord, tailWord_4485707, baseEnd_4485707] using wordTrace_append hprefix tailTrace_4485707
  have hstable : (prefixWord ++ tailWord_4485707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485707).length < 2 ^ (prefixWord ++ tailWord_4485707).sum := by decide
  have hdescent : baseEnd_4485707 < baseStart_4485707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485710 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_4485710 : Nat := 118140960795 + 4485710 * 2 ^ 59
def prefixEnd_4485710 : Nat := 4983230072969 + 3 ^ 40 * 4485710 * 2
def baseEnd_4485710 : Nat := 2303325306679749872695601

theorem tailTrace_4485710 : CollatzResearch.WordTrace tailWord_4485710 prefixEnd_4485710 2303325306679749872695601 := by
  unfold tailWord_4485710
  simp only [CollatzResearch.WordTrace]
  refine ⟨20450910572380780390113823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109071523052697495413940389 20450910572380780390113823)
  ·
    refine ⟨30676365858571170585170735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20450910572380780390113823 30676365858571170585170735)
    ·
      refine ⟨46014548787856755877756103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30676365858571170585170735 46014548787856755877756103)
      ·
        refine ⟨69021823181785133816634155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46014548787856755877756103 69021823181785133816634155)
        ·
          refine ⟨103532734772677700724951233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69021823181785133816634155 103532734772677700724951233)
          ·
            refine ⟨77649551079508275543713425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103532734772677700724951233 77649551079508275543713425)
            ·
              refine ⟨58237163309631206657785069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77649551079508275543713425 58237163309631206657785069)
              ·
                refine ⟨21838936241111702496669401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58237163309631206657785069 21838936241111702496669401)
                ·
                  refine ⟨16379202180833776872502051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21838936241111702496669401 16379202180833776872502051)
                  ·
                    refine ⟨24568803271250665308753077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16379202180833776872502051 24568803271250665308753077)
                    ·
                      refine ⟨2303325306679749872695601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24568803271250665308753077 2303325306679749872695601)
                      ·
                        rfl

theorem cell23_4485710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_4485710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485710 prefixEnd_4485710 := by exact prefixLift 4485710
  have htrace : WordTrace (prefixWord ++ tailWord_4485710) baseStart_4485710 baseEnd_4485710 := by
    simpa [prefixWord, tailWord_4485710, baseEnd_4485710] using wordTrace_append hprefix tailTrace_4485710
  have hstable : (prefixWord ++ tailWord_4485710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485710).length < 2 ^ (prefixWord ++ tailWord_4485710).sum := by decide
  have hdescent : baseEnd_4485710 < baseStart_4485710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485720 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_4485720 : Nat := 118140960795 + 4485720 * 2 ^ 59
def prefixEnd_4485720 : Nat := 4983230072969 + 3 ^ 40 * 4485720 * 2
def baseEnd_4485720 : Nat := 2303330441486294833570555

theorem tailTrace_4485720 : CollatzResearch.WordTrace tailWord_4485720 prefixEnd_4485720 2303330441486294833570555 := by
  unfold tailWord_4485720
  simp only [CollatzResearch.WordTrace]
  refine ⟨81803824654505007414387307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109071766206006676552516409 81803824654505007414387307)
  ·
    refine ⟨122705736981757511121580961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81803824654505007414387307 122705736981757511121580961)
    ·
      refine ⟨92029302736318133341185721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122705736981757511121580961 92029302736318133341185721)
      ·
        refine ⟨69021977052238600005889291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92029302736318133341185721 69021977052238600005889291)
        ·
          refine ⟨103532965578357900008833937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69021977052238600005889291 103532965578357900008833937)
          ·
            refine ⟨77649724183768425006625453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103532965578357900008833937 77649724183768425006625453)
            ·
              refine ⟨29118646568913159377484545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77649724183768425006625453 29118646568913159377484545)
              ·
                refine ⟨21838984926684869533113409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29118646568913159377484545 21838984926684869533113409)
                ·
                  refine ⟨16379238695013652149835057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21838984926684869533113409 16379238695013652149835057)
                  ·
                    refine ⟨12284429021260239112376293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16379238695013652149835057 12284429021260239112376293)
                    ·
                      refine ⟨2303330441486294833570555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12284429021260239112376293 2303330441486294833570555)
                      ·
                        rfl

theorem cell23_4485720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_4485720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485720 prefixEnd_4485720 := by exact prefixLift 4485720
  have htrace : WordTrace (prefixWord ++ tailWord_4485720) baseStart_4485720 baseEnd_4485720 := by
    simpa [prefixWord, tailWord_4485720, baseEnd_4485720] using wordTrace_append hprefix tailTrace_4485720
  have hstable : (prefixWord ++ tailWord_4485720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485720).length < 2 ^ (prefixWord ++ tailWord_4485720).sum := by decide
  have hdescent : baseEnd_4485720 < baseStart_4485720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485741 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_4485741 : Nat := 118140960795 + 4485741 * 2 ^ 59
def prefixEnd_4485741 : Nat := 4983230072969 + 3 ^ 40 * 4485741 * 2
def baseEnd_4485741 : Nat := 2303341224580039251407959

theorem tailTrace_4485741 : CollatzResearch.WordTrace tailWord_4485741 prefixEnd_4485741 2303341224580039251407959 := by
  unfold tailWord_4485741
  simp only [CollatzResearch.WordTrace]
  refine ⟨163608415241933935415289077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109072276827955956943526051 163608415241933935415289077)
  ·
    refine ⟨15338288928931306445183351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163608415241933935415289077 15338288928931306445183351)
    ·
      refine ⟨23007433393396959667775027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15338288928931306445183351 23007433393396959667775027)
      ·
        refine ⟨34511150090095439501662541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23007433393396959667775027 34511150090095439501662541)
        ·
          refine ⟨12941681283785789813123453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34511150090095439501662541 12941681283785789813123453)
          ·
            refine ⟨4853130481419671179921295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12941681283785789813123453 4853130481419671179921295)
            ·
              refine ⟨7279695722129506769881943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4853130481419671179921295 7279695722129506769881943)
              ·
                refine ⟨10919543583194260154822915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7279695722129506769881943 10919543583194260154822915)
                ·
                  refine ⟨16379315374791390232234373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10919543583194260154822915 16379315374791390232234373)
                  ·
                    refine ⟨3071121632773385668543945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16379315374791390232234373 3071121632773385668543945)
                    ·
                      refine ⟨2303341224580039251407959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071121632773385668543945 2303341224580039251407959)
                      ·
                        rfl

theorem cell23_4485741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_4485741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485741 prefixEnd_4485741 := by exact prefixLift 4485741
  have htrace : WordTrace (prefixWord ++ tailWord_4485741) baseStart_4485741 baseEnd_4485741 := by
    simpa [prefixWord, tailWord_4485741, baseEnd_4485741] using wordTrace_append hprefix tailTrace_4485741
  have hstable : (prefixWord ++ tailWord_4485741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485741).length < 2 ^ (prefixWord ++ tailWord_4485741).sum := by decide
  have hdescent : baseEnd_4485741 < baseStart_4485741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485760 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 1, 7]
def baseStart_4485760 : Nat := 118140960795 + 4485760 * 2 ^ 59
def prefixEnd_4485760 : Nat := 4983230072969 + 3 ^ 40 * 4485760 * 2
def baseEnd_4485760 : Nat := 767783660237491559023457

theorem tailTrace_4485760 : CollatzResearch.WordTrace tailWord_4485760 prefixEnd_4485760 767783660237491559023457 := by
  unfold tailWord_4485760
  simp only [CollatzResearch.WordTrace]
  refine ⟨81804554114432550830115367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109072738819243401106820489 81804554114432550830115367)
  ·
    refine ⟨122706831171648826245173051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81804554114432550830115367 122706831171648826245173051)
    ·
      refine ⟨184060246757473239367759577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122706831171648826245173051 184060246757473239367759577)
      ·
        refine ⟨138045185068104929525819683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184060246757473239367759577 138045185068104929525819683)
        ·
          refine ⟨207067777602157394288729525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138045185068104929525819683 207067777602157394288729525)
          ·
            refine ⟨19412604150202255714568393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207067777602157394288729525 19412604150202255714568393)
            ·
              refine ⟨14559453112651691785926295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19412604150202255714568393 14559453112651691785926295)
              ·
                refine ⟨21839179668977537678889443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14559453112651691785926295 21839179668977537678889443)
                ·
                  refine ⟨32758769503466306518334165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21839179668977537678889443 32758769503466306518334165)
                  ·
                    refine ⟨767783660237491559023457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32758769503466306518334165 767783660237491559023457)
                    ·
                      rfl

theorem cell23_4485760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_4485760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485760 prefixEnd_4485760 := by exact prefixLift 4485760
  have htrace : WordTrace (prefixWord ++ tailWord_4485760) baseStart_4485760 baseEnd_4485760 := by
    simpa [prefixWord, tailWord_4485760, baseEnd_4485760] using wordTrace_append hprefix tailTrace_4485760
  have hstable : (prefixWord ++ tailWord_4485760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485760).length < 2 ^ (prefixWord ++ tailWord_4485760).sum := by decide
  have hdescent : baseEnd_4485760 < baseStart_4485760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485764 : List Nat := [2, 3, 2, 1, 3, 1, 3, 3, 5]
def baseStart_4485764 : Nat := 118140960795 + 4485764 * 2 ^ 59
def prefixEnd_4485764 : Nat := 4983230072969 + 3 ^ 40 * 4485764 * 2
def baseEnd_4485764 : Nat := 255928114959454740157817

theorem tailTrace_4485764 : CollatzResearch.WordTrace tailWord_4485764 prefixEnd_4485764 255928114959454740157817 := by
  unfold tailWord_4485764
  simp only [CollatzResearch.WordTrace]
  refine ⟨81804627060425305171688173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109072836080567073562250897 81804627060425305171688173)
  ·
    refine ⟨30676735147659489439383065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81804627060425305171688173 30676735147659489439383065)
    ·
      refine ⟨23007551360744617079537299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30676735147659489439383065 23007551360744617079537299)
      ·
        refine ⟨34511327041116925619305949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23007551360744617079537299 34511327041116925619305949)
        ·
          refine ⟨12941747640418847107239731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34511327041116925619305949 12941747640418847107239731)
          ·
            refine ⟨19412621460628270660859597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12941747640418847107239731 19412621460628270660859597)
            ·
              refine ⟨7279733047735601497822349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19412621460628270660859597 7279733047735601497822349)
              ·
                refine ⟨2729899892900850561683381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7279733047735601497822349 2729899892900850561683381)
                ·
                  refine ⟨255928114959454740157817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729899892900850561683381 255928114959454740157817)
                  ·
                    rfl

theorem cell23_4485764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_4485764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485764 prefixEnd_4485764 := by exact prefixLift 4485764
  have htrace : WordTrace (prefixWord ++ tailWord_4485764) baseStart_4485764 baseEnd_4485764 := by
    simpa [prefixWord, tailWord_4485764, baseEnd_4485764] using wordTrace_append hprefix tailTrace_4485764
  have hstable : (prefixWord ++ tailWord_4485764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485764).length < 2 ^ (prefixWord ++ tailWord_4485764).sum := by decide
  have hdescent : baseEnd_4485764 < baseStart_4485764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485797 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 1, 6, 2]
def baseStart_4485797 : Nat := 118140960795 + 4485797 * 2 ^ 59
def prefixEnd_4485797 : Nat := 4983230072969 + 3 ^ 40 * 4485797 * 2
def baseEnd_4485797 : Nat := 2303369979496691032307701

theorem tailTrace_4485797 : CollatzResearch.WordTrace tailWord_4485797 prefixEnd_4485797 2303369979496691032307701 := by
  unfold tailWord_4485797
  simp only [CollatzResearch.WordTrace]
  refine ⟨163610457729731056979327645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109073638486487371319551763 163610457729731056979327645)
  ·
    refine ⟨61353921648649146367247867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163610457729731056979327645 61353921648649146367247867)
    ·
      refine ⟨92030882472973719550871801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61353921648649146367247867 92030882472973719550871801)
      ·
        refine ⟨69023161854730289663153851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92030882472973719550871801 69023161854730289663153851)
        ·
          refine ⟨103534742782095434494730777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69023161854730289663153851 103534742782095434494730777)
          ·
            refine ⟨77651057086571575871048083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103534742782095434494730777 77651057086571575871048083)
            ·
              refine ⟨116476585629857363806572125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77651057086571575871048083 116476585629857363806572125)
              ·
                refine ⟨43678719611196511427464547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116476585629857363806572125 43678719611196511427464547)
                ·
                  refine ⟨65518079416794767141196821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43678719611196511427464547 65518079416794767141196821)
                  ·
                    refine ⟨3071159972662254709743601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65518079416794767141196821 3071159972662254709743601)
                    ·
                      refine ⟨2303369979496691032307701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071159972662254709743601 2303369979496691032307701)
                      ·
                        rfl

theorem cell23_4485797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_4485797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485797 prefixEnd_4485797 := by exact prefixLift 4485797
  have htrace : WordTrace (prefixWord ++ tailWord_4485797) baseStart_4485797 baseEnd_4485797 := by
    simpa [prefixWord, tailWord_4485797, baseEnd_4485797] using wordTrace_append hprefix tailTrace_4485797
  have hstable : (prefixWord ++ tailWord_4485797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485797).length < 2 ^ (prefixWord ++ tailWord_4485797).sum := by decide
  have hdescent : baseEnd_4485797 < baseStart_4485797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485810 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_4485810 : Nat := 118140960795 + 4485810 * 2 ^ 59
def prefixEnd_4485810 : Nat := 4983230072969 + 3 ^ 40 * 4485810 * 2
def baseEnd_4485810 : Nat := 2303376654745199481445141

theorem tailTrace_4485810 : CollatzResearch.WordTrace tailWord_4485810 prefixEnd_4485810 2303376654745199481445141 := by
  unfold tailWord_4485810
  simp only [CollatzResearch.WordTrace]
  refine ⟨40902732969670990049887721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109073954585789306799700589 40902732969670990049887721)
  ·
    refine ⟨30677049727253242537415791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40902732969670990049887721 30677049727253242537415791)
    ·
      refine ⟨46015574590879863806123687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30677049727253242537415791 46015574590879863806123687)
      ·
        refine ⟨69023361886319795709185531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46015574590879863806123687 69023361886319795709185531)
        ·
          refine ⟨103535042829479693563778297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69023361886319795709185531 103535042829479693563778297)
          ·
            refine ⟨77651282122109770172833723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103535042829479693563778297 77651282122109770172833723)
            ·
              refine ⟨116476923183164655259250585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77651282122109770172833723 116476923183164655259250585)
              ·
                refine ⟨87357692387373491444437939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116476923183164655259250585 87357692387373491444437939)
                ·
                  refine ⟨131036538581060237166656909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87357692387373491444437939 131036538581060237166656909)
                  ·
                    refine ⟨49138701967897588937496341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131036538581060237166656909 49138701967897588937496341)
                    ·
                      refine ⟨2303376654745199481445141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49138701967897588937496341 2303376654745199481445141)
                      ·
                        rfl

theorem cell23_4485810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_4485810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485810 prefixEnd_4485810 := by exact prefixLift 4485810
  have htrace : WordTrace (prefixWord ++ tailWord_4485810) baseStart_4485810 baseEnd_4485810 := by
    simpa [prefixWord, tailWord_4485810, baseEnd_4485810] using wordTrace_append hprefix tailTrace_4485810
  have hstable : (prefixWord ++ tailWord_4485810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485810).length < 2 ^ (prefixWord ++ tailWord_4485810).sum := by decide
  have hdescent : baseEnd_4485810 < baseStart_4485810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485834 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_4485834 : Nat := 118140960795 + 4485834 * 2 ^ 59
def prefixEnd_4485834 : Nat := 4983230072969 + 3 ^ 40 * 4485834 * 2
def baseEnd_4485834 : Nat := 2303388978280907387545031

theorem tailTrace_4485834 : CollatzResearch.WordTrace tailWord_4485834 prefixEnd_4485834 2303388978280907387545031 := by
  unfold tailWord_4485834
  simp only [CollatzResearch.WordTrace]
  refine ⟨40902951807649253074606139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109074538153731341532283037 40902951807649253074606139)
  ·
    refine ⟨61354427711473879611909209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40902951807649253074606139 61354427711473879611909209)
    ·
      refine ⟨46015820783605409708931907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61354427711473879611909209 46015820783605409708931907)
      ·
        refine ⟨69023731175408114563397861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46015820783605409708931907 69023731175408114563397861)
        ·
          refine ⟨12941949595389021480637099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69023731175408114563397861 12941949595389021480637099)
          ·
            refine ⟨19412924393083532220955649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12941949595389021480637099 19412924393083532220955649)
            ·
              refine ⟨14559693294812649165716737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19412924393083532220955649 14559693294812649165716737)
              ·
                refine ⟨10919769971109486874287553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14559693294812649165716737 10919769971109486874287553)
                ·
                  refine ⟨8189827478332115155715665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10919769971109486874287553 8189827478332115155715665)
                  ·
                    refine ⟨6142370608749086366786749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8189827478332115155715665 6142370608749086366786749)
                    ·
                      refine ⟨2303388978280907387545031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6142370608749086366786749 2303388978280907387545031)
                      ·
                        rfl

theorem cell23_4485834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_4485834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485834 prefixEnd_4485834 := by exact prefixLift 4485834
  have htrace : WordTrace (prefixWord ++ tailWord_4485834) baseStart_4485834 baseEnd_4485834 := by
    simpa [prefixWord, tailWord_4485834, baseEnd_4485834] using wordTrace_append hprefix tailTrace_4485834
  have hstable : (prefixWord ++ tailWord_4485834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485834).length < 2 ^ (prefixWord ++ tailWord_4485834).sum := by decide
  have hdescent : baseEnd_4485834 < baseStart_4485834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485867 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 1, 5]
def baseStart_4485867 : Nat := 118140960795 + 4485867 * 2 ^ 59
def prefixEnd_4485867 : Nat := 4983230072969 + 3 ^ 40 * 4485867 * 2
def baseEnd_4485867 : Nat := 767801974380835252810793

theorem tailTrace_4485867 : CollatzResearch.WordTrace tailWord_4485867 prefixEnd_4485867 767801974380835252810793 := by
  unfold tailWord_4485867
  simp only [CollatzResearch.WordTrace]
  refine ⟨163613010839477458934375855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109075340559651639289583903 163613010839477458934375855)
  ·
    refine ⟨245419516259216188401563783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163613010839477458934375855 245419516259216188401563783)
    ·
      refine ⟨368129274388824282602345675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245419516259216188401563783 368129274388824282602345675)
      ·
        refine ⟨552193911583236423903518513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368129274388824282602345675 552193911583236423903518513)
        ·
          refine ⟨414145433687427317927638885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552193911583236423903518513 414145433687427317927638885)
          ·
            refine ⟨77652268816392622111432291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 414145433687427317927638885 77652268816392622111432291)
            ·
              refine ⟨116478403224588933167148437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77652268816392622111432291 116478403224588933167148437)
              ·
                refine ⟨5459925151152606242210083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116478403224588933167148437 5459925151152606242210083)
                ·
                  refine ⟨8189887726728909363315125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5459925151152606242210083 8189887726728909363315125)
                  ·
                    refine ⟨767801974380835252810793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8189887726728909363315125 767801974380835252810793)
                    ·
                      rfl

theorem cell23_4485867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 5].length) (baseStart_4485867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485867 prefixEnd_4485867 := by exact prefixLift 4485867
  have htrace : WordTrace (prefixWord ++ tailWord_4485867) baseStart_4485867 baseEnd_4485867 := by
    simpa [prefixWord, tailWord_4485867, baseEnd_4485867] using wordTrace_append hprefix tailTrace_4485867
  have hstable : (prefixWord ++ tailWord_4485867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485867).length < 2 ^ (prefixWord ++ tailWord_4485867).sum := by decide
  have hdescent : baseEnd_4485867 < baseStart_4485867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485884 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_4485884 : Nat := 118140960795 + 4485884 * 2 ^ 59
def prefixEnd_4485884 : Nat := 4983230072969 + 3 ^ 40 * 4485884 * 2
def baseEnd_4485884 : Nat := 767804884104544063973267

theorem tailTrace_4485884 : CollatzResearch.WordTrace tailWord_4485884 prefixEnd_4485884 767804884104544063973267 := by
  unfold tailWord_4485884
  simp only [CollatzResearch.WordTrace]
  refine ⟨81806815440207935418872353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109075753920277247225163137 81806815440207935418872353)
  ·
    refine ⟨61355111580155951564154265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81806815440207935418872353 61355111580155951564154265)
    ·
      refine ⟨46016333685116963673115699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61355111580155951564154265 46016333685116963673115699)
      ·
        refine ⟨69024500527675445509673549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46016333685116963673115699 69024500527675445509673549)
        ·
          refine ⟨25884187697878292066127581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69024500527675445509673549 25884187697878292066127581)
          ·
            refine ⟨9706570386704359524797843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25884187697878292066127581 9706570386704359524797843)
            ·
              refine ⟨14559855580056539287196765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9706570386704359524797843 14559855580056539287196765)
              ·
                refine ⟨5459945842521202232698787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14559855580056539287196765 5459945842521202232698787)
                ·
                  refine ⟨8189918763781803349048181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5459945842521202232698787 8189918763781803349048181)
                  ·
                    refine ⟨767804884104544063973267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8189918763781803349048181 767804884104544063973267)
                    ·
                      rfl

theorem cell23_4485884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_4485884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485884 prefixEnd_4485884 := by exact prefixLift 4485884
  have htrace : WordTrace (prefixWord ++ tailWord_4485884) baseStart_4485884 baseEnd_4485884 := by
    simpa [prefixWord, tailWord_4485884, baseEnd_4485884] using wordTrace_append hprefix tailTrace_4485884
  have hstable : (prefixWord ++ tailWord_4485884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485884).length < 2 ^ (prefixWord ++ tailWord_4485884).sum := by decide
  have hdescent : baseEnd_4485884 < baseStart_4485884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485907 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5]
def baseStart_4485907 : Nat := 118140960795 + 4485907 * 2 ^ 59
def prefixEnd_4485907 : Nat := 4983230072969 + 3 ^ 40 * 4485907 * 2
def baseEnd_4485907 : Nat := 2303426462368685601932195

theorem tailTrace_4485907 : CollatzResearch.WordTrace tailWord_4485907 prefixEnd_4485907 2303426462368685601932195 := by
  unfold tailWord_4485907
  simp only [CollatzResearch.WordTrace]
  refine ⟨163614469759332545765831975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109076313172888363843887983 163614469759332545765831975)
  ·
    refine ⟨245421704638998818648747963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163614469759332545765831975 245421704638998818648747963)
    ·
      refine ⟨368132556958498227973121945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245421704638998818648747963 368132556958498227973121945)
      ·
        refine ⟨276099417718873670979841459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368132556958498227973121945 276099417718873670979841459)
        ·
          refine ⟨414149126578310506469762189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276099417718873670979841459 414149126578310506469762189)
          ·
            refine ⟨155305922466866439926160821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 414149126578310506469762189 155305922466866439926160821)
            ·
              refine ⟨14559930231268728743077577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155305922466866439926160821 14559930231268728743077577)
              ·
                refine ⟨10919947673451546557308183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14559930231268728743077577 10919947673451546557308183)
                ·
                  refine ⟨16379921510177319835962275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10919947673451546557308183 16379921510177319835962275)
                  ·
                    refine ⟨24569882265265979753943413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16379921510177319835962275 24569882265265979753943413)
                    ·
                      refine ⟨2303426462368685601932195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24569882265265979753943413 2303426462368685601932195)
                      ·
                        rfl

theorem cell23_4485907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_4485907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485907 prefixEnd_4485907 := by exact prefixLift 4485907
  have htrace : WordTrace (prefixWord ++ tailWord_4485907) baseStart_4485907 baseEnd_4485907 := by
    simpa [prefixWord, tailWord_4485907, baseEnd_4485907] using wordTrace_append hprefix tailTrace_4485907
  have hstable : (prefixWord ++ tailWord_4485907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485907).length < 2 ^ (prefixWord ++ tailWord_4485907).sum := by decide
  have hdescent : baseEnd_4485907 < baseStart_4485907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485921 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_4485921 : Nat := 118140960795 + 4485921 * 2 ^ 59
def prefixEnd_4485921 : Nat := 4983230072969 + 3 ^ 40 * 4485921 * 2
def baseEnd_4485921 : Nat := 2303433651097848547157131

theorem tailTrace_4485921 : CollatzResearch.WordTrace tailWord_4485921 prefixEnd_4485921 2303433651097848547157131 := by
  unfold tailWord_4485921
  simp only [CollatzResearch.WordTrace]
  refine ⟨163614980381281826156841617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109076653587521217437894411 163614980381281826156841617)
  ·
    refine ⟨122711235285961369617631213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163614980381281826156841617 122711235285961369617631213)
    ·
      refine ⟨46016713232235513606611705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122711235285961369617631213 46016713232235513606611705)
      ·
        refine ⟨34512534924176635204958779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46016713232235513606611705 34512534924176635204958779)
        ·
          refine ⟨51768802386264952807438169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34512534924176635204958779 51768802386264952807438169)
          ·
            refine ⟨38826601789698714605578627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51768802386264952807438169 38826601789698714605578627)
            ·
              refine ⟨58239902684548071908367941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38826601789698714605578627 58239902684548071908367941)
              ·
                refine ⟨10919981753352763482818989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58239902684548071908367941 10919981753352763482818989)
                ·
                  refine ⟨4094993157507286306057121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10919981753352763482818989 4094993157507286306057121)
                  ·
                    refine ⟨3071244868130464729542841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094993157507286306057121 3071244868130464729542841)
                    ·
                      refine ⟨2303433651097848547157131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071244868130464729542841 2303433651097848547157131)
                      ·
                        rfl

theorem cell23_4485921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_4485921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485921 prefixEnd_4485921 := by exact prefixLift 4485921
  have htrace : WordTrace (prefixWord ++ tailWord_4485921) baseStart_4485921 baseEnd_4485921 := by
    simpa [prefixWord, tailWord_4485921, baseEnd_4485921] using wordTrace_append hprefix tailTrace_4485921
  have hstable : (prefixWord ++ tailWord_4485921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485921).length < 2 ^ (prefixWord ++ tailWord_4485921).sum := by decide
  have hdescent : baseEnd_4485921 < baseStart_4485921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485941 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_4485941 : Nat := 118140960795 + 4485941 * 2 ^ 59
def prefixEnd_4485941 : Nat := 4983230072969 + 3 ^ 40 * 4485941 * 2
def baseEnd_4485941 : Nat := 2303443920710938468907039

theorem tailTrace_4485941 : CollatzResearch.WordTrace tailWord_4485941 prefixEnd_4485941 2303443920710938468907039 := by
  unfold tailWord_4485941
  simp only [CollatzResearch.WordTrace]
  refine ⟨163615709841209369572569677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109077139894139579715046451 163615709841209369572569677)
  ·
    refine ⟨61355891190453513589713629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163615709841209369572569677 61355891190453513589713629)
    ·
      refine ⟨23008459196420067596142611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61355891190453513589713629 23008459196420067596142611)
      ·
        refine ⟨34512688794630101394213917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23008459196420067596142611 34512688794630101394213917)
        ·
          refine ⟨12942258297986288022830219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34512688794630101394213917 12942258297986288022830219)
          ·
            refine ⟨19413387446979432034245329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12942258297986288022830219 19413387446979432034245329)
            ·
              refine ⟨14560040585234574025683997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19413387446979432034245329 14560040585234574025683997)
              ·
                refine ⟨5460015219462965259631499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14560040585234574025683997 5460015219462965259631499)
                ·
                  refine ⟨8190022829194447889447249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5460015219462965259631499 8190022829194447889447249)
                  ·
                    refine ⟨6142517121895835917085437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8190022829194447889447249 6142517121895835917085437)
                    ·
                      refine ⟨2303443920710938468907039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6142517121895835917085437 2303443920710938468907039)
                      ·
                        rfl

theorem cell23_4485941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_4485941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485941 prefixEnd_4485941 := by exact prefixLift 4485941
  have htrace : WordTrace (prefixWord ++ tailWord_4485941) baseStart_4485941 baseEnd_4485941 := by
    simpa [prefixWord, tailWord_4485941, baseEnd_4485941] using wordTrace_append hprefix tailTrace_4485941
  have hstable : (prefixWord ++ tailWord_4485941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485941).length < 2 ^ (prefixWord ++ tailWord_4485941).sum := by decide
  have hdescent : baseEnd_4485941 < baseStart_4485941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4485955 : List Nat := [1, 1, 1, 3, 1, 4, 5, 2, 1, 2, 2]
def baseStart_4485955 : Nat := 118140960795 + 4485955 * 2 ^ 59
def prefixEnd_4485955 : Nat := 4983230072969 + 3 ^ 40 * 4485955 * 2
def baseEnd_4485955 : Nat := 2303451109440101414131975

theorem tailTrace_4485955 : CollatzResearch.WordTrace tailWord_4485955 prefixEnd_4485955 2303451109440101414131975 := by
  unfold tailWord_4485955
  simp only [CollatzResearch.WordTrace]
  refine ⟨163616220463158649963579319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109077480308772433309052879 163616220463158649963579319)
  ·
    refine ⟨245424330694737974945368979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163616220463158649963579319 245424330694737974945368979)
    ·
      refine ⟨368136496042106962418053469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245424330694737974945368979 368136496042106962418053469)
      ·
        refine ⟨138051186015790110906770051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368136496042106962418053469 138051186015790110906770051)
        ·
          refine ⟨207076779023685166360155077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138051186015790110906770051 207076779023685166360155077)
          ·
            refine ⟨38826896066940968692529077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207076779023685166360155077 38826896066940968692529077)
            ·
              refine ⟨3640021506275715814924601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38826896066940968692529077 3640021506275715814924601)
              ·
                refine ⟨2730016129706786861193451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3640021506275715814924601 2730016129706786861193451)
                ·
                  refine ⟨4095024194560180291790177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730016129706786861193451 4095024194560180291790177)
                  ·
                    refine ⟨3071268145920135218842633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095024194560180291790177 3071268145920135218842633)
                    ·
                      refine ⟨2303451109440101414131975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071268145920135218842633 2303451109440101414131975)
                      ·
                        rfl

theorem cell23_4485955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_4485955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4485955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4485955 prefixEnd_4485955 := by exact prefixLift 4485955
  have htrace : WordTrace (prefixWord ++ tailWord_4485955) baseStart_4485955 baseEnd_4485955 := by
    simpa [prefixWord, tailWord_4485955, baseEnd_4485955] using wordTrace_append hprefix tailTrace_4485955
  have hstable : (prefixWord ++ tailWord_4485955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4485955).length < 2 ^ (prefixWord ++ tailWord_4485955).sum := by decide
  have hdescent : baseEnd_4485955 < baseStart_4485955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4485955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486007 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_4486007 : Nat := 118140960795 + 4486007 * 2 ^ 59
def prefixEnd_4486007 : Nat := 4983230072969 + 3 ^ 40 * 4486007 * 2
def baseEnd_4486007 : Nat := 2303477810434135210681735

theorem tailTrace_4486007 : CollatzResearch.WordTrace tailWord_4486007 prefixEnd_4486007 2303477810434135210681735 := by
  unfold tailWord_4486007
  simp only [CollatzResearch.WordTrace]
  refine ⟨163618117058970262844472275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109078744705980175229648183 163618117058970262844472275)
  ·
    refine ⟨245427175588455394266708413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163618117058970262844472275 245427175588455394266708413)
    ·
      refine ⟨92035190845670772850015655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245427175588455394266708413 92035190845670772850015655)
      ·
        refine ⟨138052786268506159275023483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92035190845670772850015655 138052786268506159275023483)
        ·
          refine ⟨207079179402759238912535225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138052786268506159275023483 207079179402759238912535225)
          ·
            refine ⟨155309384552069429184401419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207079179402759238912535225 155309384552069429184401419)
            ·
              refine ⟨232964076828104143776602129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155309384552069429184401419 232964076828104143776602129)
              ·
                refine ⟨174723057621078107832451597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232964076828104143776602129 174723057621078107832451597)
                ·
                  refine ⟨65521146607904290437169349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174723057621078107832451597 65521146607904290437169349)
                  ·
                    refine ⟨12285214988982054456969253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65521146607904290437169349 12285214988982054456969253)
                    ·
                      refine ⟨2303477810434135210681735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12285214988982054456969253 2303477810434135210681735)
                      ·
                        rfl

theorem cell23_4486007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_4486007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486007 prefixEnd_4486007 := by exact prefixLift 4486007
  have htrace : WordTrace (prefixWord ++ tailWord_4486007) baseStart_4486007 baseEnd_4486007 := by
    simpa [prefixWord, tailWord_4486007, baseEnd_4486007] using wordTrace_append hprefix tailTrace_4486007
  have hstable : (prefixWord ++ tailWord_4486007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486007).length < 2 ^ (prefixWord ++ tailWord_4486007).sum := by decide
  have hdescent : baseEnd_4486007 < baseStart_4486007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486011 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 4, 2, 2]
def baseStart_4486011 : Nat := 118140960795 + 4486011 * 2 ^ 59
def prefixEnd_4486011 : Nat := 4983230072969 + 3 ^ 40 * 4486011 * 2
def baseEnd_4486011 : Nat := 2303479864356753195031717

theorem tailTrace_4486011 : CollatzResearch.WordTrace tailWord_4486011 prefixEnd_4486011 2303479864356753195031717 := by
  unfold tailWord_4486011
  simp only [CollatzResearch.WordTrace]
  refine ⟨163618262950955771527617887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109078841967303847685078591 163618262950955771527617887)
  ·
    refine ⟨245427394426433657291426831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163618262950955771527617887 245427394426433657291426831)
    ·
      refine ⟨368141091639650485937140247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245427394426433657291426831 368141091639650485937140247)
      ·
        refine ⟨552211637459475728905710371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368141091639650485937140247 552211637459475728905710371)
        ·
          refine ⟨828317456189213593358565557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552211637459475728905710371 828317456189213593358565557)
          ·
            refine ⟨77654761517738774377365521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 828317456189213593358565557 77654761517738774377365521)
            ·
              refine ⟨58241071138304080783024141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77654761517738774377365521 58241071138304080783024141)
              ·
                refine ⟨21840401676864030293634053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58241071138304080783024141 21840401676864030293634053)
                ·
                  refine ⟨4095075314412005680056385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21840401676864030293634053 4095075314412005680056385)
                  ·
                    refine ⟨3071306485809004260042289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095075314412005680056385 3071306485809004260042289)
                    ·
                      refine ⟨2303479864356753195031717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071306485809004260042289 2303479864356753195031717)
                      ·
                        rfl

theorem cell23_4486011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 2, 2].length) (baseStart_4486011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486011 prefixEnd_4486011 := by exact prefixLift 4486011
  have htrace : WordTrace (prefixWord ++ tailWord_4486011) baseStart_4486011 baseEnd_4486011 := by
    simpa [prefixWord, tailWord_4486011, baseEnd_4486011] using wordTrace_append hprefix tailTrace_4486011
  have hstable : (prefixWord ++ tailWord_4486011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486011).length < 2 ^ (prefixWord ++ tailWord_4486011).sum := by decide
  have hdescent : baseEnd_4486011 < baseStart_4486011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486024 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4486024 : Nat := 118140960795 + 4486024 * 2 ^ 59
def prefixEnd_4486024 : Nat := 4983230072969 + 3 ^ 40 * 4486024 * 2
def baseEnd_4486024 : Nat := 2303486539605261644169157

theorem tailTrace_4486024 : CollatzResearch.WordTrace tailWord_4486024 prefixEnd_4486024 2303486539605261644169157 := by
  unfold tailWord_4486024
  simp only [CollatzResearch.WordTrace]
  refine ⟨81809368549954337373920563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109079158066605783165227417 81809368549954337373920563)
  ·
    refine ⟨122714052824931506060880845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81809368549954337373920563 122714052824931506060880845)
    ·
      refine ⟨46017769809349314772830317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122714052824931506060880845 46017769809349314772830317)
      ·
        refine ⟨17256663678505993039811369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46017769809349314772830317 17256663678505993039811369)
        ·
          refine ⟨12942497758879494779858527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17256663678505993039811369 12942497758879494779858527)
          ·
            refine ⟨19413746638319242169787791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12942497758879494779858527 19413746638319242169787791)
            ·
              refine ⟨29120619957478863254681687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19413746638319242169787791 29120619957478863254681687)
              ·
                refine ⟨43680929936218294882022531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29120619957478863254681687 43680929936218294882022531)
                ·
                  refine ⟨65521394904327442323033797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43680929936218294882022531 65521394904327442323033797)
                  ·
                    refine ⟨12285261544561395435568837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65521394904327442323033797 12285261544561395435568837)
                    ·
                      refine ⟨2303486539605261644169157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12285261544561395435568837 2303486539605261644169157)
                      ·
                        rfl

theorem cell23_4486024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4486024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486024 prefixEnd_4486024 := by exact prefixLift 4486024
  have htrace : WordTrace (prefixWord ++ tailWord_4486024) baseStart_4486024 baseEnd_4486024 := by
    simpa [prefixWord, tailWord_4486024, baseEnd_4486024] using wordTrace_append hprefix tailTrace_4486024
  have hstable : (prefixWord ++ tailWord_4486024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486024).length < 2 ^ (prefixWord ++ tailWord_4486024).sum := by decide
  have hdescent : baseEnd_4486024 < baseStart_4486024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486028 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 2, 2, 2]
def baseStart_4486028 : Nat := 118140960795 + 4486028 * 2 ^ 59
def prefixEnd_4486028 : Nat := 4983230072969 + 3 ^ 40 * 4486028 * 2
def baseEnd_4486028 : Nat := 2303488593527879628519139

theorem tailTrace_4486028 : CollatzResearch.WordTrace tailWord_4486028 prefixEnd_4486028 2303488593527879628519139 := by
  unfold tailWord_4486028
  simp only [CollatzResearch.WordTrace]
  refine ⟨81809441495947091715493369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109079255327929455620657825 81809441495947091715493369)
  ·
    refine ⟨61357081121960318786620027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81809441495947091715493369 61357081121960318786620027)
    ·
      refine ⟨92035621682940478179930041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61357081121960318786620027 92035621682940478179930041)
      ·
        refine ⟨69026716262205358634947531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92035621682940478179930041 69026716262205358634947531)
        ·
          refine ⟨103540074393308037952421297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69026716262205358634947531 103540074393308037952421297)
          ·
            refine ⟨77655055794981028464315973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103540074393308037952421297 77655055794981028464315973)
            ·
              refine ⟨14560322961558942837059245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77655055794981028464315973 14560322961558942837059245)
              ·
                refine ⟨5460121110584603563897217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14560322961558942837059245 5460121110584603563897217)
                ·
                  refine ⟨4095090832938452672922913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5460121110584603563897217 4095090832938452672922913)
                  ·
                    refine ⟨3071318124703839504692185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095090832938452672922913 3071318124703839504692185)
                    ·
                      refine ⟨2303488593527879628519139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071318124703839504692185 2303488593527879628519139)
                      ·
                        rfl

theorem cell23_4486028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_4486028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486028 prefixEnd_4486028 := by exact prefixLift 4486028
  have htrace : WordTrace (prefixWord ++ tailWord_4486028) baseStart_4486028 baseEnd_4486028 := by
    simpa [prefixWord, tailWord_4486028, baseEnd_4486028] using wordTrace_append hprefix tailTrace_4486028
  have hstable : (prefixWord ++ tailWord_4486028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486028).length < 2 ^ (prefixWord ++ tailWord_4486028).sum := by decide
  have hdescent : baseEnd_4486028 < baseStart_4486028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486068 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 7]
def baseStart_4486068 : Nat := 118140960795 + 4486068 * 2 ^ 59
def prefixEnd_4486068 : Nat := 4983230072969 + 3 ^ 40 * 4486068 * 2
def baseEnd_4486068 : Nat := 255945459194895496890995

theorem tailTrace_4486068 : CollatzResearch.WordTrace tailWord_4486068 prefixEnd_4486068 255945459194895496890995 := by
  unfold tailWord_4486068
  simp only [CollatzResearch.WordTrace]
  refine ⟨81810170955874635131221429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109080227941166180174961905 81810170955874635131221429)
  ·
    refine ⟨7669703527113247043552009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81810170955874635131221429 7669703527113247043552009)
    ·
      refine ⟨5752277645334935282664007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7669703527113247043552009 5752277645334935282664007)
      ·
        refine ⟨8628416468002402923996011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5752277645334935282664007 8628416468002402923996011)
        ·
          refine ⟨12942624702003604385994017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8628416468002402923996011 12942624702003604385994017)
          ·
            refine ⟨9706968526502703289495513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12942624702003604385994017 9706968526502703289495513)
            ·
              refine ⟨7280226394877027467121635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9706968526502703289495513 7280226394877027467121635)
              ·
                refine ⟨10920339592315541200682453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7280226394877027467121635 10920339592315541200682453)
                ·
                  refine ⟨255945459194895496890995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10920339592315541200682453 255945459194895496890995)
                  ·
                    rfl

theorem cell23_4486068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_4486068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486068 prefixEnd_4486068 := by exact prefixLift 4486068
  have htrace : WordTrace (prefixWord ++ tailWord_4486068) baseStart_4486068 baseEnd_4486068 := by
    simpa [prefixWord, tailWord_4486068, baseEnd_4486068] using wordTrace_append hprefix tailTrace_4486068
  have hstable : (prefixWord ++ tailWord_4486068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486068).length < 2 ^ (prefixWord ++ tailWord_4486068).sum := by decide
  have hdescent : baseEnd_4486068 < baseStart_4486068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486161 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 1, 5, 2]
def baseStart_4486161 : Nat := 118140960795 + 4486161 * 2 ^ 59
def prefixEnd_4486161 : Nat := 4983230072969 + 3 ^ 40 * 4486161 * 2
def baseEnd_4486161 : Nat := 2303556886454927608156027

theorem tailTrace_4486161 : CollatzResearch.WordTrace tailWord_4486161 prefixEnd_4486161 2303556886454927608156027 := by
  unfold tailWord_4486161
  simp only [CollatzResearch.WordTrace]
  refine ⟨163623733900412347145578337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109082489266941564763718891 163623733900412347145578337)
  ·
    refine ⟨122717800425309260359183753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163623733900412347145578337 122717800425309260359183753)
    ·
      refine ⟨92038350318981945269387815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122717800425309260359183753 92038350318981945269387815)
      ·
        refine ⟨138057525478472917904081723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92038350318981945269387815 138057525478472917904081723)
        ·
          refine ⟨207086288217709376856122585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138057525478472917904081723 207086288217709376856122585)
          ·
            refine ⟨155314716163282032642091939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207086288217709376856122585 155314716163282032642091939)
            ·
              refine ⟨232972074244923048963137909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155314716163282032642091939 232972074244923048963137909)
              ·
                refine ⟨21841131960461535840294179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232972074244923048963137909 21841131960461535840294179)
                ·
                  refine ⟨32761697940692303760441269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21841131960461535840294179 32761697940692303760441269)
                  ·
                    refine ⟨3071409181939903477541369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32761697940692303760441269 3071409181939903477541369)
                    ·
                      refine ⟨2303556886454927608156027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071409181939903477541369 2303556886454927608156027)
                      ·
                        rfl

theorem cell23_4486161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_4486161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486161 prefixEnd_4486161 := by exact prefixLift 4486161
  have htrace : WordTrace (prefixWord ++ tailWord_4486161) baseStart_4486161 baseEnd_4486161 := by
    simpa [prefixWord, tailWord_4486161, baseEnd_4486161] using wordTrace_append hprefix tailTrace_4486161
  have hstable : (prefixWord ++ tailWord_4486161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486161).length < 2 ^ (prefixWord ++ tailWord_4486161).sum := by decide
  have hdescent : baseEnd_4486161 < baseStart_4486161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486201 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 1, 6]
def baseStart_4486201 : Nat := 118140960795 + 4486201 * 2 ^ 59
def prefixEnd_4486201 : Nat := 4983230072969 + 3 ^ 40 * 4486201 * 2
def baseEnd_4486201 : Nat := 767859141893702483885281

theorem tailTrace_4486201 : CollatzResearch.WordTrace tailWord_4486201 prefixEnd_4486201 767859141893702483885281 := by
  unfold tailWord_4486201
  simp only [CollatzResearch.WordTrace]
  refine ⟨163625192820267433977034457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109083461880178289318022971 163625192820267433977034457)
  ·
    refine ⟨122718894615200575482775843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163625192820267433977034457 122718894615200575482775843)
    ·
      refine ⟨184078341922800863224163765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122718894615200575482775843 184078341922800863224163765)
      ·
        refine ⟨17257344555262580927265353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 184078341922800863224163765 17257344555262580927265353)
        ·
          refine ⟨12943008416446935695449015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17257344555262580927265353 12943008416446935695449015)
          ·
            refine ⟨19414512624670403543173523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12943008416446935695449015 19414512624670403543173523)
            ·
              refine ⟨29121768937005605314760285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19414512624670403543173523 29121768937005605314760285)
              ·
                refine ⟨10920663351377101993035107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29121768937005605314760285 10920663351377101993035107)
                ·
                  refine ⟨16380995027065652989552661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10920663351377101993035107 16380995027065652989552661)
                  ·
                    refine ⟨767859141893702483885281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16380995027065652989552661 767859141893702483885281)
                    ·
                      rfl

theorem cell23_4486201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_4486201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486201 prefixEnd_4486201 := by exact prefixLift 4486201
  have htrace : WordTrace (prefixWord ++ tailWord_4486201) baseStart_4486201 baseEnd_4486201 := by
    simpa [prefixWord, tailWord_4486201, baseEnd_4486201] using wordTrace_append hprefix tailTrace_4486201
  have hstable : (prefixWord ++ tailWord_4486201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486201).length < 2 ^ (prefixWord ++ tailWord_4486201).sum := by decide
  have hdescent : baseEnd_4486201 < baseStart_4486201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486211 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 3]
def baseStart_4486211 : Nat := 118140960795 + 4486211 * 2 ^ 59
def prefixEnd_4486211 : Nat := 4983230072969 + 3 ^ 40 * 4486211 * 2
def baseEnd_4486211 : Nat := 2303582560487652412530797

theorem tailTrace_4486211 : CollatzResearch.WordTrace tailWord_4486211 prefixEnd_4486211 2303582560487652412530797 := by
  unfold tailWord_4486211
  simp only [CollatzResearch.WordTrace]
  refine ⟨163625557550231205684898487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109083705033487470456598991 163625557550231205684898487)
  ·
    refine ⟨245438336325346808527347731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163625557550231205684898487 245438336325346808527347731)
    ·
      refine ⟨368157504488020212791021597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245438336325346808527347731 368157504488020212791021597)
      ·
        refine ⟨138059064183007579796633099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368157504488020212791021597 138059064183007579796633099)
        ·
          refine ⟨207088596274511369694949649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138059064183007579796633099 207088596274511369694949649)
          ·
            refine ⟨155316447205883527271212237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207088596274511369694949649 155316447205883527271212237)
            ·
              refine ⟨58243667702206322726704589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155316447205883527271212237 58243667702206322726704589)
              ·
                refine ⟨21841375388327371022514221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58243667702206322726704589 21841375388327371022514221)
                ·
                  refine ⟨8190515770622764133442833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21841375388327371022514221 8190515770622764133442833)
                  ·
                    refine ⟨6142886827967073100082125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8190515770622764133442833 6142886827967073100082125)
                    ·
                      refine ⟨2303582560487652412530797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6142886827967073100082125 2303582560487652412530797)
                      ·
                        rfl

theorem cell23_4486211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_4486211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486211 prefixEnd_4486211 := by exact prefixLift 4486211
  have htrace : WordTrace (prefixWord ++ tailWord_4486211) baseStart_4486211 baseEnd_4486211 := by
    simpa [prefixWord, tailWord_4486211, baseEnd_4486211] using wordTrace_append hprefix tailTrace_4486211
  have hstable : (prefixWord ++ tailWord_4486211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486211).length < 2 ^ (prefixWord ++ tailWord_4486211).sum := by decide
  have hdescent : baseEnd_4486211 < baseStart_4486211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486241 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_4486241 : Nat := 118140960795 + 4486241 * 2 ^ 59
def prefixEnd_4486241 : Nat := 4983230072969 + 3 ^ 40 * 4486241 * 2
def baseEnd_4486241 : Nat := 2303597964907287295155659

theorem tailTrace_4486241 : CollatzResearch.WordTrace tailWord_4486241 prefixEnd_4486241 2303597964907287295155659 := by
  unfold tailWord_4486241
  simp only [CollatzResearch.WordTrace]
  refine ⟨163626651740122520808490577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109084434493415013872327051 163626651740122520808490577)
  ·
    refine ⟨122719988805091890606367933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163626651740122520808490577 122719988805091890606367933)
    ·
      refine ⟨46019995801909458977387975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122719988805091890606367933 46019995801909458977387975)
      ·
        refine ⟨69029993702864188466081963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46019995801909458977387975 69029993702864188466081963)
        ·
          refine ⟨103544990554296282699122945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69029993702864188466081963 103544990554296282699122945)
          ·
            refine ⟨77658742915722212024342209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103544990554296282699122945 77658742915722212024342209)
            ·
              refine ⟨58244057186791659018256657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77658742915722212024342209 58244057186791659018256657)
              ·
                refine ⟨43683042890093744263692493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58244057186791659018256657 43683042890093744263692493)
                ·
                  refine ⟨16381141083785154098884685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43683042890093744263692493 16381141083785154098884685)
                  ·
                    refine ⟨6142927906419432787081757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16381141083785154098884685 6142927906419432787081757)
                    ·
                      refine ⟨2303597964907287295155659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6142927906419432787081757 2303597964907287295155659)
                      ·
                        rfl

theorem cell23_4486241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_4486241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486241 prefixEnd_4486241 := by exact prefixLift 4486241
  have htrace : WordTrace (prefixWord ++ tailWord_4486241) baseStart_4486241 baseEnd_4486241 := by
    simpa [prefixWord, tailWord_4486241, baseEnd_4486241] using wordTrace_append hprefix tailTrace_4486241
  have hstable : (prefixWord ++ tailWord_4486241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486241).length < 2 ^ (prefixWord ++ tailWord_4486241).sum := by decide
  have hdescent : baseEnd_4486241 < baseStart_4486241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486242 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4486242 : Nat := 118140960795 + 4486242 * 2 ^ 59
def prefixEnd_4486242 : Nat := 4983230072969 + 3 ^ 40 * 4486242 * 2
def baseEnd_4486242 : Nat := 2303598478387941791243155

theorem tailTrace_4486242 : CollatzResearch.WordTrace tailWord_4486242 prefixEnd_4486242 2303598478387941791243155 := by
  unfold tailWord_4486242
  simp only [CollatzResearch.WordTrace]
  refine ⟨40906672053279724494819245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109084458808745931986184653 40906672053279724494819245)
  ·
    refine ⟨15340002019979896685557217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40906672053279724494819245 15340002019979896685557217)
    ·
      refine ⟨11505001514984922514167913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15340002019979896685557217 11505001514984922514167913)
      ·
        refine ⟨8628751136238691885625935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11505001514984922514167913 8628751136238691885625935)
        ·
          refine ⟨12943126704358037828438903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8628751136238691885625935 12943126704358037828438903)
          ·
            refine ⟨19414690056537056742658355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12943126704358037828438903 19414690056537056742658355)
            ·
              refine ⟨29122035084805585113987533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19414690056537056742658355 29122035084805585113987533)
              ·
                refine ⟨10920763156802094417745325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29122035084805585113987533 10920763156802094417745325)
                ·
                  refine ⟨4095286183800785406654497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10920763156802094417745325 4095286183800785406654497)
                  ·
                    refine ⟨3071464637850589054990873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095286183800785406654497 3071464637850589054990873)
                    ·
                      refine ⟨2303598478387941791243155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071464637850589054990873 2303598478387941791243155)
                      ·
                        rfl

theorem cell23_4486242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4486242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486242 prefixEnd_4486242 := by exact prefixLift 4486242
  have htrace : WordTrace (prefixWord ++ tailWord_4486242) baseStart_4486242 baseEnd_4486242 := by
    simpa [prefixWord, tailWord_4486242, baseEnd_4486242] using wordTrace_append hprefix tailTrace_4486242
  have hstable : (prefixWord ++ tailWord_4486242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486242).length < 2 ^ (prefixWord ++ tailWord_4486242).sum := by decide
  have hdescent : baseEnd_4486242 < baseStart_4486242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486265 : List Nat := [1, 2, 1, 3, 6, 1, 2, 7]
def baseStart_4486265 : Nat := 118140960795 + 4486265 * 2 ^ 59
def prefixEnd_4486265 : Nat := 4983230072969 + 3 ^ 40 * 4486265 * 2
def baseEnd_4486265 : Nat := 85318899571962785231687

theorem tailTrace_4486265 : CollatzResearch.WordTrace tailWord_4486265 prefixEnd_4486265 85318899571962785231687 := by
  unfold tailWord_4486265
  simp only [CollatzResearch.WordTrace]
  refine ⟨163627527092035572907364249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109085018061357048604909499 163627527092035572907364249)
  ·
    refine ⟨122720645319026679680523187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163627527092035572907364249 122720645319026679680523187)
    ·
      refine ⟨184080967978540019520784781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122720645319026679680523187 184080967978540019520784781)
      ·
        refine ⟨69030362991952507320294293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184080967978540019520784781 69030362991952507320294293)
        ·
          refine ⟨3235798265247773780638795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69030362991952507320294293 3235798265247773780638795)
          ·
            refine ⟨4853697397871660670958193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235798265247773780638795 4853697397871660670958193)
            ·
              refine ⟨3640273048403745503218645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4853697397871660670958193 3640273048403745503218645)
              ·
                refine ⟨85318899571962785231687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3640273048403745503218645 85318899571962785231687)
                ·
                  rfl

theorem cell23_4486265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 7].length) (baseStart_4486265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486265 prefixEnd_4486265 := by exact prefixLift 4486265
  have htrace : WordTrace (prefixWord ++ tailWord_4486265) baseStart_4486265 baseEnd_4486265 := by
    simpa [prefixWord, tailWord_4486265, baseEnd_4486265] using wordTrace_append hprefix tailTrace_4486265
  have hstable : (prefixWord ++ tailWord_4486265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486265).length < 2 ^ (prefixWord ++ tailWord_4486265).sum := by decide
  have hdescent : baseEnd_4486265 < baseStart_4486265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486270 : List Nat := [4, 2, 4, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4486270 : Nat := 118140960795 + 4486270 * 2 ^ 59
def prefixEnd_4486270 : Nat := 4983230072969 + 3 ^ 40 * 4486270 * 2
def baseEnd_4486270 : Nat := 2303612855846267681693027

theorem tailTrace_4486270 : CollatzResearch.WordTrace tailWord_4486270 prefixEnd_4486270 2303612855846267681693027 := by
  unfold tailWord_4486270
  simp only [CollatzResearch.WordTrace]
  refine ⟨20453463682127182345162033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109085139638011639174197509 20453463682127182345162033)
  ·
    refine ⟨15340097761595386758871525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20453463682127182345162033 15340097761595386758871525)
    ·
      refine ⟨2876268330299135017288411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15340097761595386758871525 2876268330299135017288411)
      ·
        refine ⟨4314402495448702525932617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876268330299135017288411 4314402495448702525932617)
        ·
          refine ⟨3235801871586526894449463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4314402495448702525932617 3235801871586526894449463)
          ·
            refine ⟨4853702807379790341674195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235801871586526894449463 4853702807379790341674195)
            ·
              refine ⟨7280554211069685512511293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4853702807379790341674195 7280554211069685512511293)
              ·
                refine ⟨2730207829151132067191735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7280554211069685512511293 2730207829151132067191735)
                ·
                  refine ⟨4095311743726698100787603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730207829151132067191735 4095311743726698100787603)
                  ·
                    refine ⟨6142967615590047151181405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4095311743726698100787603 6142967615590047151181405)
                    ·
                      refine ⟨2303612855846267681693027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6142967615590047151181405 2303612855846267681693027)
                      ·
                        rfl

theorem cell23_4486270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4486270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486270 prefixEnd_4486270 := by exact prefixLift 4486270
  have htrace : WordTrace (prefixWord ++ tailWord_4486270) baseStart_4486270 baseEnd_4486270 := by
    simpa [prefixWord, tailWord_4486270, baseEnd_4486270] using wordTrace_append hprefix tailTrace_4486270
  have hstable : (prefixWord ++ tailWord_4486270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486270).length < 2 ^ (prefixWord ++ tailWord_4486270).sum := by decide
  have hdescent : baseEnd_4486270 < baseStart_4486270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486301 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4486301 : Nat := 118140960795 + 4486301 * 2 ^ 59
def prefixEnd_4486301 : Nat := 4983230072969 + 3 ^ 40 * 4486301 * 2
def baseEnd_4486301 : Nat := 2303628773746557060405383

theorem tailTrace_4486301 : CollatzResearch.WordTrace tailWord_4486301 prefixEnd_4486301 2303628773746557060405383 := by
  unfold tailWord_4486301
  simp only [CollatzResearch.WordTrace]
  refine ⟨163628840119905151055674757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109085893413270100703783171 163628840119905151055674757)
  ·
    refine ⟨30680407522482215822939017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163628840119905151055674757 30680407522482215822939017)
    ·
      refine ⟨23010305641861661867204263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30680407522482215822939017 23010305641861661867204263)
      ·
        refine ⟨34515458462792492800806395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23010305641861661867204263 34515458462792492800806395)
        ·
          refine ⟨51773187694188739201209593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34515458462792492800806395 51773187694188739201209593)
          ·
            refine ⟨38829890770641554400907195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51773187694188739201209593 38829890770641554400907195)
            ·
              refine ⟨58244836155962331601360793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38829890770641554400907195 58244836155962331601360793)
              ·
                refine ⟨43683627116971748701020595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58244836155962331601360793 43683627116971748701020595)
                ·
                  refine ⟨65525440675457623051530893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43683627116971748701020595 65525440675457623051530893)
                  ·
                    refine ⟨24572040253296608644324085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65525440675457623051530893 24572040253296608644324085)
                    ·
                      refine ⟨2303628773746557060405383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24572040253296608644324085 2303628773746557060405383)
                      ·
                        rfl

theorem cell23_4486301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4486301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486301 prefixEnd_4486301 := by exact prefixLift 4486301
  have htrace : WordTrace (prefixWord ++ tailWord_4486301) baseStart_4486301 baseEnd_4486301 := by
    simpa [prefixWord, tailWord_4486301, baseEnd_4486301] using wordTrace_append hprefix tailTrace_4486301
  have hstable : (prefixWord ++ tailWord_4486301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486301).length < 2 ^ (prefixWord ++ tailWord_4486301).sum := by decide
  have hdescent : baseEnd_4486301 < baseStart_4486301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486331 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 3]
def baseStart_4486331 : Nat := 118140960795 + 4486331 * 2 ^ 59
def prefixEnd_4486331 : Nat := 4983230072969 + 3 ^ 40 * 4486331 * 2
def baseEnd_4486331 : Nat := 2303644178166191943030245

theorem tailTrace_4486331 : CollatzResearch.WordTrace tailWord_4486331 prefixEnd_4486331 2303644178166191943030245 := by
  unfold tailWord_4486331
  simp only [CollatzResearch.WordTrace]
  refine ⟨163629934309796466179266847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109086622873197644119511231 163629934309796466179266847)
  ·
    refine ⟨245444901464694699268900271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163629934309796466179266847 245444901464694699268900271)
    ·
      refine ⟨368167352197042048903350407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245444901464694699268900271 368167352197042048903350407)
      ·
        refine ⟨552251028295563073355025611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368167352197042048903350407 552251028295563073355025611)
        ·
          refine ⟨828376542443344610032538417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552251028295563073355025611 828376542443344610032538417)
          ·
            refine ⟨621282406832508457524403813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828376542443344610032538417 621282406832508457524403813)
            ·
              refine ⟨116490451281095335785825715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 621282406832508457524403813 116490451281095335785825715)
              ·
                refine ⟨174735676921643003678738573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116490451281095335785825715 174735676921643003678738573)
                ·
                  refine ⟨65525878845616126379526965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174735676921643003678738573 65525878845616126379526965)
                  ·
                    refine ⟨6143051141776511848080653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65525878845616126379526965 6143051141776511848080653)
                    ·
                      refine ⟨2303644178166191943030245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6143051141776511848080653 2303644178166191943030245)
                      ·
                        rfl

theorem cell23_4486331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 3].length) (baseStart_4486331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486331 prefixEnd_4486331 := by exact prefixLift 4486331
  have htrace : WordTrace (prefixWord ++ tailWord_4486331) baseStart_4486331 baseEnd_4486331 := by
    simpa [prefixWord, tailWord_4486331, baseEnd_4486331] using wordTrace_append hprefix tailTrace_4486331
  have hstable : (prefixWord ++ tailWord_4486331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486331).length < 2 ^ (prefixWord ++ tailWord_4486331).sum := by decide
  have hdescent : baseEnd_4486331 < baseStart_4486331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486351 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 4, 5]
def baseStart_4486351 : Nat := 118140960795 + 4486351 * 2 ^ 59
def prefixEnd_4486351 : Nat := 4983230072969 + 3 ^ 40 * 4486351 * 2
def baseEnd_4486351 : Nat := 767884815926427288260051

theorem tailTrace_4486351 : CollatzResearch.WordTrace tailWord_4486351 prefixEnd_4486351 767884815926427288260051 := by
  unfold tailWord_4486351
  simp only [CollatzResearch.WordTrace]
  refine ⟨163630663769724009594994907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109087109179816006396663271 163630663769724009594994907)
  ·
    refine ⟨245445995654586014392492361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163630663769724009594994907 245445995654586014392492361)
    ·
      refine ⟨184084496740939510794369271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245445995654586014392492361 184084496740939510794369271)
      ·
        refine ⟨276126745111409266191553907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184084496740939510794369271 276126745111409266191553907)
        ·
          refine ⟨414190117667113899287330861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276126745111409266191553907 414190117667113899287330861)
          ·
            refine ⟨155321294125167712232749073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 414190117667113899287330861 155321294125167712232749073)
            ·
              refine ⟨116490970593875784174561805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155321294125167712232749073 116490970593875784174561805)
              ·
                refine ⟨43684113972703419065460677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116490970593875784174561805 43684113972703419065460677)
                ·
                  refine ⟨8190771369881891074773877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43684113972703419065460677 8190771369881891074773877)
                  ·
                    refine ⟨767884815926427288260051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8190771369881891074773877 767884815926427288260051)
                    ·
                      rfl

theorem cell23_4486351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_4486351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486351 prefixEnd_4486351 := by exact prefixLift 4486351
  have htrace : WordTrace (prefixWord ++ tailWord_4486351) baseStart_4486351 baseEnd_4486351 := by
    simpa [prefixWord, tailWord_4486351, baseEnd_4486351] using wordTrace_append hprefix tailTrace_4486351
  have hstable : (prefixWord ++ tailWord_4486351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486351).length < 2 ^ (prefixWord ++ tailWord_4486351).sum := by decide
  have hdescent : baseEnd_4486351 < baseStart_4486351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486428 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 6]
def baseStart_4486428 : Nat := 118140960795 + 4486428 * 2 ^ 59
def prefixEnd_4486428 : Nat := 4983230072969 + 3 ^ 40 * 4486428 * 2
def baseEnd_4486428 : Nat := 255965998421075340390811

theorem tailTrace_4486428 : CollatzResearch.WordTrace tailWord_4486428 prefixEnd_4486428 255965998421075340390811 := by
  unfold tailWord_4486428
  simp only [CollatzResearch.WordTrace]
  refine ⟨81816736095222525872773969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109088981460296701163698625 81816736095222525872773969)
  ·
    refine ⟨61362552071416894404580477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81816736095222525872773969 61362552071416894404580477)
    ·
      refine ⟨23010957026781335401717679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61362552071416894404580477 23010957026781335401717679)
      ·
        refine ⟨34516435540172003102576519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23010957026781335401717679 34516435540172003102576519)
        ·
          refine ⟨51774653310258004653864779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34516435540172003102576519 51774653310258004653864779)
          ·
            refine ⟨77661979965387006980797169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51774653310258004653864779 77661979965387006980797169)
            ·
              refine ⟨58246484974040255235597877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77661979965387006980797169 58246484974040255235597877)
              ·
                refine ⟨5460607966316273928337301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58246484974040255235597877 5460607966316273928337301)
                ·
                  refine ⟨255965998421075340390811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5460607966316273928337301 255965998421075340390811)
                  ·
                    rfl

theorem cell23_4486428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_4486428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486428 prefixEnd_4486428 := by exact prefixLift 4486428
  have htrace : WordTrace (prefixWord ++ tailWord_4486428) baseStart_4486428 baseEnd_4486428 := by
    simpa [prefixWord, tailWord_4486428, baseEnd_4486428] using wordTrace_append hprefix tailTrace_4486428
  have hstable : (prefixWord ++ tailWord_4486428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486428).length < 2 ^ (prefixWord ++ tailWord_4486428).sum := by decide
  have hdescent : baseEnd_4486428 < baseStart_4486428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486445 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 8]
def baseStart_4486445 : Nat := 118140960795 + 4486445 * 2 ^ 59
def prefixEnd_4486445 : Nat := 4983230072969 + 3 ^ 40 * 4486445 * 2
def baseEnd_4486445 : Nat := 255966968328978277444969

theorem tailTrace_4486445 : CollatzResearch.WordTrace tailWord_4486445 prefixEnd_4486445 255966968328978277444969 := by
  unfold tailWord_4486445
  simp only [CollatzResearch.WordTrace]
  refine ⟨163634092231383463648916789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109089394820922309099277859 163634092231383463648916789)
  ·
    refine ⟨15340696146692199717085949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163634092231383463648916789 15340696146692199717085949)
    ·
      refine ⟨5752761055009574893907231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15340696146692199717085949 5752761055009574893907231)
      ·
        refine ⟨8629141582514362340860847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5752761055009574893907231 8629141582514362340860847)
        ·
          refine ⟨12943712373771543511291271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8629141582514362340860847 12943712373771543511291271)
          ·
            refine ⟨19415568560657315266936907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12943712373771543511291271 19415568560657315266936907)
            ·
              refine ⟨29123352840985972900405361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19415568560657315266936907 29123352840985972900405361)
              ·
                refine ⟨21842514630739479675304021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29123352840985972900405361 21842514630739479675304021)
                ·
                  refine ⟨255966968328978277444969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21842514630739479675304021 255966968328978277444969)
                  ·
                    rfl

theorem cell23_4486445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_4486445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486445 prefixEnd_4486445 := by exact prefixLift 4486445
  have htrace : WordTrace (prefixWord ++ tailWord_4486445) baseStart_4486445 baseEnd_4486445 := by
    simpa [prefixWord, tailWord_4486445, baseEnd_4486445] using wordTrace_append hprefix tailTrace_4486445
  have hstable : (prefixWord ++ tailWord_4486445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486445).length < 2 ^ (prefixWord ++ tailWord_4486445).sum := by decide
  have hdescent : baseEnd_4486445 < baseStart_4486445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486449 : List Nat := [1, 2, 2, 3, 3, 3, 1, 3, 1, 4]
def baseStart_4486449 : Nat := 118140960795 + 4486449 * 2 ^ 59
def prefixEnd_4486449 : Nat := 4983230072969 + 3 ^ 40 * 4486449 * 2
def baseEnd_4486449 : Nat := 767901589627807493784901

theorem tailTrace_4486449 : CollatzResearch.WordTrace tailWord_4486449 prefixEnd_4486449 767901589627807493784901 := by
  unfold tailWord_4486449
  simp only [CollatzResearch.WordTrace]
  refine ⟨163634238123368972332062401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109089492082245981554708267 163634238123368972332062401)
  ·
    refine ⟨122725678592526729249046801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163634238123368972332062401 122725678592526729249046801)
    ·
      refine ⟨92044258944395046936785101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122725678592526729249046801 92044258944395046936785101)
      ·
        refine ⟨34516597104148142601294413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92044258944395046936785101 34516597104148142601294413)
        ·
          refine ⟨12943723914055553475485405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34516597104148142601294413 12943723914055553475485405)
          ·
            refine ⟨4853896467770832553307027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12943723914055553475485405 4853896467770832553307027)
            ·
              refine ⟨7280844701656248829960541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4853896467770832553307027 7280844701656248829960541)
              ·
                refine ⟨2730316763121093311235203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7280844701656248829960541 2730316763121093311235203)
                ·
                  refine ⟨4095475144681639966852805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730316763121093311235203 4095475144681639966852805)
                  ·
                    refine ⟨767901589627807493784901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4095475144681639966852805 767901589627807493784901)
                    ·
                      rfl

theorem cell23_4486449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_4486449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486449 prefixEnd_4486449 := by exact prefixLift 4486449
  have htrace : WordTrace (prefixWord ++ tailWord_4486449) baseStart_4486449 baseEnd_4486449 := by
    simpa [prefixWord, tailWord_4486449, baseEnd_4486449] using wordTrace_append hprefix tailTrace_4486449
  have hstable : (prefixWord ++ tailWord_4486449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486449).length < 2 ^ (prefixWord ++ tailWord_4486449).sum := by decide
  have hdescent : baseEnd_4486449 < baseStart_4486449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486488 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 1, 6]
def baseStart_4486488 : Nat := 118140960795 + 4486488 * 2 ^ 59
def prefixEnd_4486488 : Nat := 4983230072969 + 3 ^ 40 * 4486488 * 2
def baseEnd_4486488 : Nat := 767908264876315942922341

theorem tailTrace_4486488 : CollatzResearch.WordTrace tailWord_4486488 prefixEnd_4486488 767908264876315942922341 := by
  unfold tailWord_4486488
  simp only [CollatzResearch.WordTrace]
  refine ⟨81817830285113840996366059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109090440380151787995154745 81817830285113840996366059)
  ·
    refine ⟨122726745427670761494549089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81817830285113840996366059 122726745427670761494549089)
    ·
      refine ⟨92045059070753071120911817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122726745427670761494549089 92045059070753071120911817)
      ·
        refine ⟨69033794303064803340683863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92045059070753071120911817 69033794303064803340683863)
        ·
          refine ⟨103550691454597205011025795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69033794303064803340683863 103550691454597205011025795)
          ·
            refine ⟨155326037181895807516538693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103550691454597205011025795 155326037181895807516538693)
            ·
              refine ⟨29123631971605463909351005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155326037181895807516538693 29123631971605463909351005)
              ·
                refine ⟨10921361989352048966006627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29123631971605463909351005 10921361989352048966006627)
                ·
                  refine ⟨16382042984028073449009941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10921361989352048966006627 16382042984028073449009941)
                  ·
                    refine ⟨767908264876315942922341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16382042984028073449009941 767908264876315942922341)
                    ·
                      rfl

theorem cell23_4486488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_4486488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486488 prefixEnd_4486488 := by exact prefixLift 4486488
  have htrace : WordTrace (prefixWord ++ tailWord_4486488) baseStart_4486488 baseEnd_4486488 := by
    simpa [prefixWord, tailWord_4486488, baseEnd_4486488] using wordTrace_append hprefix tailTrace_4486488
  have hstable : (prefixWord ++ tailWord_4486488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486488).length < 2 ^ (prefixWord ++ tailWord_4486488).sum := by decide
  have hdescent : baseEnd_4486488 < baseStart_4486488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486512 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 1, 1, 4]
def baseStart_4486512 : Nat := 118140960795 + 4486512 * 2 ^ 59
def prefixEnd_4486512 : Nat := 4983230072969 + 3 ^ 40 * 4486512 * 2
def baseEnd_4486512 : Nat := 2303737118164655734866913

theorem tailTrace_4486512 : CollatzResearch.WordTrace tailWord_4486512 prefixEnd_4486512 2303737118164655734866913 := by
  unfold tailWord_4486512
  simp only [CollatzResearch.WordTrace]
  refine ⟨81818267961070367045802895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109091023948093822727737193 81818267961070367045802895)
  ·
    refine ⟨122727401941605550568704343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81818267961070367045802895 122727401941605550568704343)
    ·
      refine ⟨184091102912408325853056515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122727401941605550568704343 184091102912408325853056515)
      ·
        refine ⟨276136654368612488779584773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184091102912408325853056515 276136654368612488779584773)
        ·
          refine ⟨51775622694114841646172145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276136654368612488779584773 51775622694114841646172145)
          ·
            refine ⟨38831717020586131234629109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51775622694114841646172145 38831717020586131234629109)
            ·
              refine ⟨3640473470679949803246479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38831717020586131234629109 3640473470679949803246479)
              ·
                refine ⟨5460710206019924704869719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3640473470679949803246479 5460710206019924704869719)
                ·
                  refine ⟨8191065309029887057304579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5460710206019924704869719 8191065309029887057304579)
                  ·
                    refine ⟨12286597963544830585956869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8191065309029887057304579 12286597963544830585956869)
                    ·
                      refine ⟨2303737118164655734866913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12286597963544830585956869 2303737118164655734866913)
                      ·
                        rfl

theorem cell23_4486512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 1, 4].length) (baseStart_4486512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486512 prefixEnd_4486512 := by exact prefixLift 4486512
  have htrace : WordTrace (prefixWord ++ tailWord_4486512) baseStart_4486512 baseEnd_4486512 := by
    simpa [prefixWord, tailWord_4486512, baseEnd_4486512] using wordTrace_append hprefix tailTrace_4486512
  have hstable : (prefixWord ++ tailWord_4486512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486512).length < 2 ^ (prefixWord ++ tailWord_4486512).sum := by decide
  have hdescent : baseEnd_4486512 < baseStart_4486512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486518 : List Nat := [5, 1, 1, 16]
def baseStart_4486518 : Nat := 118140960795 + 4486518 * 2 ^ 59
def prefixEnd_4486518 : Nat := 4983230072969 + 3 ^ 40 * 4486518 * 2
def baseEnd_4486518 : Nat := 1053379149084857206855

theorem tailTrace_4486518 : CollatzResearch.WordTrace tailWord_4486518 prefixEnd_4486518 1053379149084857206855 := by
  unfold tailWord_4486518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227297172507437319770263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109091169840079331410882805 10227297172507437319770263)
  ·
    refine ⟨15340945758761155979655395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10227297172507437319770263 15340945758761155979655395)
    ·
      refine ⟨23011418638141733969483093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15340945758761155979655395 23011418638141733969483093)
      ·
        refine ⟨1053379149084857206855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 23011418638141733969483093 1053379149084857206855)
        ·
          rfl

theorem cell23_4486518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 16].length) (baseStart_4486518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486518 prefixEnd_4486518 := by exact prefixLift 4486518
  have htrace : WordTrace (prefixWord ++ tailWord_4486518) baseStart_4486518 baseEnd_4486518 := by
    simpa [prefixWord, tailWord_4486518, baseEnd_4486518] using wordTrace_append hprefix tailTrace_4486518
  have hstable : (prefixWord ++ tailWord_4486518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486518).length < 2 ^ (prefixWord ++ tailWord_4486518).sum := by decide
  have hdescent : baseEnd_4486518 < baseStart_4486518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486535 : List Nat := [1, 1, 4, 2, 2, 4, 1, 8]
def baseStart_4486535 : Nat := 118140960795 + 4486535 * 2 ^ 59
def prefixEnd_4486535 : Nat := 4983230072969 + 3 ^ 40 * 4486535 * 2
def baseEnd_4486535 : Nat := 85324034378507746106641

theorem tailTrace_4486535 : CollatzResearch.WordTrace tailWord_4486535 prefixEnd_4486535 85324034378507746106641 := by
  unfold tailWord_4486535
  simp only [CollatzResearch.WordTrace]
  refine ⟨163637374801057409019693059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109091583200704939346462039 163637374801057409019693059)
  ·
    refine ⟨245456062201586113529539589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163637374801057409019693059 245456062201586113529539589)
    ·
      refine ⟨46023011662797396286788673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245456062201586113529539589 46023011662797396286788673)
      ·
        refine ⟨34517258747098047215091505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46023011662797396286788673 34517258747098047215091505)
        ·
          refine ⟨25887944060323535411318629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34517258747098047215091505 25887944060323535411318629)
          ·
            refine ⟨4853989511310662889622243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25887944060323535411318629 4853989511310662889622243)
            ·
              refine ⟨7280984266965994334433365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4853989511310662889622243 7280984266965994334433365)
              ·
                refine ⟨85324034378507746106641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7280984266965994334433365 85324034378507746106641)
                ·
                  rfl

theorem cell23_4486535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 8].length) (baseStart_4486535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486535 prefixEnd_4486535 := by exact prefixLift 4486535
  have htrace : WordTrace (prefixWord ++ tailWord_4486535) baseStart_4486535 baseEnd_4486535 := by
    simpa [prefixWord, tailWord_4486535, baseEnd_4486535] using wordTrace_append hprefix tailTrace_4486535
  have hstable : (prefixWord ++ tailWord_4486535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486535).length < 2 ^ (prefixWord ++ tailWord_4486535).sum := by decide
  have hdescent : baseEnd_4486535 < baseStart_4486535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486552 : List Nat := [2, 1, 2, 5, 2, 1, 3, 7]
def baseStart_4486552 : Nat := 118140960795 + 4486552 * 2 ^ 59
def prefixEnd_4486552 : Nat := 4983230072969 + 3 ^ 40 * 4486552 * 2
def baseEnd_4486552 : Nat := 85324357681142058458027

theorem tailTrace_4486552 : CollatzResearch.WordTrace tailWord_4486552 prefixEnd_4486552 85324357681142058458027 := by
  unfold tailWord_4486552
  simp only [CollatzResearch.WordTrace]
  refine ⟨81818997420997910461530955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109091996561330547282041273 81818997420997910461530955)
  ·
    refine ⟨122728496131496865692296433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81818997420997910461530955 122728496131496865692296433)
    ·
      refine ⟨92046372098622649269222325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122728496131496865692296433 92046372098622649269222325)
      ·
        refine ⟨8629347384245873368989593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92046372098622649269222325 8629347384245873368989593)
        ·
          refine ⟨6472010538184405026742195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8629347384245873368989593 6472010538184405026742195)
          ·
            refine ⟨9708015807276607540113293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472010538184405026742195 9708015807276607540113293)
            ·
              refine ⟨3640505927728727827542485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9708015807276607540113293 3640505927728727827542485)
              ·
                refine ⟨85324357681142058458027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3640505927728727827542485 85324357681142058458027)
                ·
                  rfl

theorem cell23_4486552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 7].length) (baseStart_4486552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486552 prefixEnd_4486552 := by exact prefixLift 4486552
  have htrace : WordTrace (prefixWord ++ tailWord_4486552) baseStart_4486552 baseEnd_4486552 := by
    simpa [prefixWord, tailWord_4486552, baseEnd_4486552] using wordTrace_append hprefix tailTrace_4486552
  have hstable : (prefixWord ++ tailWord_4486552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486552).length < 2 ^ (prefixWord ++ tailWord_4486552).sum := by decide
  have hdescent : baseEnd_4486552 < baseStart_4486552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486562 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_4486562 : Nat := 118140960795 + 4486562 * 2 ^ 59
def prefixEnd_4486562 : Nat := 4983230072969 + 3 ^ 40 * 4486562 * 2
def baseEnd_4486562 : Nat := 2303762792197380539241683

theorem tailTrace_4486562 : CollatzResearch.WordTrace tailWord_4486562 prefixEnd_4486562 2303762792197380539241683 := by
  unfold tailWord_4486562
  simp only [CollatzResearch.WordTrace]
  refine ⟨40909589892989898157731485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109092239714639728420617293 40909589892989898157731485)
  ·
    refine ⟨15341096209871211809149307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40909589892989898157731485 15341096209871211809149307)
    ·
      refine ⟨23011644314806817713723961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15341096209871211809149307 23011644314806817713723961)
      ·
        refine ⟨17258733236105113285292971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23011644314806817713723961 17258733236105113285292971)
        ·
          refine ⟨25888099854157669927939457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17258733236105113285292971 25888099854157669927939457)
          ·
            refine ⟨19416074890618252445954593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25888099854157669927939457 19416074890618252445954593)
            ·
              refine ⟨14562056167963689334465945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19416074890618252445954593 14562056167963689334465945)
              ·
                refine ⟨10921542125972767000849459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14562056167963689334465945 10921542125972767000849459)
                ·
                  refine ⟨16382313188959150501274189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10921542125972767000849459 16382313188959150501274189)
                  ·
                    refine ⟨6143367445859681437977821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16382313188959150501274189 6143367445859681437977821)
                    ·
                      refine ⟨2303762792197380539241683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6143367445859681437977821 2303762792197380539241683)
                      ·
                        rfl

theorem cell23_4486562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_4486562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486562 prefixEnd_4486562 := by exact prefixLift 4486562
  have htrace : WordTrace (prefixWord ++ tailWord_4486562) baseStart_4486562 baseEnd_4486562 := by
    simpa [prefixWord, tailWord_4486562, baseEnd_4486562] using wordTrace_append hprefix tailTrace_4486562
  have hstable : (prefixWord ++ tailWord_4486562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486562).length < 2 ^ (prefixWord ++ tailWord_4486562).sum := by decide
  have hdescent : baseEnd_4486562 < baseStart_4486562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486635 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 3]
def baseStart_4486635 : Nat := 118140960795 + 4486635 * 2 ^ 59
def prefixEnd_4486635 : Nat := 4983230072969 + 3 ^ 40 * 4486635 * 2
def baseEnd_4486635 : Nat := 2303800276285158753628847

theorem tailTrace_4486635 : CollatzResearch.WordTrace tailWord_4486635 prefixEnd_4486635 2303800276285158753628847 := by
  unfold tailWord_4486635
  simp only [CollatzResearch.WordTrace]
  refine ⟨163641022100695126098333359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109094014733796750732222239 163641022100695126098333359)
  ·
    refine ⟨245461533151042689147500039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163641022100695126098333359 245461533151042689147500039)
    ·
      refine ⟨368192299726564033721250059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245461533151042689147500039 368192299726564033721250059)
      ·
        refine ⟨552288449589846050581875089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368192299726564033721250059 552288449589846050581875089)
        ·
          refine ⟨414216337192384537936406317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552288449589846050581875089 414216337192384537936406317)
          ·
            refine ⟨155331126447144201726152369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 414216337192384537936406317 155331126447144201726152369)
            ·
              refine ⟨116498344835358151294614277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155331126447144201726152369 116498344835358151294614277)
              ·
                refine ⟨21843439656629653367740177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116498344835358151294614277 21843439656629653367740177)
                ·
                  refine ⟨16382579742472240025805133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21843439656629653367740177 16382579742472240025805133)
                  ·
                    refine ⟨6143467403427090009676925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16382579742472240025805133 6143467403427090009676925)
                    ·
                      refine ⟨2303800276285158753628847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6143467403427090009676925 2303800276285158753628847)
                      ·
                        rfl

theorem cell23_4486635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 3].length) (baseStart_4486635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486635 prefixEnd_4486635 := by exact prefixLift 4486635
  have htrace : WordTrace (prefixWord ++ tailWord_4486635) baseStart_4486635 baseEnd_4486635 := by
    simpa [prefixWord, tailWord_4486635, baseEnd_4486635] using wordTrace_append hprefix tailTrace_4486635
  have hstable : (prefixWord ++ tailWord_4486635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486635).length < 2 ^ (prefixWord ++ tailWord_4486635).sum := by decide
  have hdescent : baseEnd_4486635 < baseStart_4486635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486642 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 7]
def baseStart_4486642 : Nat := 118140960795 + 4486642 * 2 ^ 59
def prefixEnd_4486642 : Nat := 4983230072969 + 3 ^ 40 * 4486642 * 2
def baseEnd_4486642 : Nat := 255978207849971136249035

theorem tailTrace_4486642 : CollatzResearch.WordTrace tailWord_4486642 prefixEnd_4486642 255978207849971136249035 := by
  unfold tailWord_4486642
  simp only [CollatzResearch.WordTrace]
  refine ⟨40910319352917441573459545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109094184941113177529225453 40910319352917441573459545)
  ·
    refine ⟨30682739514688081180094659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40910319352917441573459545 30682739514688081180094659)
    ·
      refine ⟨46024109272032121770141989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30682739514688081180094659 46024109272032121770141989)
      ·
        refine ⟨8629520488506022831901623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46024109272032121770141989 8629520488506022831901623)
        ·
          refine ⟨12944280732759034247852435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8629520488506022831901623 12944280732759034247852435)
          ·
            refine ⟨19416421099138551371778653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12944280732759034247852435 19416421099138551371778653)
            ·
              refine ⟨7281157912176956764416995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19416421099138551371778653 7281157912176956764416995)
              ·
                refine ⟨10921736868265435146625493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7281157912176956764416995 10921736868265435146625493)
                ·
                  refine ⟨255978207849971136249035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10921736868265435146625493 255978207849971136249035)
                  ·
                    rfl

theorem cell23_4486642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_4486642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486642 prefixEnd_4486642 := by exact prefixLift 4486642
  have htrace : WordTrace (prefixWord ++ tailWord_4486642) baseStart_4486642 baseEnd_4486642 := by
    simpa [prefixWord, tailWord_4486642, baseEnd_4486642] using wordTrace_append hprefix tailTrace_4486642
  have hstable : (prefixWord ++ tailWord_4486642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486642).length < 2 ^ (prefixWord ++ tailWord_4486642).sum := by decide
  have hdescent : baseEnd_4486642 < baseStart_4486642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486653 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_4486653 : Nat := 118140960795 + 4486653 * 2 ^ 59
def prefixEnd_4486653 : Nat := 4983230072969 + 3 ^ 40 * 4486653 * 2
def baseEnd_4486653 : Nat := 2303809518936939683203765

theorem tailTrace_4486653 : CollatzResearch.WordTrace tailWord_4486653 prefixEnd_4486653 2303809518936939683203765 := by
  unfold tailWord_4486653
  simp only [CollatzResearch.WordTrace]
  refine ⟨163641678614629915172488613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109094452409753276781659075 163641678614629915172488613)
  ·
    refine ⟨30682814740243109094841615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163641678614629915172488613 30682814740243109094841615)
    ·
      refine ⟨46024222110364663642262423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30682814740243109094841615 46024222110364663642262423)
      ·
        refine ⟨69036333165546995463393635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46024222110364663642262423 69036333165546995463393635)
        ·
          refine ⟨103554499748320493195090453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69036333165546995463393635 103554499748320493195090453)
          ·
            refine ⟨4854117175702523118519865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103554499748320493195090453 4854117175702523118519865)
            ·
              refine ⟨3640587881776892338889899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4854117175702523118519865 3640587881776892338889899)
              ·
                refine ⟨5460881822665338508334849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3640587881776892338889899 5460881822665338508334849)
                ·
                  refine ⟨4095661366999003881251137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5460881822665338508334849 4095661366999003881251137)
                  ·
                    refine ⟨3071746025249252910938353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095661366999003881251137 3071746025249252910938353)
                    ·
                      refine ⟨2303809518936939683203765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071746025249252910938353 2303809518936939683203765)
                      ·
                        rfl

theorem cell23_4486653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_4486653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486653 prefixEnd_4486653 := by exact prefixLift 4486653
  have htrace : WordTrace (prefixWord ++ tailWord_4486653) baseStart_4486653 baseEnd_4486653 := by
    simpa [prefixWord, tailWord_4486653, baseEnd_4486653] using wordTrace_append hprefix tailTrace_4486653
  have hstable : (prefixWord ++ tailWord_4486653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486653).length < 2 ^ (prefixWord ++ tailWord_4486653).sum := by decide
  have hdescent : baseEnd_4486653 < baseStart_4486653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486705 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_4486705 : Nat := 118140960795 + 4486705 * 2 ^ 59
def prefixEnd_4486705 : Nat := 4983230072969 + 3 ^ 40 * 4486705 * 2
def baseEnd_4486705 : Nat := 2303836219930973479753525

theorem tailTrace_4486705 : CollatzResearch.WordTrace tailWord_4486705 prefixEnd_4486705 2303836219930973479753525 := by
  unfold tailWord_4486705
  simp only [CollatzResearch.WordTrace]
  refine ⟨163643575210441528053381569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109095716806961018702254379 163643575210441528053381569)
  ·
    refine ⟨122732681407831146040036177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163643575210441528053381569 122732681407831146040036177)
    ·
      refine ⟨92049511055873359530027133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122732681407831146040036177 92049511055873359530027133)
      ·
        refine ⟨34518566645952509823760175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92049511055873359530027133 34518566645952509823760175)
        ·
          refine ⟨51777849968928764735640263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34518566645952509823760175 51777849968928764735640263)
          ·
            refine ⟨77666774953393147103460395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51777849968928764735640263 77666774953393147103460395)
            ·
              refine ⟨116500162430089720655190593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77666774953393147103460395 116500162430089720655190593)
              ·
                refine ⟨87375121822567290491392945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116500162430089720655190593 87375121822567290491392945)
                ·
                  refine ⟨65531341366925467868544709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87375121822567290491392945 65531341366925467868544709)
                  ·
                    refine ⟨12287126506298525225352133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65531341366925467868544709 12287126506298525225352133)
                    ·
                      refine ⟨2303836219930973479753525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12287126506298525225352133 2303836219930973479753525)
                      ·
                        rfl

theorem cell23_4486705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_4486705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486705 prefixEnd_4486705 := by exact prefixLift 4486705
  have htrace : WordTrace (prefixWord ++ tailWord_4486705) baseStart_4486705 baseEnd_4486705 := by
    simpa [prefixWord, tailWord_4486705, baseEnd_4486705] using wordTrace_append hprefix tailTrace_4486705
  have hstable : (prefixWord ++ tailWord_4486705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486705).length < 2 ^ (prefixWord ++ tailWord_4486705).sum := by decide
  have hdescent : baseEnd_4486705 < baseStart_4486705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486709 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_4486709 : Nat := 118140960795 + 4486709 * 2 ^ 59
def prefixEnd_4486709 : Nat := 4983230072969 + 3 ^ 40 * 4486709 * 2
def baseEnd_4486709 : Nat := 2303838273853591464103507

theorem tailTrace_4486709 : CollatzResearch.WordTrace tailWord_4486709 prefixEnd_4486709 2303838273853591464103507 := by
  unfold tailWord_4486709
  simp only [CollatzResearch.WordTrace]
  refine ⟨163643721102427036736527181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109095814068284691157684787 163643721102427036736527181)
  ·
    refine ⟨61366395413410138776197693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163643721102427036736527181 61366395413410138776197693)
    ·
      refine ⟨23012398280028802041074135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61366395413410138776197693 23012398280028802041074135)
      ·
        refine ⟨34518597420043203061611203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23012398280028802041074135 34518597420043203061611203)
        ·
          refine ⟨51777896130064804592416805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34518597420043203061611203 51777896130064804592416805)
          ·
            refine ⟨9708355524387150861078151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51777896130064804592416805 9708355524387150861078151)
            ·
              refine ⟨14562533286580726291617227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9708355524387150861078151 14562533286580726291617227)
              ·
                refine ⟨21843799929871089437425841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14562533286580726291617227 21843799929871089437425841)
                ·
                  refine ⟨16382849947403317078069381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21843799929871089437425841 16382849947403317078069381)
                  ·
                    refine ⟨3071784365138121952138009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16382849947403317078069381 3071784365138121952138009)
                    ·
                      refine ⟨2303838273853591464103507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071784365138121952138009 2303838273853591464103507)
                      ·
                        rfl

theorem cell23_4486709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_4486709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486709 prefixEnd_4486709 := by exact prefixLift 4486709
  have htrace : WordTrace (prefixWord ++ tailWord_4486709) baseStart_4486709 baseEnd_4486709 := by
    simpa [prefixWord, tailWord_4486709, baseEnd_4486709] using wordTrace_append hprefix tailTrace_4486709
  have hstable : (prefixWord ++ tailWord_4486709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486709).length < 2 ^ (prefixWord ++ tailWord_4486709).sum := by decide
  have hdescent : baseEnd_4486709 < baseStart_4486709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486726 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4486726 : Nat := 118140960795 + 4486726 * 2 ^ 59
def prefixEnd_4486726 : Nat := 4983230072969 + 3 ^ 40 * 4486726 * 2
def baseEnd_4486726 : Nat := 2303847003024717897590929

theorem tailTrace_4486726 : CollatzResearch.WordTrace tailWord_4486726 prefixEnd_4486726 2303847003024717897590929 := by
  unfold tailWord_4486726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5113885660730170269996751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109096227428910299093264021 5113885660730170269996751)
  ·
    refine ⟨7670828491095255404995127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5113885660730170269996751 7670828491095255404995127)
    ·
      refine ⟨11506242736642883107492691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7670828491095255404995127 11506242736642883107492691)
      ·
        refine ⟨17259364104964324661239037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11506242736642883107492691 17259364104964324661239037)
        ·
          refine ⟨6472261539361621747964639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17259364104964324661239037 6472261539361621747964639)
          ·
            refine ⟨9708392309042432621946959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472261539361621747964639 9708392309042432621946959)
            ·
              refine ⟨14562588463563648932920439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9708392309042432621946959 14562588463563648932920439)
              ·
                refine ⟨21843882695345473399380659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14562588463563648932920439 21843882695345473399380659)
                ·
                  refine ⟨32765824043018210099070989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21843882695345473399380659 32765824043018210099070989)
                  ·
                    refine ⟨12287184016131828787151621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32765824043018210099070989 12287184016131828787151621)
                    ·
                      refine ⟨2303847003024717897590929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12287184016131828787151621 2303847003024717897590929)
                      ·
                        rfl

theorem cell23_4486726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4486726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486726 prefixEnd_4486726 := by exact prefixLift 4486726
  have htrace : WordTrace (prefixWord ++ tailWord_4486726) baseStart_4486726 baseEnd_4486726 := by
    simpa [prefixWord, tailWord_4486726, baseEnd_4486726] using wordTrace_append hprefix tailTrace_4486726
  have hstable : (prefixWord ++ tailWord_4486726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486726).length < 2 ^ (prefixWord ++ tailWord_4486726).sum := by decide
  have hdescent : baseEnd_4486726 < baseStart_4486726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486759 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_4486759 : Nat := 118140960795 + 4486759 * 2 ^ 59
def prefixEnd_4486759 : Nat := 4983230072969 + 3 ^ 40 * 4486759 * 2
def baseEnd_4486759 : Nat := 2303863947886316268478277

theorem tailTrace_4486759 : CollatzResearch.WordTrace tailWord_4486759 prefixEnd_4486759 2303863947886316268478277 := by
  unfold tailWord_4486759
  simp only [CollatzResearch.WordTrace]
  refine ⟨163645544752245895275847331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109097029834830596850564887 163645544752245895275847331)
  ·
    refine ⟨245468317128368842913770997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163645544752245895275847331 245468317128368842913770997)
    ·
      refine ⟨23012654730784579023166031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245468317128368842913770997 23012654730784579023166031)
      ·
        refine ⟨34518982096176868534749047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23012654730784579023166031 34518982096176868534749047)
        ·
          refine ⟨51778473144265302802123571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34518982096176868534749047 51778473144265302802123571)
          ·
            refine ⟨77667709716397954203185357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51778473144265302802123571 77667709716397954203185357)
            ·
              refine ⟨29125391143649232826194509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77667709716397954203185357 29125391143649232826194509)
              ·
                refine ⟨10922021678868462309822941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29125391143649232826194509 10922021678868462309822941)
                ·
                  refine ⟨4095758129575673366183603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10922021678868462309822941 4095758129575673366183603)
                  ·
                    refine ⟨6143637194363510049275405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4095758129575673366183603 6143637194363510049275405)
                    ·
                      refine ⟨2303863947886316268478277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6143637194363510049275405 2303863947886316268478277)
                      ·
                        rfl

theorem cell23_4486759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_4486759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486759 prefixEnd_4486759 := by exact prefixLift 4486759
  have htrace : WordTrace (prefixWord ++ tailWord_4486759) baseStart_4486759 baseEnd_4486759 := by
    simpa [prefixWord, tailWord_4486759, baseEnd_4486759] using wordTrace_append hprefix tailTrace_4486759
  have hstable : (prefixWord ++ tailWord_4486759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486759).length < 2 ^ (prefixWord ++ tailWord_4486759).sum := by decide
  have hdescent : baseEnd_4486759 < baseStart_4486759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486766 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_4486766 : Nat := 118140960795 + 4486766 * 2 ^ 59
def prefixEnd_4486766 : Nat := 4983230072969 + 3 ^ 40 * 4486766 * 2
def baseEnd_4486766 : Nat := 255985282472321971232305

theorem tailTrace_4486766 : CollatzResearch.WordTrace tailWord_4486766 prefixEnd_4486766 255985282472321971232305 := by
  unfold tailWord_4486766
  simp only [CollatzResearch.WordTrace]
  refine ⟨20455725007902566933919019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109097200042147023647568101 20455725007902566933919019)
  ·
    refine ⟨30683587511853850400878529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20455725007902566933919019 30683587511853850400878529)
    ·
      refine ⟨23012690633890387800658897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30683587511853850400878529 23012690633890387800658897)
      ·
        refine ⟨17259517975417790850494173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23012690633890387800658897 17259517975417790850494173)
        ·
          refine ⟨6472319240781671568935315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17259517975417790850494173 6472319240781671568935315)
          ·
            refine ⟨9708478861172507353402973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472319240781671568935315 9708478861172507353402973)
            ·
              refine ⟨3640679572939690257526115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9708478861172507353402973 3640679572939690257526115)
              ·
                refine ⟨5461019359409535386289173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3640679572939690257526115 5461019359409535386289173)
                ·
                  refine ⟨255985282472321971232305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5461019359409535386289173 255985282472321971232305)
                  ·
                    rfl

theorem cell23_4486766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_4486766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486766 prefixEnd_4486766 := by exact prefixLift 4486766
  have htrace : WordTrace (prefixWord ++ tailWord_4486766) baseStart_4486766 baseEnd_4486766 := by
    simpa [prefixWord, tailWord_4486766, baseEnd_4486766] using wordTrace_append hprefix tailTrace_4486766
  have hstable : (prefixWord ++ tailWord_4486766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486766).length < 2 ^ (prefixWord ++ tailWord_4486766).sum := by decide
  have hdescent : baseEnd_4486766 < baseStart_4486766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486829 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4486829 : Nat := 118140960795 + 4486829 * 2 ^ 59
def prefixEnd_4486829 : Nat := 4983230072969 + 3 ^ 40 * 4486829 * 2
def baseEnd_4486829 : Nat := 2303899891532130994602955

theorem tailTrace_4486829 : CollatzResearch.WordTrace tailWord_4486829 prefixEnd_4486829 2303899891532130994602955 := by
  unfold tailWord_4486829
  simp only [CollatzResearch.WordTrace]
  refine ⟨163648097861992297230895541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109098731907994864820597027 163648097861992297230895541)
  ·
    refine ⟨15342009174561777865396457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163648097861992297230895541 15342009174561777865396457)
    ·
      refine ⟨11506506880921333399047343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15342009174561777865396457 11506506880921333399047343)
      ·
        refine ⟨17259760321382000098571015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11506506880921333399047343 17259760321382000098571015)
        ·
          refine ⟨25889640482073000147856523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17259760321382000098571015 25889640482073000147856523)
          ·
            refine ⟨38834460723109500221784785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25889640482073000147856523 38834460723109500221784785)
            ·
              refine ⟨29125845542332125166338589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38834460723109500221784785 29125845542332125166338589)
              ·
                refine ⟨10922192078374546937376971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29125845542332125166338589 10922192078374546937376971)
                ·
                  refine ⟨16383288117561820406065457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10922192078374546937376971 16383288117561820406065457)
                  ·
                    refine ⟨12287466088171365304549093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16383288117561820406065457 12287466088171365304549093)
                    ·
                      refine ⟨2303899891532130994602955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12287466088171365304549093 2303899891532130994602955)
                      ·
                        rfl

theorem cell23_4486829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4486829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486829 prefixEnd_4486829 := by exact prefixLift 4486829
  have htrace : WordTrace (prefixWord ++ tailWord_4486829) baseStart_4486829 baseEnd_4486829 := by
    simpa [prefixWord, tailWord_4486829, baseEnd_4486829] using wordTrace_append hprefix tailTrace_4486829
  have hstable : (prefixWord ++ tailWord_4486829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486829).length < 2 ^ (prefixWord ++ tailWord_4486829).sum := by decide
  have hdescent : baseEnd_4486829 < baseStart_4486829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486830 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4486830 : Nat := 118140960795 + 4486830 * 2 ^ 59
def prefixEnd_4486830 : Nat := 4983230072969 + 3 ^ 40 * 4486830 * 2
def baseEnd_4486830 : Nat := 767966801670928496896817

theorem tailTrace_4486830 : CollatzResearch.WordTrace tailWord_4486830 prefixEnd_4486830 767966801670928496896817 := by
  unfold tailWord_4486830
  simp only [CollatzResearch.WordTrace]
  refine ⟨20456016791873584300210243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109098756223325782934454629 20456016791873584300210243)
  ·
    refine ⟨30684025187810376450315365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20456016791873584300210243 30684025187810376450315365)
    ·
      refine ⟨5753254722714445584434131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30684025187810376450315365 5753254722714445584434131)
      ·
        refine ⟨8629882084071668376651197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5753254722714445584434131 8629882084071668376651197)
        ·
          refine ⟨3236205781526875641244199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8629882084071668376651197 3236205781526875641244199)
          ·
            refine ⟨4854308672290313461866299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236205781526875641244199 4854308672290313461866299)
            ·
              refine ⟨7281463008435470192799449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854308672290313461866299 7281463008435470192799449)
              ·
                refine ⟨5461097256326602644599587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7281463008435470192799449 5461097256326602644599587)
                ·
                  refine ⟨8191645884489903966899381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5461097256326602644599587 8191645884489903966899381)
                  ·
                    refine ⟨767966801670928496896817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8191645884489903966899381 767966801670928496896817)
                    ·
                      rfl

theorem cell23_4486830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4486830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486830 prefixEnd_4486830 := by exact prefixLift 4486830
  have htrace : WordTrace (prefixWord ++ tailWord_4486830) baseStart_4486830 baseEnd_4486830 := by
    simpa [prefixWord, tailWord_4486830, baseEnd_4486830] using wordTrace_append hprefix tailTrace_4486830
  have hstable : (prefixWord ++ tailWord_4486830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486830).length < 2 ^ (prefixWord ++ tailWord_4486830).sum := by decide
  have hdescent : baseEnd_4486830 < baseStart_4486830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486872 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_4486872 : Nat := 118140960795 + 4486872 * 2 ^ 59
def prefixEnd_4486872 : Nat := 4983230072969 + 3 ^ 40 * 4486872 * 2
def baseEnd_4486872 : Nat := 2303921971200274326365257

theorem tailTrace_4486872 : CollatzResearch.WordTrace tailWord_4486872 prefixEnd_4486872 2303921971200274326365257 := by
  unfold tailWord_4486872
  simp only [CollatzResearch.WordTrace]
  refine ⟨81824833100418257787355435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109099777467224343716473913 81824833100418257787355435)
  ·
    refine ⟨122737249650627386681033153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81824833100418257787355435 122737249650627386681033153)
    ·
      refine ⟨92052937237970540010774865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122737249650627386681033153 92052937237970540010774865)
      ·
        refine ⟨69039702928477905008081149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92052937237970540010774865 69039702928477905008081149)
        ·
          refine ⟨25889888598179214378030431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69039702928477905008081149 25889888598179214378030431)
          ·
            refine ⟨38834832897268821567045647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25889888598179214378030431 38834832897268821567045647)
            ·
              refine ⟨58252249345903232350568471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38834832897268821567045647 58252249345903232350568471)
              ·
                refine ⟨87378374018854848525852707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58252249345903232350568471 87378374018854848525852707)
                ·
                  refine ⟨131067561028282272788779061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87378374018854848525852707 131067561028282272788779061)
                  ·
                    refine ⟨12287583846401463073948037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131067561028282272788779061 12287583846401463073948037)
                    ·
                      refine ⟨2303921971200274326365257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12287583846401463073948037 2303921971200274326365257)
                      ·
                        rfl

theorem cell23_4486872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_4486872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486872 prefixEnd_4486872 := by exact prefixLift 4486872
  have htrace : WordTrace (prefixWord ++ tailWord_4486872) baseStart_4486872 baseEnd_4486872 := by
    simpa [prefixWord, tailWord_4486872, baseEnd_4486872] using wordTrace_append hprefix tailTrace_4486872
  have hstable : (prefixWord ++ tailWord_4486872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486872).length < 2 ^ (prefixWord ++ tailWord_4486872).sum := by decide
  have hdescent : baseEnd_4486872 < baseStart_4486872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486892 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_4486892 : Nat := 118140960795 + 4486892 * 2 ^ 59
def prefixEnd_4486892 : Nat := 4983230072969 + 3 ^ 40 * 4486892 * 2
def baseEnd_4486892 : Nat := 2303932240813364248115165

theorem tailTrace_4486892 : CollatzResearch.WordTrace tailWord_4486892 prefixEnd_4486892 2303932240813364248115165 := by
  unfold tailWord_4486892
  simp only [CollatzResearch.WordTrace]
  refine ⟨81825197830382029495219465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109100263773842705993625953 81825197830382029495219465)
  ·
    refine ⟨61368898372786522121414599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81825197830382029495219465 61368898372786522121414599)
    ·
      refine ⟨92053347559179783182121899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61368898372786522121414599 92053347559179783182121899)
      ·
        refine ⟨138080021338769674773182849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92053347559179783182121899 138080021338769674773182849)
        ·
          refine ⟨103560016004077256079887137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138080021338769674773182849 103560016004077256079887137)
          ·
            refine ⟨77670012003057942059915353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103560016004077256079887137 77670012003057942059915353)
            ·
              refine ⟨58252509002293456544936515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77670012003057942059915353 58252509002293456544936515)
              ·
                refine ⟨87378763503440184817404773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58252509002293456544936515 87378763503440184817404773)
                ·
                  refine ⟨16383518156895034653263395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87378763503440184817404773 16383518156895034653263395)
                  ·
                    refine ⟨24575277235342551979895093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16383518156895034653263395 24575277235342551979895093)
                    ·
                      refine ⟨2303932240813364248115165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24575277235342551979895093 2303932240813364248115165)
                      ·
                        rfl

theorem cell23_4486892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_4486892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486892 prefixEnd_4486892 := by exact prefixLift 4486892
  have htrace : WordTrace (prefixWord ++ tailWord_4486892) baseStart_4486892 baseEnd_4486892 := by
    simpa [prefixWord, tailWord_4486892, baseEnd_4486892] using wordTrace_append hprefix tailTrace_4486892
  have hstable : (prefixWord ++ tailWord_4486892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486892).length < 2 ^ (prefixWord ++ tailWord_4486892).sum := by decide
  have hdescent : baseEnd_4486892 < baseStart_4486892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486906 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2]
def baseStart_4486906 : Nat := 118140960795 + 4486906 * 2 ^ 59
def prefixEnd_4486906 : Nat := 4983230072969 + 3 ^ 40 * 4486906 * 2
def baseEnd_4486906 : Nat := 2303939429542527193340101

theorem tailTrace_4486906 : CollatzResearch.WordTrace tailWord_4486906 prefixEnd_4486906 2303939429542527193340101 := by
  unfold tailWord_4486906
  simp only [CollatzResearch.WordTrace]
  refine ⟨40912726570678334845362143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109100604188475559587632381 40912726570678334845362143)
  ·
    refine ⟨61369089856017502268043215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40912726570678334845362143 61369089856017502268043215)
    ·
      refine ⟨92053634784026253402064823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61369089856017502268043215 92053634784026253402064823)
      ·
        refine ⟨138080452176039380103097235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92053634784026253402064823 138080452176039380103097235)
        ·
          refine ⟨207120678264059070154645853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138080452176039380103097235 207120678264059070154645853)
          ·
            refine ⟨77670254349022151307992195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207120678264059070154645853 77670254349022151307992195)
            ·
              refine ⟨116505381523533226961988293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77670254349022151307992195 116505381523533226961988293)
              ·
                refine ⟨21844759035662480055372805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116505381523533226961988293 21844759035662480055372805)
                ·
                  refine ⟨4095892319186715010382401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21844759035662480055372805 4095892319186715010382401)
                  ·
                    refine ⟨3071919239390036257786801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095892319186715010382401 3071919239390036257786801)
                    ·
                      refine ⟨2303939429542527193340101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071919239390036257786801 2303939429542527193340101)
                      ·
                        rfl

theorem cell23_4486906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_4486906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486906 prefixEnd_4486906 := by exact prefixLift 4486906
  have htrace : WordTrace (prefixWord ++ tailWord_4486906) baseStart_4486906 baseEnd_4486906 := by
    simpa [prefixWord, tailWord_4486906, baseEnd_4486906] using wordTrace_append hprefix tailTrace_4486906
  have hstable : (prefixWord ++ tailWord_4486906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486906).length < 2 ^ (prefixWord ++ tailWord_4486906).sum := by decide
  have hdescent : baseEnd_4486906 < baseStart_4486906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486910 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_4486910 : Nat := 118140960795 + 4486910 * 2 ^ 59
def prefixEnd_4486910 : Nat := 4983230072969 + 3 ^ 40 * 4486910 * 2
def baseEnd_4486910 : Nat := 2303941483465145177690083

theorem tailTrace_4486910 : CollatzResearch.WordTrace tailWord_4486910 prefixEnd_4486910 2303941483465145177690083 := by
  unfold tailWord_4486910
  simp only [CollatzResearch.WordTrace]
  refine ⟨20456381521837356008074273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109100701449799232043062789 20456381521837356008074273)
  ·
    refine ⟨15342286141378017006055705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20456381521837356008074273 15342286141378017006055705)
    ·
      refine ⟨11506714606033512754541779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15342286141378017006055705 11506714606033512754541779)
      ·
        refine ⟨17260071909050269131812669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11506714606033512754541779 17260071909050269131812669)
        ·
          refine ⟨6472526965893850924429751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17260071909050269131812669 6472526965893850924429751)
          ·
            refine ⟨9708790448840776386644627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472526965893850924429751 9708790448840776386644627)
            ·
              refine ⟨14563185673261164579966941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9708790448840776386644627 14563185673261164579966941)
              ·
                refine ⟨5461194627472936717487603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14563185673261164579966941 5461194627472936717487603)
                ·
                  refine ⟨8191791941209405076231405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5461194627472936717487603 8191791941209405076231405)
                  ·
                    refine ⟨3071921977953526903586777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8191791941209405076231405 3071921977953526903586777)
                    ·
                      refine ⟨2303941483465145177690083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071921977953526903586777 2303941483465145177690083)
                      ·
                        rfl

theorem cell23_4486910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_4486910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486910 prefixEnd_4486910 := by exact prefixLift 4486910
  have htrace : WordTrace (prefixWord ++ tailWord_4486910) baseStart_4486910 baseEnd_4486910 := by
    simpa [prefixWord, tailWord_4486910, baseEnd_4486910] using wordTrace_append hprefix tailTrace_4486910
  have hstable : (prefixWord ++ tailWord_4486910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486910).length < 2 ^ (prefixWord ++ tailWord_4486910).sum := by decide
  have hdescent : baseEnd_4486910 < baseStart_4486910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486923 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 2, 2, 2]
def baseStart_4486923 : Nat := 118140960795 + 4486923 * 2 ^ 59
def prefixEnd_4486923 : Nat := 4983230072969 + 3 ^ 40 * 4486923 * 2
def baseEnd_4486923 : Nat := 2303948158713653626827523

theorem tailTrace_4486923 : CollatzResearch.WordTrace tailWord_4486923 prefixEnd_4486923 2303948158713653626827523 := by
  unfold tailWord_4486923
  simp only [CollatzResearch.WordTrace]
  refine ⟨163651526323651751284817423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109101017549101167523211615 163651526323651751284817423)
  ·
    refine ⟨245477289485477626927226135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163651526323651751284817423 245477289485477626927226135)
    ·
      refine ⟨368215934228216440390839203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245477289485477626927226135 368215934228216440390839203)
      ·
        refine ⟨552323901342324660586258805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368215934228216440390839203 552323901342324660586258805)
        ·
          refine ⟨51780365750842936929961763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 552323901342324660586258805 51780365750842936929961763)
          ·
            refine ⟨77670548626264405394942645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51780365750842936929961763 77670548626264405394942645)
            ·
              refine ⟨7281613933712288005775873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77670548626264405394942645 7281613933712288005775873)
              ·
                refine ⟨5461210450284216004331905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7281613933712288005775873 5461210450284216004331905)
                ·
                  refine ⟨4095907837713162003248929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5461210450284216004331905 4095907837713162003248929)
                  ·
                    refine ⟨3071930878284871502436697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095907837713162003248929 3071930878284871502436697)
                    ·
                      refine ⟨2303948158713653626827523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071930878284871502436697 2303948158713653626827523)
                      ·
                        rfl

theorem cell23_4486923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 2, 2].length) (baseStart_4486923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486923 prefixEnd_4486923 := by exact prefixLift 4486923
  have htrace : WordTrace (prefixWord ++ tailWord_4486923) baseStart_4486923 baseEnd_4486923 := by
    simpa [prefixWord, tailWord_4486923, baseEnd_4486923] using wordTrace_append hprefix tailTrace_4486923
  have hstable : (prefixWord ++ tailWord_4486923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486923).length < 2 ^ (prefixWord ++ tailWord_4486923).sum := by decide
  have hdescent : baseEnd_4486923 < baseStart_4486923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486940 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_4486940 : Nat := 118140960795 + 4486940 * 2 ^ 59
def prefixEnd_4486940 : Nat := 4983230072969 + 3 ^ 40 * 4486940 * 2
def baseEnd_4486940 : Nat := 2303956887884780060314945

theorem tailTrace_4486940 : CollatzResearch.WordTrace tailWord_4486940 prefixEnd_4486940 2303956887884780060314945 := by
  unfold tailWord_4486940
  simp only [CollatzResearch.WordTrace]
  refine ⟨81826073182295081594093137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109101430909726775458790849 81826073182295081594093137)
  ·
    refine ⟨61369554886721311195569853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81826073182295081594093137 61369554886721311195569853)
    ·
      refine ⟨23013583082520491698338695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61369554886721311195569853 23013583082520491698338695)
      ·
        refine ⟨34520374623780737547508043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23013583082520491698338695 34520374623780737547508043)
        ·
          refine ⟨51780561935671106321262065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34520374623780737547508043 51780561935671106321262065)
          ·
            refine ⟨38835421451753329740946549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51780561935671106321262065 38835421451753329740946549)
            ·
              refine ⟨3640820761101874663213739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38835421451753329740946549 3640820761101874663213739)
              ·
                refine ⟨5461231141652811994820609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3640820761101874663213739 5461231141652811994820609)
                ·
                  refine ⟨4095923356239608996115457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5461231141652811994820609 4095923356239608996115457)
                  ·
                    refine ⟨3071942517179706747086593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095923356239608996115457 3071942517179706747086593)
                    ·
                      refine ⟨2303956887884780060314945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3071942517179706747086593 2303956887884780060314945)
                      ·
                        rfl

theorem cell23_4486940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_4486940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486940 prefixEnd_4486940 := by exact prefixLift 4486940
  have htrace : WordTrace (prefixWord ++ tailWord_4486940) baseStart_4486940 baseEnd_4486940 := by
    simpa [prefixWord, tailWord_4486940, baseEnd_4486940] using wordTrace_append hprefix tailTrace_4486940
  have hstable : (prefixWord ++ tailWord_4486940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486940).length < 2 ^ (prefixWord ++ tailWord_4486940).sum := by decide
  have hdescent : baseEnd_4486940 < baseStart_4486940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486963 : List Nat := [1, 1, 1, 2, 7, 2, 1, 3, 5]
def baseStart_4486963 : Nat := 118140960795 + 4486963 * 2 ^ 59
def prefixEnd_4486963 : Nat := 4983230072969 + 3 ^ 40 * 4486963 * 2
def baseEnd_4486963 : Nat := 255996521993314830036371

theorem tailTrace_4486963 : CollatzResearch.WordTrace tailWord_4486963 prefixEnd_4486963 255996521993314830036371 := by
  unfold tailWord_4486963
  simp only [CollatzResearch.WordTrace]
  refine ⟨163652985243506838116273543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109101990162337892077515695 163652985243506838116273543)
  ·
    refine ⟨245479477865260257174410315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163652985243506838116273543 245479477865260257174410315)
    ·
      refine ⟨368219216797890385761615473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245479477865260257174410315 368219216797890385761615473)
      ·
        refine ⟨276164412598417789321211605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368219216797890385761615473 276164412598417789321211605)
        ·
          refine ⟨6472603420275416937215897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 276164412598417789321211605 6472603420275416937215897)
          ·
            refine ⟨4854452565206562702911923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6472603420275416937215897 4854452565206562702911923)
            ·
              refine ⟨7281678847809844054367885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854452565206562702911923 7281678847809844054367885)
              ·
                refine ⟨2730629567928691520387957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7281678847809844054367885 2730629567928691520387957)
                ·
                  refine ⟨255996521993314830036371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2730629567928691520387957 255996521993314830036371)
                  ·
                    rfl

theorem cell23_4486963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 5].length) (baseStart_4486963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486963 prefixEnd_4486963 := by exact prefixLift 4486963
  have htrace : WordTrace (prefixWord ++ tailWord_4486963) baseStart_4486963 baseEnd_4486963 := by
    simpa [prefixWord, tailWord_4486963, baseEnd_4486963] using wordTrace_append hprefix tailTrace_4486963
  have hstable : (prefixWord ++ tailWord_4486963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486963).length < 2 ^ (prefixWord ++ tailWord_4486963).sum := by decide
  have hdescent : baseEnd_4486963 < baseStart_4486963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4486979 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 4]
def baseStart_4486979 : Nat := 118140960795 + 4486979 * 2 ^ 59
def prefixEnd_4486979 : Nat := 4983230072969 + 3 ^ 40 * 4486979 * 2
def baseEnd_4486979 : Nat := 2303976913630305407727265

theorem tailTrace_4486979 : CollatzResearch.WordTrace tailWord_4486979 prefixEnd_4486979 2303976913630305407727265 := by
  unfold tailWord_4486979
  simp only [CollatzResearch.WordTrace]
  refine ⟨163653568811448872848855991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109102379207632581899237327 163653568811448872848855991)
  ·
    refine ⟨245480353217173309273283987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163653568811448872848855991 245480353217173309273283987)
    ·
      refine ⟨368220529825759963909925981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245480353217173309273283987 368220529825759963909925981)
      ·
        refine ⟨138082698684659986466222243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368220529825759963909925981 138082698684659986466222243)
        ·
          refine ⟨207124048026989979699333365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138082698684659986466222243 207124048026989979699333365)
          ·
            refine ⟨19417879502530310596812503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207124048026989979699333365 19417879502530310596812503)
            ·
              refine ⟨29126819253795465895218755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19417879502530310596812503 29126819253795465895218755)
              ·
                refine ⟨43690228880693198842828133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29126819253795465895218755 43690228880693198842828133)
                ·
                  refine ⟨8191917915129974783030275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43690228880693198842828133 8191917915129974783030275)
                  ·
                    refine ⟨12287876872694962174545413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8191917915129974783030275 12287876872694962174545413)
                    ·
                      refine ⟨2303976913630305407727265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12287876872694962174545413 2303976913630305407727265)
                      ·
                        rfl

theorem cell23_4486979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_4486979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4486979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4486979 prefixEnd_4486979 := by exact prefixLift 4486979
  have htrace : WordTrace (prefixWord ++ tailWord_4486979) baseStart_4486979 baseEnd_4486979 := by
    simpa [prefixWord, tailWord_4486979, baseEnd_4486979] using wordTrace_append hprefix tailTrace_4486979
  have hstable : (prefixWord ++ tailWord_4486979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4486979).length < 2 ^ (prefixWord ++ tailWord_4486979).sum := by decide
  have hdescent : baseEnd_4486979 < baseStart_4486979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4486979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487049 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 5, 5]
def baseStart_4487049 : Nat := 118140960795 + 4487049 * 2 ^ 59
def prefixEnd_4487049 : Nat := 4983230072969 + 3 ^ 40 * 4487049 * 2
def baseEnd_4487049 : Nat := 768004285758706711283981

theorem tailTrace_4487049 : CollatzResearch.WordTrace tailWord_4487049 prefixEnd_4487049 768004285758706711283981 := by
  unfold tailWord_4487049
  simp only [CollatzResearch.WordTrace]
  refine ⟨163656121921195274803904201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109104081280796849869269467 163656121921195274803904201)
  ·
    refine ⟨122742091440896456102928151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163656121921195274803904201 122742091440896456102928151)
    ·
      refine ⟨184113137161344684154392227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122742091440896456102928151 184113137161344684154392227)
      ·
        refine ⟨276169705742017026231588341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184113137161344684154392227 276169705742017026231588341)
        ·
          refine ⟨25890909913314096209211407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 276169705742017026231588341 25890909913314096209211407)
          ·
            refine ⟨38836364869971144313817111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25890909913314096209211407 38836364869971144313817111)
            ·
              refine ⟨58254547304956716470725667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38836364869971144313817111 58254547304956716470725667)
              ·
                refine ⟨87381820957435074706088501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58254547304956716470725667 87381820957435074706088501)
                ·
                  refine ⟨8192045714759538253695797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87381820957435074706088501 8192045714759538253695797)
                  ·
                    refine ⟨768004285758706711283981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8192045714759538253695797 768004285758706711283981)
                    ·
                      rfl

theorem cell23_4487049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_4487049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487049 prefixEnd_4487049 := by exact prefixLift 4487049
  have htrace : WordTrace (prefixWord ++ tailWord_4487049) baseStart_4487049 baseEnd_4487049 := by
    simpa [prefixWord, tailWord_4487049, baseEnd_4487049] using wordTrace_append hprefix tailTrace_4487049
  have hstable : (prefixWord ++ tailWord_4487049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487049).length < 2 ^ (prefixWord ++ tailWord_4487049).sum := by decide
  have hdescent : baseEnd_4487049 < baseStart_4487049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487056 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 6, 3, 2]
def baseStart_4487056 : Nat := 118140960795 + 4487056 * 2 ^ 59
def prefixEnd_4487056 : Nat := 4983230072969 + 3 ^ 40 * 4487056 * 2
def baseEnd_4487056 : Nat := 2304016451640701606464411

theorem tailTrace_4487056 : CollatzResearch.WordTrace tailWord_4487056 prefixEnd_4487056 2304016451640701606464411 := by
  unfold tailWord_4487056
  simp only [CollatzResearch.WordTrace]
  refine ⟨81828188616084957499704511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109104251488113276666272681 81828188616084957499704511)
  ·
    refine ⟨122742282924127436249556767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81828188616084957499704511 122742282924127436249556767)
    ·
      refine ⟨184113424386191154374335151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122742282924127436249556767 184113424386191154374335151)
      ·
        refine ⟨276170136579286731561502727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184113424386191154374335151 276170136579286731561502727)
        ·
          refine ⟨414255204868930097342254091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276170136579286731561502727 414255204868930097342254091)
          ·
            refine ⟨621382807303395146013381137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414255204868930097342254091 621382807303395146013381137)
            ·
              refine ⟨466037105477546359510035853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621382807303395146013381137 466037105477546359510035853)
              ·
                refine ⟨174763914554079884816263445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466037105477546359510035853 174763914554079884816263445)
                ·
                  refine ⟨8192058494722494600762349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174763914554079884816263445 8192058494722494600762349)
                  ·
                    refine ⟨3072021935520935475285881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8192058494722494600762349 3072021935520935475285881)
                    ·
                      refine ⟨2304016451640701606464411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072021935520935475285881 2304016451640701606464411)
                      ·
                        rfl

theorem cell23_4487056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 3, 2].length) (baseStart_4487056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487056 prefixEnd_4487056 := by exact prefixLift 4487056
  have htrace : WordTrace (prefixWord ++ tailWord_4487056) baseStart_4487056 baseEnd_4487056 := by
    simpa [prefixWord, tailWord_4487056, baseEnd_4487056] using wordTrace_append hprefix tailTrace_4487056
  have hstable : (prefixWord ++ tailWord_4487056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487056).length < 2 ^ (prefixWord ++ tailWord_4487056).sum := by decide
  have hdescent : baseEnd_4487056 < baseStart_4487056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487063 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_4487063 : Nat := 118140960795 + 4487063 * 2 ^ 59
def prefixEnd_4487063 : Nat := 4983230072969 + 3 ^ 40 * 4487063 * 2
def baseEnd_4487063 : Nat := 2304020046005283079076879

theorem tailTrace_4487063 : CollatzResearch.WordTrace tailWord_4487063 prefixEnd_4487063 2304020046005283079076879 := by
  unfold tailWord_4487063
  simp only [CollatzResearch.WordTrace]
  refine ⟨163656632543144555194913843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109104421695429703463275895 163656632543144555194913843)
  ·
    refine ⟨245484948814716832792370765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163656632543144555194913843 245484948814716832792370765)
    ·
      refine ⟨92056855805518812297139037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245484948814716832792370765 92056855805518812297139037)
      ·
        refine ⟨34521320927069554611427139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92056855805518812297139037 34521320927069554611427139)
        ·
          refine ⟨51781981390604331917140709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34521320927069554611427139 51781981390604331917140709)
          ·
            refine ⟨9709121510738312234463883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51781981390604331917140709 9709121510738312234463883)
            ·
              refine ⟨14563682266107468351695825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709121510738312234463883 14563682266107468351695825)
              ·
                refine ⟨10922761699580601263771869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14563682266107468351695825 10922761699580601263771869)
                ·
                  refine ⟨4096035637342725473914451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10922761699580601263771869 4096035637342725473914451)
                  ·
                    refine ⟨6144053456014088210871677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4096035637342725473914451 6144053456014088210871677)
                    ·
                      refine ⟨2304020046005283079076879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6144053456014088210871677 2304020046005283079076879)
                      ·
                        rfl

theorem cell23_4487063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_4487063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487063 prefixEnd_4487063 := by exact prefixLift 4487063
  have htrace : WordTrace (prefixWord ++ tailWord_4487063) baseStart_4487063 baseEnd_4487063 := by
    simpa [prefixWord, tailWord_4487063, baseEnd_4487063] using wordTrace_append hprefix tailTrace_4487063
  have hstable : (prefixWord ++ tailWord_4487063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487063).length < 2 ^ (prefixWord ++ tailWord_4487063).sum := by decide
  have hdescent : baseEnd_4487063 < baseStart_4487063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487066 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_4487066 : Nat := 118140960795 + 4487066 * 2 ^ 59
def prefixEnd_4487066 : Nat := 4983230072969 + 3 ^ 40 * 4487066 * 2
def baseEnd_4487066 : Nat := 768007195482415522446455

theorem tailTrace_4487066 : CollatzResearch.WordTrace tailWord_4487066 prefixEnd_4487066 768007195482415522446455 := by
  unfold tailWord_4487066
  simp only [CollatzResearch.WordTrace]
  refine ⟨40914185490533421676818263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109104494641422457804848701 40914185490533421676818263)
  ·
    refine ⟨61371278235800132515227395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40914185490533421676818263 61371278235800132515227395)
    ·
      refine ⟨92056917353700198772841093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61371278235800132515227395 92056917353700198772841093)
      ·
        refine ⟨17260672003818787269907705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92056917353700198772841093 17260672003818787269907705)
        ·
          refine ⟨12945504002864090452430779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17260672003818787269907705 12945504002864090452430779)
          ·
            refine ⟨19418256004296135678646169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12945504002864090452430779 19418256004296135678646169)
            ·
              refine ⟨14563692003222101758984627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19418256004296135678646169 14563692003222101758984627)
              ·
                refine ⟨21845538004833152638476941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14563692003222101758984627 21845538004833152638476941)
                ·
                  refine ⟨8192076751812432239428853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21845538004833152638476941 8192076751812432239428853)
                  ·
                    refine ⟨768007195482415522446455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8192076751812432239428853 768007195482415522446455)
                    ·
                      rfl

theorem cell23_4487066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_4487066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487066 prefixEnd_4487066 := by exact prefixLift 4487066
  have htrace : WordTrace (prefixWord ++ tailWord_4487066) baseStart_4487066 baseEnd_4487066 := by
    simpa [prefixWord, tailWord_4487066, baseEnd_4487066] using wordTrace_append hprefix tailTrace_4487066
  have hstable : (prefixWord ++ tailWord_4487066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487066).length < 2 ^ (prefixWord ++ tailWord_4487066).sum := by decide
  have hdescent : baseEnd_4487066 < baseStart_4487066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487096 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 4, 4]
def baseStart_4487096 : Nat := 118140960795 + 4487096 * 2 ^ 59
def prefixEnd_4487096 : Nat := 4983230072969 + 3 ^ 40 * 4487096 * 2
def baseEnd_4487096 : Nat := 768012330288960483321409

theorem tailTrace_4487096 : CollatzResearch.WordTrace tailWord_4487096 prefixEnd_4487096 768012330288960483321409 := by
  unfold tailWord_4487096
  simp only [CollatzResearch.WordTrace]
  refine ⟨81828918076012500915432571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109105224101350001220576761 81828918076012500915432571)
  ·
    refine ⟨122743377114018751373148857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81828918076012500915432571 122743377114018751373148857)
    ·
      refine ⟨92057532835514063529861643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122743377114018751373148857 92057532835514063529861643)
      ·
        refine ⟨138086299253271095294792465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92057532835514063529861643 138086299253271095294792465)
        ·
          refine ⟨103564724439953321471094349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138086299253271095294792465 103564724439953321471094349)
          ·
            refine ⟨38836771664982495551660381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103564724439953321471094349 38836771664982495551660381)
            ·
              refine ⟨14563789374368435831872643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38836771664982495551660381 14563789374368435831872643)
              ·
                refine ⟨21845684061552653747808965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14563789374368435831872643 21845684061552653747808965)
                ·
                  refine ⟨4096065761541122577714181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21845684061552653747808965 4096065761541122577714181)
                  ·
                    refine ⟨768012330288960483321409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4096065761541122577714181 768012330288960483321409)
                    ·
                      rfl

theorem cell23_4487096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_4487096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487096 prefixEnd_4487096 := by exact prefixLift 4487096
  have htrace : WordTrace (prefixWord ++ tailWord_4487096) baseStart_4487096 baseEnd_4487096 := by
    simpa [prefixWord, tailWord_4487096, baseEnd_4487096] using wordTrace_append hprefix tailTrace_4487096
  have hstable : (prefixWord ++ tailWord_4487096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487096).length < 2 ^ (prefixWord ++ tailWord_4487096).sum := by decide
  have hdescent : baseEnd_4487096 < baseStart_4487096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487099 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4]
def baseStart_4487099 : Nat := 118140960795 + 4487099 * 2 ^ 59
def prefixEnd_4487099 : Nat := 4983230072969 + 3 ^ 40 * 4487099 * 2
def baseEnd_4487099 : Nat := 2304038531308844938226713

theorem tailTrace_4487099 : CollatzResearch.WordTrace tailWord_4487099 prefixEnd_4487099 2304038531308844938226713 := by
  unfold tailWord_4487099
  simp only [CollatzResearch.WordTrace]
  refine ⟨163657945571014133343224351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109105297047342755562149567 163657945571014133343224351)
  ·
    refine ⟨245486918356521200014836527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163657945571014133343224351 245486918356521200014836527)
    ·
      refine ⟨368230377534781800022254791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245486918356521200014836527 368230377534781800022254791)
      ·
        refine ⟨552345566302172700033382187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368230377534781800022254791 552345566302172700033382187)
        ·
          refine ⟨828518349453259050050073281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552345566302172700033382187 828518349453259050050073281)
          ·
            refine ⟨621388762089944287537554961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828518349453259050050073281 621388762089944287537554961)
            ·
              refine ⟨466041571567458215653166221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621388762089944287537554961 466041571567458215653166221)
              ·
                refine ⟨174765589337796830869937333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466041571567458215653166221 174765589337796830869937333)
                ·
                  refine ⟨16384274000418452894056625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174765589337796830869937333 16384274000418452894056625)
                  ·
                    refine ⟨12288205500313839670542469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16384274000418452894056625 12288205500313839670542469)
                    ·
                      refine ⟨2304038531308844938226713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12288205500313839670542469 2304038531308844938226713)
                      ·
                        rfl

theorem cell23_4487099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_4487099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487099 prefixEnd_4487099 := by exact prefixLift 4487099
  have htrace : WordTrace (prefixWord ++ tailWord_4487099) baseStart_4487099 baseEnd_4487099 := by
    simpa [prefixWord, tailWord_4487099, baseEnd_4487099] using wordTrace_append hprefix tailTrace_4487099
  have hstable : (prefixWord ++ tailWord_4487099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487099).length < 2 ^ (prefixWord ++ tailWord_4487099).sum := by decide
  have hdescent : baseEnd_4487099 < baseStart_4487099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487116 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4487116 : Nat := 118140960795 + 4487116 * 2 ^ 59
def prefixEnd_4487116 : Nat := 4983230072969 + 3 ^ 40 * 4487116 * 2
def baseEnd_4487116 : Nat := 2304047260479971371714135

theorem tailTrace_4487116 : CollatzResearch.WordTrace tailWord_4487116 prefixEnd_4487116 2304047260479971371714135 := by
  unfold tailWord_4487116
  simp only [CollatzResearch.WordTrace]
  refine ⟨81829282805976272623296601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109105710407968363497728801 81829282805976272623296601)
  ·
    refine ⟨61371962104482204467472451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81829282805976272623296601 61371962104482204467472451)
    ·
      refine ⟨92057943156723306701208677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61371962104482204467472451 92057943156723306701208677)
      ·
        refine ⟨17260864341885620006476627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92057943156723306701208677 17260864341885620006476627)
        ·
          refine ⟨25891296512828430009714941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17260864341885620006476627 25891296512828430009714941)
          ·
            refine ⟨9709236192310661253643103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25891296512828430009714941 9709236192310661253643103)
            ·
              refine ⟨14563854288465991880464655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709236192310661253643103 14563854288465991880464655)
              ·
                refine ⟨21845781432698987820696983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14563854288465991880464655 21845781432698987820696983)
                ·
                  refine ⟨32768672149048481731045475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21845781432698987820696983 32768672149048481731045475)
                  ·
                    refine ⟨49153008223572722596568213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32768672149048481731045475 49153008223572722596568213)
                    ·
                      refine ⟨2304047260479971371714135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49153008223572722596568213 2304047260479971371714135)
                      ·
                        rfl

theorem cell23_4487116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4487116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487116 prefixEnd_4487116 := by exact prefixLift 4487116
  have htrace : WordTrace (prefixWord ++ tailWord_4487116) baseStart_4487116 baseEnd_4487116 := by
    simpa [prefixWord, tailWord_4487116, baseEnd_4487116] using wordTrace_append hprefix tailTrace_4487116
  have hstable : (prefixWord ++ tailWord_4487116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487116).length < 2 ^ (prefixWord ++ tailWord_4487116).sum := by decide
  have hdescent : baseEnd_4487116 < baseStart_4487116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487136 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3]
def baseStart_4487136 : Nat := 118140960795 + 4487136 * 2 ^ 59
def prefixEnd_4487136 : Nat := 4983230072969 + 3 ^ 40 * 4487136 * 2
def baseEnd_4487136 : Nat := 2304057530093061293464043

theorem tailTrace_4487136 : CollatzResearch.WordTrace tailWord_4487136 prefixEnd_4487136 2304057530093061293464043 := by
  unfold tailWord_4487136
  simp only [CollatzResearch.WordTrace]
  refine ⟨81829647535940044331160631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109106196714586725774880841 81829647535940044331160631)
  ·
    refine ⟨122744471303910066496740947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81829647535940044331160631 122744471303910066496740947)
    ·
      refine ⟨184116706955865099745111421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122744471303910066496740947 184116706955865099745111421)
      ·
        refine ⟨69043765108449412404416783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184116706955865099745111421 69043765108449412404416783)
        ·
          refine ⟨103565647662674118606625175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69043765108449412404416783 103565647662674118606625175)
          ·
            refine ⟨155348471494011177909937763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103565647662674118606625175 155348471494011177909937763)
            ·
              refine ⟨233022707241016766864906645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155348471494011177909937763 233022707241016766864906645)
              ·
                refine ⟨10922939401922660946792499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 233022707241016766864906645 10922939401922660946792499)
                ·
                  refine ⟨16384409102883991420188749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10922939401922660946792499 16384409102883991420188749)
                  ·
                    refine ⟨6144153413581496782570781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16384409102883991420188749 6144153413581496782570781)
                    ·
                      refine ⟨2304057530093061293464043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6144153413581496782570781 2304057530093061293464043)
                      ·
                        rfl

theorem cell23_4487136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_4487136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487136 prefixEnd_4487136 := by exact prefixLift 4487136
  have htrace : WordTrace (prefixWord ++ tailWord_4487136) baseStart_4487136 baseEnd_4487136 := by
    simpa [prefixWord, tailWord_4487136, baseEnd_4487136] using wordTrace_append hprefix tailTrace_4487136
  have hstable : (prefixWord ++ tailWord_4487136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487136).length < 2 ^ (prefixWord ++ tailWord_4487136).sum := by decide
  have hdescent : baseEnd_4487136 < baseStart_4487136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487137 : List Nat := [1, 2, 3, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_4487137 : Nat := 118140960795 + 4487137 * 2 ^ 59
def prefixEnd_4487137 : Nat := 4983230072969 + 3 ^ 40 * 4487137 * 2
def baseEnd_4487137 : Nat := 2304058043573715789551539

theorem tailTrace_4487137 : CollatzResearch.WordTrace tailWord_4487137 prefixEnd_4487137 2304058043573715789551539 := by
  unfold tailWord_4487137
  simp only [CollatzResearch.WordTrace]
  refine ⟨163659331544876465833107665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109106221029917643888738443 163659331544876465833107665)
  ·
    refine ⟨122744498658657349374830749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163659331544876465833107665 122744498658657349374830749)
    ·
      refine ⟨46029186996996506015561531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122744498658657349374830749 46029186996996506015561531)
      ·
        refine ⟨69043780495494759023342297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46029186996996506015561531 69043780495494759023342297)
        ·
          refine ⟨51782835371621069267506723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69043780495494759023342297 51782835371621069267506723)
          ·
            refine ⟨77674253057431603901260085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51782835371621069267506723 77674253057431603901260085)
            ·
              refine ⟨7281961224134212865743133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77674253057431603901260085 7281961224134212865743133)
              ·
                refine ⟨2730735459050329824653675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7281961224134212865743133 2730735459050329824653675)
                ·
                  refine ⟨4096103188575494736980513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730735459050329824653675 4096103188575494736980513)
                  ·
                    refine ⟨3072077391431621052735385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4096103188575494736980513 3072077391431621052735385)
                    ·
                      refine ⟨2304058043573715789551539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072077391431621052735385 2304058043573715789551539)
                      ·
                        rfl

theorem cell23_4487137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_4487137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487137 prefixEnd_4487137 := by exact prefixLift 4487137
  have htrace : WordTrace (prefixWord ++ tailWord_4487137) baseStart_4487137 baseEnd_4487137 := by
    simpa [prefixWord, tailWord_4487137, baseEnd_4487137] using wordTrace_append hprefix tailTrace_4487137
  have hstable : (prefixWord ++ tailWord_4487137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487137).length < 2 ^ (prefixWord ++ tailWord_4487137).sum := by decide
  have hdescent : baseEnd_4487137 < baseStart_4487137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487143 : List Nat := [1, 1, 5, 2, 4, 1, 9]
def baseStart_4487143 : Nat := 118140960795 + 4487143 * 2 ^ 59
def prefixEnd_4487143 : Nat := 4983230072969 + 3 ^ 40 * 4487143 * 2
def baseEnd_4487143 : Nat := 28445199067378305754031

theorem tailTrace_4487143 : CollatzResearch.WordTrace tailWord_4487143 prefixEnd_4487143 28445199067378305754031 := by
  unfold tailWord_4487143
  simp only [CollatzResearch.WordTrace]
  refine ⟨163659550382854728857826083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109106366921903152571884055 163659550382854728857826083)
  ·
    refine ⟨245489325574282093286739125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163659550382854728857826083 245489325574282093286739125)
    ·
      refine ⟨23014624272588946245631793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245489325574282093286739125 23014624272588946245631793)
      ·
        refine ⟨17260968204441709684223845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23014624272588946245631793 17260968204441709684223845)
        ·
          refine ⟨3236431538332820565791971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17260968204441709684223845 3236431538332820565791971)
          ·
            refine ⟨4854647307499230848687957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236431538332820565791971 4854647307499230848687957)
            ·
              refine ⟨28445199067378305754031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4854647307499230848687957 28445199067378305754031)
              ·
                rfl

theorem cell23_4487143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 9].length) (baseStart_4487143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487143 prefixEnd_4487143 := by exact prefixLift 4487143
  have htrace : WordTrace (prefixWord ++ tailWord_4487143) baseStart_4487143 baseEnd_4487143 := by
    simpa [prefixWord, tailWord_4487143, baseEnd_4487143] using wordTrace_append hprefix tailTrace_4487143
  have hstable : (prefixWord ++ tailWord_4487143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487143).length < 2 ^ (prefixWord ++ tailWord_4487143).sum := by decide
  have hdescent : baseEnd_4487143 < baseStart_4487143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487220 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_4487220 : Nat := 118140960795 + 4487220 * 2 ^ 59
def prefixEnd_4487220 : Nat := 4983230072969 + 3 ^ 40 * 4487220 * 2
def baseEnd_4487220 : Nat := 768033554156012988271219

theorem tailTrace_4487220 : CollatzResearch.WordTrace tailWord_4487220 prefixEnd_4487220 768033554156012988271219 := by
  unfold tailWord_4487220
  simp only [CollatzResearch.WordTrace]
  refine ⟨81831179401787885504189557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109108239202383847338919409 81831179401787885504189557)
  ·
    refine ⟨7671673068917614266017771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81831179401787885504189557 7671673068917614266017771)
    ·
      refine ⟨11507509603376421399026657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7671673068917614266017771 11507509603376421399026657)
      ·
        refine ⟨8630632202532316049269993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11507509603376421399026657 8630632202532316049269993)
        ·
          refine ⟨6472974151899237036952495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8630632202532316049269993 6472974151899237036952495)
          ·
            refine ⟨9709461227848855555428743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472974151899237036952495 9709461227848855555428743)
            ·
              refine ⟨14564191841773283333143115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709461227848855555428743 14564191841773283333143115)
              ·
                refine ⟨21846287762659924999714673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14564191841773283333143115 21846287762659924999714673)
                ·
                  refine ⟨16384715821994943749786005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21846287762659924999714673 16384715821994943749786005)
                  ·
                    refine ⟨768033554156012988271219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16384715821994943749786005 768033554156012988271219)
                    ·
                      rfl

theorem cell23_4487220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_4487220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487220 prefixEnd_4487220 := by exact prefixLift 4487220
  have htrace : WordTrace (prefixWord ++ tailWord_4487220) baseStart_4487220 baseEnd_4487220 := by
    simpa [prefixWord, tailWord_4487220, baseEnd_4487220] using wordTrace_append hprefix tailTrace_4487220
  have hstable : (prefixWord ++ tailWord_4487220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487220).length < 2 ^ (prefixWord ++ tailWord_4487220).sum := by decide
  have hdescent : baseEnd_4487220 < baseStart_4487220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487233 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 7]
def baseStart_4487233 : Nat := 118140960795 + 4487233 * 2 ^ 59
def prefixEnd_4487233 : Nat := 4983230072969 + 3 ^ 40 * 4487233 * 2
def baseEnd_4487233 : Nat := 256011926412949712661233

theorem tailTrace_4487233 : CollatzResearch.WordTrace tailWord_4487233 prefixEnd_4487233 256011926412949712661233 := by
  unfold tailWord_4487233
  simp only [CollatzResearch.WordTrace]
  refine ⟨163662832952528674228602353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109108555301685782819068235 163662832952528674228602353)
  ·
    refine ⟨122747124714396505671451765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163662832952528674228602353 122747124714396505671451765)
    ·
      refine ⟨11507542941974672406698603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122747124714396505671451765 11507542941974672406698603)
      ·
        refine ⟨17261314412962008610047905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11507542941974672406698603 17261314412962008610047905)
        ·
          refine ⟨12945985809721506457535929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17261314412962008610047905 12945985809721506457535929)
          ·
            refine ⟨9709489357291129843151947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12945985809721506457535929 9709489357291129843151947)
            ·
              refine ⟨14564234035936694764727921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709489357291129843151947 14564234035936694764727921)
              ·
                refine ⟨10923175526952521073545941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14564234035936694764727921 10923175526952521073545941)
                ·
                  refine ⟨256011926412949712661233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10923175526952521073545941 256011926412949712661233)
                  ·
                    rfl

theorem cell23_4487233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 7].length) (baseStart_4487233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487233 prefixEnd_4487233 := by exact prefixLift 4487233
  have htrace : WordTrace (prefixWord ++ tailWord_4487233) baseStart_4487233 baseEnd_4487233 := by
    simpa [prefixWord, tailWord_4487233, baseEnd_4487233] using wordTrace_append hprefix tailTrace_4487233
  have hstable : (prefixWord ++ tailWord_4487233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487233).length < 2 ^ (prefixWord ++ tailWord_4487233).sum := by decide
  have hdescent : baseEnd_4487233 < baseStart_4487233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487261 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4487261 : Nat := 118140960795 + 4487261 * 2 ^ 59
def prefixEnd_4487261 : Nat := 4983230072969 + 3 ^ 40 * 4487261 * 2
def baseEnd_4487261 : Nat := 2304121715174873304400969

theorem tailTrace_4487261 : CollatzResearch.WordTrace tailWord_4487261 prefixEnd_4487261 2304121715174873304400969 := by
  unfold tailWord_4487261
  simp only [CollatzResearch.WordTrace]
  refine ⟨163663854196427235010621637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109109236130951490007081091 163663854196427235010621637)
  ·
    refine ⟨30686972661830106564491557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163663854196427235010621637 30686972661830106564491557)
    ·
      refine ⟨5753807374093144980842167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30686972661830106564491557 5753807374093144980842167)
      ·
        refine ⟨8630711061139717471263251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5753807374093144980842167 8630711061139717471263251)
        ·
          refine ⟨12946066591709576206894877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8630711061139717471263251 12946066591709576206894877)
          ·
            refine ⟨4854774971891091077585579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12946066591709576206894877 4854774971891091077585579)
            ·
              refine ⟨7282162457836636616378369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854774971891091077585579 7282162457836636616378369)
              ·
                refine ⟨5461621843377477462283777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7282162457836636616378369 5461621843377477462283777)
                ·
                  refine ⟨4096216382533108096712833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5461621843377477462283777 4096216382533108096712833)
                  ·
                    refine ⟨3072162286899831072534625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4096216382533108096712833 3072162286899831072534625)
                    ·
                      refine ⟨2304121715174873304400969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072162286899831072534625 2304121715174873304400969)
                      ·
                        rfl

theorem cell23_4487261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4487261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487261 prefixEnd_4487261 := by exact prefixLift 4487261
  have htrace : WordTrace (prefixWord ++ tailWord_4487261) baseStart_4487261 baseEnd_4487261 := by
    simpa [prefixWord, tailWord_4487261, baseEnd_4487261] using wordTrace_append hprefix tailTrace_4487261
  have hstable : (prefixWord ++ tailWord_4487261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487261).length < 2 ^ (prefixWord ++ tailWord_4487261).sum := by decide
  have hdescent : baseEnd_4487261 < baseStart_4487261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487296 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_4487296 : Nat := 118140960795 + 4487296 * 2 ^ 59
def prefixEnd_4487296 : Nat := 4983230072969 + 3 ^ 40 * 4487296 * 2
def baseEnd_4487296 : Nat := 2304139686997780667463307

theorem tailTrace_4487296 : CollatzResearch.WordTrace tailWord_4487296 prefixEnd_4487296 2304139686997780667463307 := by
  unfold tailWord_4487296
  simp only [CollatzResearch.WordTrace]
  refine ⟨81832565375650217994072871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109110087167533623992097161 81832565375650217994072871)
  ·
    refine ⟨122748848063475326991109307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81832565375650217994072871 122748848063475326991109307)
    ·
      refine ⟨184123272095212990486663961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122748848063475326991109307 184123272095212990486663961)
      ·
        refine ⟨138092454071409742864997971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184123272095212990486663961 138092454071409742864997971)
        ·
          refine ⟨207138681107114614297496957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138092454071409742864997971 207138681107114614297496957)
          ·
            refine ⟨77677005415167980361561359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207138681107114614297496957 77677005415167980361561359)
            ·
              refine ⟨116515508122751970542342039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77677005415167980361561359 116515508122751970542342039)
              ·
                refine ⟨174773262184127955813513059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116515508122751970542342039 174773262184127955813513059)
                ·
                  refine ⟨262159893276191933720269589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174773262184127955813513059 262159893276191933720269589)
                  ·
                    refine ⟨12288744997321496893137637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 262159893276191933720269589 12288744997321496893137637)
                    ·
                      refine ⟨2304139686997780667463307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12288744997321496893137637 2304139686997780667463307)
                      ·
                        rfl

theorem cell23_4487296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_4487296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487296 prefixEnd_4487296 := by exact prefixLift 4487296
  have htrace : WordTrace (prefixWord ++ tailWord_4487296) baseStart_4487296 baseEnd_4487296 := by
    simpa [prefixWord, tailWord_4487296, baseEnd_4487296] using wordTrace_append hprefix tailTrace_4487296
  have hstable : (prefixWord ++ tailWord_4487296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487296).length < 2 ^ (prefixWord ++ tailWord_4487296).sum := by decide
  have hdescent : baseEnd_4487296 < baseStart_4487296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487303 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_4487303 : Nat := 118140960795 + 4487303 * 2 ^ 59
def prefixEnd_4487303 : Nat := 4983230072969 + 3 ^ 40 * 4487303 * 2
def baseEnd_4487303 : Nat := 2304143281362362140075775

theorem tailTrace_4487303 : CollatzResearch.WordTrace tailWord_4487303 prefixEnd_4487303 2304143281362362140075775 := by
  unfold tailWord_4487303
  simp only [CollatzResearch.WordTrace]
  refine ⟨163665386062275076183650563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109110257374850050789100375 163665386062275076183650563)
  ·
    refine ⟨245498079093412614275475845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163665386062275076183650563 245498079093412614275475845)
    ·
      refine ⟨46030889830014865176651721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245498079093412614275475845 46030889830014865176651721)
      ·
        refine ⟨34523167372511148882488791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46030889830014865176651721 34523167372511148882488791)
        ·
          refine ⟨51784751058766723323733187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34523167372511148882488791 51784751058766723323733187)
          ·
            refine ⟨77677126588150084985599781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51784751058766723323733187 77677126588150084985599781)
            ·
              refine ⟨14564461235278140934799959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77677126588150084985599781 14564461235278140934799959)
              ·
                refine ⟨21846691852917211402199939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14564461235278140934799959 21846691852917211402199939)
                ·
                  refine ⟨32770037779375817103299909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21846691852917211402199939 32770037779375817103299909)
                  ·
                    refine ⟨6144382083632965706868733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32770037779375817103299909 6144382083632965706868733)
                    ·
                      refine ⟨2304143281362362140075775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6144382083632965706868733 2304143281362362140075775)
                      ·
                        rfl

theorem cell23_4487303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_4487303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487303 prefixEnd_4487303 := by exact prefixLift 4487303
  have htrace : WordTrace (prefixWord ++ tailWord_4487303) baseStart_4487303 baseEnd_4487303 := by
    simpa [prefixWord, tailWord_4487303, baseEnd_4487303] using wordTrace_append hprefix tailTrace_4487303
  have hstable : (prefixWord ++ tailWord_4487303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487303).length < 2 ^ (prefixWord ++ tailWord_4487303).sum := by decide
  have hdescent : baseEnd_4487303 < baseStart_4487303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487318 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_4487318 : Nat := 118140960795 + 4487318 * 2 ^ 59
def prefixEnd_4487318 : Nat := 4983230072969 + 3 ^ 40 * 4487318 * 2
def baseEnd_4487318 : Nat := 256016775952464397932023

theorem tailTrace_4487318 : CollatzResearch.WordTrace tailWord_4487318 prefixEnd_4487318 256016775952464397932023 := by
  unfold tailWord_4487318
  simp only [CollatzResearch.WordTrace]
  refine ⟨10229120822326295859090413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109110622104813822496964405 10229120822326295859090413)
  ·
    refine ⟨3835920308372360947158905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10229120822326295859090413 3835920308372360947158905)
    ·
      refine ⟨2876940231279270710369179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3835920308372360947158905 2876940231279270710369179)
      ·
        refine ⟨4315410346918906065553769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876940231279270710369179 4315410346918906065553769)
        ·
          refine ⟨3236557760189179549165327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315410346918906065553769 3236557760189179549165327)
          ·
            refine ⟨4854836640283769323747991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236557760189179549165327 4854836640283769323747991)
            ·
              refine ⟨7282254960425653985621987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854836640283769323747991 7282254960425653985621987)
              ·
                refine ⟨10923382440638480978432981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282254960425653985621987 10923382440638480978432981)
                ·
                  refine ⟨256016775952464397932023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10923382440638480978432981 256016775952464397932023)
                  ·
                    rfl

theorem cell23_4487318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_4487318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487318 prefixEnd_4487318 := by exact prefixLift 4487318
  have htrace : WordTrace (prefixWord ++ tailWord_4487318) baseStart_4487318 baseEnd_4487318 := by
    simpa [prefixWord, tailWord_4487318, baseEnd_4487318] using wordTrace_append hprefix tailTrace_4487318
  have hstable : (prefixWord ++ tailWord_4487318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487318).length < 2 ^ (prefixWord ++ tailWord_4487318).sum := by decide
  have hdescent : baseEnd_4487318 < baseStart_4487318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487327 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 3, 4]
def baseStart_4487327 : Nat := 118140960795 + 4487327 * 2 ^ 59
def prefixEnd_4487327 : Nat := 4983230072969 + 3 ^ 40 * 4487327 * 2
def baseEnd_4487327 : Nat := 768051868299356682058555

theorem tailTrace_4487327 : CollatzResearch.WordTrace tailWord_4487327 prefixEnd_4487327 768051868299356682058555 := by
  unfold tailWord_4487327
  simp only [CollatzResearch.WordTrace]
  refine ⟨163666261414188128282524235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109110840942792085521682823 163666261414188128282524235)
  ·
    refine ⟨245499392121282192423786353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163666261414188128282524235 245499392121282192423786353)
    ·
      refine ⟨184124544090961644317839765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245499392121282192423786353 184124544090961644317839765)
      ·
        refine ⟨8630838004263827077398739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 184124544090961644317839765 8630838004263827077398739)
        ·
          refine ⟨12946257006395740616098109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8630838004263827077398739 12946257006395740616098109)
          ·
            refine ⟨4854846377398402731036791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12946257006395740616098109 4854846377398402731036791)
            ·
              refine ⟨7282269566097604096555187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854846377398402731036791 7282269566097604096555187)
              ·
                refine ⟨10923404349146406144832781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282269566097604096555187 10923404349146406144832781)
                ·
                  refine ⟨4096276630929902304312293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10923404349146406144832781 4096276630929902304312293)
                  ·
                    refine ⟨768051868299356682058555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4096276630929902304312293 768051868299356682058555)
                    ·
                      rfl

theorem cell23_4487327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_4487327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487327 prefixEnd_4487327 := by exact prefixLift 4487327
  have htrace : WordTrace (prefixWord ++ tailWord_4487327) baseStart_4487327 baseEnd_4487327 := by
    simpa [prefixWord, tailWord_4487327, baseEnd_4487327] using wordTrace_append hprefix tailTrace_4487327
  have hstable : (prefixWord ++ tailWord_4487327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487327).length < 2 ^ (prefixWord ++ tailWord_4487327).sum := by decide
  have hdescent : baseEnd_4487327 < baseStart_4487327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487353 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 3, 5]
def baseStart_4487353 : Nat := 118140960795 + 4487353 * 2 ^ 59
def prefixEnd_4487353 : Nat := 4983230072969 + 3 ^ 40 * 4487353 * 2
def baseEnd_4487353 : Nat := 768056318465028981483515

theorem tailTrace_4487353 : CollatzResearch.WordTrace tailWord_4487353 prefixEnd_4487353 768056318465028981483515 := by
  unfold tailWord_4487353
  simp only [CollatzResearch.WordTrace]
  refine ⟨163667209712093934722970713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109111473141395956481980475 163667209712093934722970713)
  ·
    refine ⟨122750407284070451042228035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163667209712093934722970713 122750407284070451042228035)
    ·
      refine ⟨184125610926105676563342053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122750407284070451042228035 184125610926105676563342053)
      ·
        refine ⟨34523552048644814355626635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184125610926105676563342053 34523552048644814355626635)
        ·
          refine ⟨51785328072967221533439953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34523552048644814355626635 51785328072967221533439953)
          ·
            refine ⟨38838996054725416150079965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51785328072967221533439953 38838996054725416150079965)
            ·
              refine ⟨14564623520522031056279987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38838996054725416150079965 14564623520522031056279987)
              ·
                refine ⟨21846935280783046584419981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14564623520522031056279987 21846935280783046584419981)
                ·
                  refine ⟨8192600730293642469157493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21846935280783046584419981 8192600730293642469157493)
                  ·
                    refine ⟨768056318465028981483515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8192600730293642469157493 768056318465028981483515)
                    ·
                      rfl

theorem cell23_4487353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_4487353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487353 prefixEnd_4487353 := by exact prefixLift 4487353
  have htrace : WordTrace (prefixWord ++ tailWord_4487353) baseStart_4487353 baseEnd_4487353 := by
    simpa [prefixWord, tailWord_4487353, baseEnd_4487353] using wordTrace_append hprefix tailTrace_4487353
  have hstable : (prefixWord ++ tailWord_4487353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487353).length < 2 ^ (prefixWord ++ tailWord_4487353).sum := by decide
  have hdescent : baseEnd_4487353 < baseStart_4487353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487384 : List Nat := [2, 1, 2, 2, 4, 2, 1, 4, 1, 1, 3]
def baseStart_4487384 : Nat := 118140960795 + 4487384 * 2 ^ 59
def prefixEnd_4487384 : Nat := 4983230072969 + 3 ^ 40 * 4487384 * 2
def baseEnd_4487384 : Nat := 2304184873295376323162903

theorem tailTrace_4487384 : CollatzResearch.WordTrace tailWord_4487384 prefixEnd_4487384 2304184873295376323162903 := by
  unfold tailWord_4487384
  simp only [CollatzResearch.WordTrace]
  refine ⟨81834170187490813508674603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109112226916654418011566137 81834170187490813508674603)
  ·
    refine ⟨122751255281236220263011905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81834170187490813508674603 122751255281236220263011905)
    ·
      refine ⟨92063441460927165197258929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122751255281236220263011905 92063441460927165197258929)
      ·
        refine ⟨69047581095695373897944197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92063441460927165197258929 69047581095695373897944197)
        ·
          refine ⟨12946421455442882605864537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69047581095695373897944197 12946421455442882605864537)
          ·
            refine ⟨9709816091582161954398403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12946421455442882605864537 9709816091582161954398403)
            ·
              refine ⟨14564724137373242931597605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709816091582161954398403 14564724137373242931597605)
              ·
                refine ⟨2730885775757483049674551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14564724137373242931597605 2730885775757483049674551)
                ·
                  refine ⟨4096328663636224574511827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730885775757483049674551 4096328663636224574511827)
                  ·
                    refine ⟨6144492995454336861767741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4096328663636224574511827 6144492995454336861767741)
                    ·
                      refine ⟨2304184873295376323162903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6144492995454336861767741 2304184873295376323162903)
                      ·
                        rfl

theorem cell23_4487384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_4487384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487384 prefixEnd_4487384 := by exact prefixLift 4487384
  have htrace : WordTrace (prefixWord ++ tailWord_4487384) baseStart_4487384 baseEnd_4487384 := by
    simpa [prefixWord, tailWord_4487384, baseEnd_4487384] using wordTrace_append hprefix tailTrace_4487384
  have hstable : (prefixWord ++ tailWord_4487384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487384).length < 2 ^ (prefixWord ++ tailWord_4487384).sum := by decide
  have hdescent : baseEnd_4487384 < baseStart_4487384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487393 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_4487393 : Nat := 118140960795 + 4487393 * 2 ^ 59
def prefixEnd_4487393 : Nat := 4983230072969 + 3 ^ 40 * 4487393 * 2
def baseEnd_4487393 : Nat := 2304189494621266787950361

theorem tailTrace_4487393 : CollatzResearch.WordTrace tailWord_4487393 prefixEnd_4487393 2304189494621266787950361 := by
  unfold tailWord_4487393
  simp only [CollatzResearch.WordTrace]
  refine ⟨163668668631949021554426833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109112445754632681036284555 163668668631949021554426833)
  ·
    refine ⟨122751501473961766165820125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163668668631949021554426833 122751501473961766165820125)
    ·
      refine ⟨46031813052735662312182547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122751501473961766165820125 46031813052735662312182547)
      ·
        refine ⟨69047719579103493468273821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46031813052735662312182547 69047719579103493468273821)
        ·
          refine ⟨25892894842163810050602683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69047719579103493468273821 25892894842163810050602683)
          ·
            refine ⟨38839342263245715075904025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25892894842163810050602683 38839342263245715075904025)
            ·
              refine ⟨29129506697434286306928019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38839342263245715075904025 29129506697434286306928019)
              ·
                refine ⟨43694260046151429460392029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29129506697434286306928019 43694260046151429460392029)
                ·
                  refine ⟨16385347517306786047647011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43694260046151429460392029 16385347517306786047647011)
                  ·
                    refine ⟨24578021275960179071470517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16385347517306786047647011 24578021275960179071470517)
                    ·
                      refine ⟨2304189494621266787950361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24578021275960179071470517 2304189494621266787950361)
                      ·
                        rfl

theorem cell23_4487393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_4487393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487393 prefixEnd_4487393 := by exact prefixLift 4487393
  have htrace : WordTrace (prefixWord ++ tailWord_4487393) baseStart_4487393 baseEnd_4487393 := by
    simpa [prefixWord, tailWord_4487393, baseEnd_4487393] using wordTrace_append hprefix tailTrace_4487393
  have hstable : (prefixWord ++ tailWord_4487393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487393).length < 2 ^ (prefixWord ++ tailWord_4487393).sum := by decide
  have hdescent : baseEnd_4487393 < baseStart_4487393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487400 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 1, 6]
def baseStart_4487400 : Nat := 118140960795 + 4487400 * 2 ^ 59
def prefixEnd_4487400 : Nat := 4983230072969 + 3 ^ 40 * 4487400 * 2
def baseEnd_4487400 : Nat := 768064362995282753520943

theorem tailTrace_4487400 : CollatzResearch.WordTrace tailWord_4487400 prefixEnd_4487400 768064362995282753520943 := by
  unfold tailWord_4487400
  simp only [CollatzResearch.WordTrace]
  refine ⟨81834461971461830874965827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109112615961949107833287769 81834461971461830874965827)
  ·
    refine ⟨122751692957192746312448741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81834461971461830874965827 122751692957192746312448741)
    ·
      refine ⟨23015942429473639933584139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122751692957192746312448741 23015942429473639933584139)
      ·
        refine ⟨34523913644210459900376209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23015942429473639933584139 34523913644210459900376209)
        ·
          refine ⟨25892935233157844925282157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34523913644210459900376209 25892935233157844925282157)
          ·
            refine ⟨9709850712434191846980809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25892935233157844925282157 9709850712434191846980809)
            ·
              refine ⟨7282388034325643885235607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9709850712434191846980809 7282388034325643885235607)
              ·
                refine ⟨10923582051488465827853411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282388034325643885235607 10923582051488465827853411)
                ·
                  refine ⟨16385373077232698741780117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10923582051488465827853411 16385373077232698741780117)
                  ·
                    refine ⟨768064362995282753520943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16385373077232698741780117 768064362995282753520943)
                    ·
                      rfl

theorem cell23_4487400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_4487400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487400 prefixEnd_4487400 := by exact prefixLift 4487400
  have htrace : WordTrace (prefixWord ++ tailWord_4487400) baseStart_4487400 baseEnd_4487400 := by
    simpa [prefixWord, tailWord_4487400, baseEnd_4487400] using wordTrace_append hprefix tailTrace_4487400
  have hstable : (prefixWord ++ tailWord_4487400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487400).length < 2 ^ (prefixWord ++ tailWord_4487400).sum := by decide
  have hdescent : baseEnd_4487400 < baseStart_4487400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487407 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 5, 2, 2]
def baseStart_4487407 : Nat := 118140960795 + 4487407 * 2 ^ 59
def prefixEnd_4487407 : Nat := 4983230072969 + 3 ^ 40 * 4487407 * 2
def baseEnd_4487407 : Nat := 2304196683350429733175297

theorem tailTrace_4487407 : CollatzResearch.WordTrace tailWord_4487407 prefixEnd_4487407 2304196683350429733175297 := by
  unfold tailWord_4487407
  simp only [CollatzResearch.WordTrace]
  refine ⟨163669179253898301945436475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109112786169265534630290983 163669179253898301945436475)
  ·
    refine ⟨245503768880847452918154713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163669179253898301945436475 245503768880847452918154713)
    ·
      refine ⟨184127826660635589688616035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245503768880847452918154713 184127826660635589688616035)
      ·
        refine ⟨276191739990953384532924053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184127826660635589688616035 276191739990953384532924053)
        ·
          refine ⟨12946487812075939899980815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 276191739990953384532924053 12946487812075939899980815)
          ·
            refine ⟨19419731718113909849971223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12946487812075939899980815 19419731718113909849971223)
            ·
              refine ⟨29129597577170864774956835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19419731718113909849971223 29129597577170864774956835)
              ·
                refine ⟨43694396365756297162435253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29129597577170864774956835 43694396365756297162435253)
                ·
                  refine ⟨4096349659289652858978305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43694396365756297162435253 4096349659289652858978305)
                  ·
                    refine ⟨3072262244467239644233729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4096349659289652858978305 3072262244467239644233729)
                    ·
                      refine ⟨2304196683350429733175297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072262244467239644233729 2304196683350429733175297)
                      ·
                        rfl

theorem cell23_4487407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 2, 2].length) (baseStart_4487407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487407 prefixEnd_4487407 := by exact prefixLift 4487407
  have htrace : WordTrace (prefixWord ++ tailWord_4487407) baseStart_4487407 baseEnd_4487407 := by
    simpa [prefixWord, tailWord_4487407, baseEnd_4487407] using wordTrace_append hprefix tailTrace_4487407
  have hstable : (prefixWord ++ tailWord_4487407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487407).length < 2 ^ (prefixWord ++ tailWord_4487407).sum := by decide
  have hdescent : baseEnd_4487407 < baseStart_4487407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487420 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_4487420 : Nat := 118140960795 + 4487420 * 2 ^ 59
def prefixEnd_4487420 : Nat := 4983230072969 + 3 ^ 40 * 4487420 * 2
def baseEnd_4487420 : Nat := 2304203358598938182312737

theorem tailTrace_4487420 : CollatzResearch.WordTrace tailWord_4487420 prefixEnd_4487420 2304203358598938182312737 := by
  unfold tailWord_4487420
  simp only [CollatzResearch.WordTrace]
  refine ⟨81834826701425602582829857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109113102268567470110439809 81834826701425602582829857)
  ·
    refine ⟨61376120026069201937122393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81834826701425602582829857 61376120026069201937122393)
    ·
      refine ⟨46032090019551901452841795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61376120026069201937122393 46032090019551901452841795)
      ·
        refine ⟨69048135029327852179262693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46032090019551901452841795 69048135029327852179262693)
        ·
          refine ⟨12946525317998972283611755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69048135029327852179262693 12946525317998972283611755)
          ·
            refine ⟨19419787976998458425417633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12946525317998972283611755 19419787976998458425417633)
            ·
              refine ⟨14564840982748843819063225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19419787976998458425417633 14564840982748843819063225)
              ·
                refine ⟨10923630737061632864297419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14564840982748843819063225 10923630737061632864297419)
                ·
                  refine ⟨16385446105592449296446129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10923630737061632864297419 16385446105592449296446129)
                  ·
                    refine ⟨12289084579194336972334597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16385446105592449296446129 12289084579194336972334597)
                    ·
                      refine ⟨2304203358598938182312737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12289084579194336972334597 2304203358598938182312737)
                      ·
                        rfl

theorem cell23_4487420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_4487420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487420 prefixEnd_4487420 := by exact prefixLift 4487420
  have htrace : WordTrace (prefixWord ++ tailWord_4487420) baseStart_4487420 baseEnd_4487420 := by
    simpa [prefixWord, tailWord_4487420, baseEnd_4487420] using wordTrace_append hprefix tailTrace_4487420
  have hstable : (prefixWord ++ tailWord_4487420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487420).length < 2 ^ (prefixWord ++ tailWord_4487420).sum := by decide
  have hdescent : baseEnd_4487420 < baseStart_4487420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487424 : List Nat := [2, 1, 1, 2, 1, 1, 5, 5, 1, 2, 2]
def baseStart_4487424 : Nat := 118140960795 + 4487424 * 2 ^ 59
def prefixEnd_4487424 : Nat := 4983230072969 + 3 ^ 40 * 4487424 * 2
def baseEnd_4487424 : Nat := 2304205412521556166662719

theorem tailTrace_4487424 : CollatzResearch.WordTrace tailWord_4487424 prefixEnd_4487424 2304205412521556166662719 := by
  unfold tailWord_4487424
  simp only [CollatzResearch.WordTrace]
  refine ⟨81834899647418356924402663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109113199529891142565870217 81834899647418356924402663)
  ·
    refine ⟨122752349471127535386603995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81834899647418356924402663 122752349471127535386603995)
    ·
      refine ⟨184128524206691303079905993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122752349471127535386603995 184128524206691303079905993)
      ·
        refine ⟨138096393155018477309929495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184128524206691303079905993 138096393155018477309929495)
        ·
          refine ⟨207144589732527715964894243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138096393155018477309929495 207144589732527715964894243)
          ·
            refine ⟨310716884598791573947341365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207144589732527715964894243 310716884598791573947341365)
            ·
              refine ⟨29129707931136710057563253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 310716884598791573947341365 29129707931136710057563253)
              ·
                refine ⟨2730910118544066567896555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29129707931136710057563253 2730910118544066567896555)
                ·
                  refine ⟨4096365177816099851844833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730910118544066567896555 4096365177816099851844833)
                  ·
                    refine ⟨3072273883362074888883625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4096365177816099851844833 3072273883362074888883625)
                    ·
                      refine ⟨2304205412521556166662719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072273883362074888883625 2304205412521556166662719)
                      ·
                        rfl

theorem cell23_4487424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_4487424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487424 prefixEnd_4487424 := by exact prefixLift 4487424
  have htrace : WordTrace (prefixWord ++ tailWord_4487424) baseStart_4487424 baseEnd_4487424 := by
    simpa [prefixWord, tailWord_4487424, baseEnd_4487424] using wordTrace_append hprefix tailTrace_4487424
  have hstable : (prefixWord ++ tailWord_4487424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487424).length < 2 ^ (prefixWord ++ tailWord_4487424).sum := by decide
  have hdescent : baseEnd_4487424 < baseStart_4487424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487454 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4487454 : Nat := 118140960795 + 4487454 * 2 ^ 59
def prefixEnd_4487454 : Nat := 4983230072969 + 3 ^ 40 * 4487454 * 2
def baseEnd_4487454 : Nat := 2304220816941191049287581

theorem tailTrace_4487454 : CollatzResearch.WordTrace tailWord_4487454 prefixEnd_4487454 2304220816941191049287581 := by
  unfold tailWord_4487454
  simp only [CollatzResearch.WordTrace]
  refine ⟨20458861685591003621549677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109113928989818685981598277 20458861685591003621549677)
  ·
    refine ⟨7672073132096626358081129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20458861685591003621549677 7672073132096626358081129)
    ·
      refine ⟨5754054849072469768560847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7672073132096626358081129 5754054849072469768560847)
      ·
        refine ⟨8631082273608704652841271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5754054849072469768560847 8631082273608704652841271)
        ·
          refine ⟨12946623410413056979261907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8631082273608704652841271 12946623410413056979261907)
          ·
            refine ⟨19419935115619585468892861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12946623410413056979261907 19419935115619585468892861)
            ·
              refine ⟨7282475668357344550834823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19419935115619585468892861 7282475668357344550834823)
              ·
                refine ⟨10923713502536016826252235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282475668357344550834823 10923713502536016826252235)
                ·
                  refine ⟨16385570253804025239378353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10923713502536016826252235 16385570253804025239378353)
                  ·
                    refine ⟨12289177690353018929533765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16385570253804025239378353 12289177690353018929533765)
                    ·
                      refine ⟨2304220816941191049287581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12289177690353018929533765 2304220816941191049287581)
                      ·
                        rfl

theorem cell23_4487454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4487454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487454 prefixEnd_4487454 := by exact prefixLift 4487454
  have htrace : WordTrace (prefixWord ++ tailWord_4487454) baseStart_4487454 baseEnd_4487454 := by
    simpa [prefixWord, tailWord_4487454, baseEnd_4487454] using wordTrace_append hprefix tailTrace_4487454
  have hstable : (prefixWord ++ tailWord_4487454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487454).length < 2 ^ (prefixWord ++ tailWord_4487454).sum := by decide
  have hdescent : baseEnd_4487454 < baseStart_4487454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487457 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4487457 : Nat := 118140960795 + 4487457 * 2 ^ 59
def prefixEnd_4487457 : Nat := 4983230072969 + 3 ^ 40 * 4487457 * 2
def baseEnd_4487457 : Nat := 2304222357383154537550067

theorem tailTrace_4487457 : CollatzResearch.WordTrace tailWord_4487457 prefixEnd_4487457 2304222357383154537550067 := by
  unfold tailWord_4487457
  simp only [CollatzResearch.WordTrace]
  refine ⟨163671002903717160484756625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109114001935811440323171083 163671002903717160484756625)
  ·
    refine ⟨122753252177787870363567469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163671002903717160484756625 122753252177787870363567469)
    ·
      refine ⟨46032469566670451386337801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122753252177787870363567469 46032469566670451386337801)
      ·
        refine ⟨34524352175002838539753351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46032469566670451386337801 34524352175002838539753351)
        ·
          refine ⟨51786528262504257809630027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34524352175002838539753351 51786528262504257809630027)
          ·
            refine ⟨77679792393756386714445041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51786528262504257809630027 77679792393756386714445041)
            ·
              refine ⟨58259844295317290035833781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77679792393756386714445041 58259844295317290035833781)
              ·
                refine ⟨5461860402685995940859417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58259844295317290035833781 5461860402685995940859417)
                ·
                  refine ⟨4096395302014496955644563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5461860402685995940859417 4096395302014496955644563)
                  ·
                    refine ⟨6144592953021745433466845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4096395302014496955644563 6144592953021745433466845)
                    ·
                      refine ⟨2304222357383154537550067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6144592953021745433466845 2304222357383154537550067)
                      ·
                        rfl

theorem cell23_4487457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4487457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487457 prefixEnd_4487457 := by exact prefixLift 4487457
  have htrace : WordTrace (prefixWord ++ tailWord_4487457) baseStart_4487457 baseEnd_4487457 := by
    simpa [prefixWord, tailWord_4487457, baseEnd_4487457] using wordTrace_append hprefix tailTrace_4487457
  have hstable : (prefixWord ++ tailWord_4487457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487457).length < 2 ^ (prefixWord ++ tailWord_4487457).sum := by decide
  have hdescent : baseEnd_4487457 < baseStart_4487457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487464 : List Nat := [2, 1, 5, 1, 4, 1, 2, 7]
def baseStart_4487464 : Nat := 118140960795 + 4487464 * 2 ^ 59
def prefixEnd_4487464 : Nat := 4983230072969 + 3 ^ 40 * 4487464 * 2
def baseEnd_4487464 : Nat := 85341701916582815191205

theorem tailTrace_4487464 : CollatzResearch.WordTrace tailWord_4487464 prefixEnd_4487464 85341701916582815191205 := by
  unfold tailWord_4487464
  simp only [CollatzResearch.WordTrace]
  refine ⟨81835629107345900340130723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109114172143127867120174297 81835629107345900340130723)
  ·
    refine ⟨122753443661018850510196085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81835629107345900340130723 122753443661018850510196085)
    ·
      refine ⟨11508135343220517235330883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122753443661018850510196085 11508135343220517235330883)
      ·
        refine ⟨17262203014830775852996325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11508135343220517235330883 17262203014830775852996325)
        ·
          refine ⟨3236663065280770472436811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17262203014830775852996325 3236663065280770472436811)
          ·
            refine ⟨4854994597921155708655217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236663065280770472436811 4854994597921155708655217)
            ·
              refine ⟨3641245948440866781491413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4854994597921155708655217 3641245948440866781491413)
              ·
                refine ⟨85341701916582815191205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3641245948440866781491413 85341701916582815191205)
                ·
                  rfl

theorem cell23_4487464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 7].length) (baseStart_4487464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487464 prefixEnd_4487464 := by exact prefixLift 4487464
  have htrace : WordTrace (prefixWord ++ tailWord_4487464) baseStart_4487464 baseEnd_4487464 := by
    simpa [prefixWord, tailWord_4487464, baseEnd_4487464] using wordTrace_append hprefix tailTrace_4487464
  have hstable : (prefixWord ++ tailWord_4487464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487464).length < 2 ^ (prefixWord ++ tailWord_4487464).sum := by decide
  have hdescent : baseEnd_4487464 < baseStart_4487464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487500 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_4487500 : Nat := 118140960795 + 4487500 * 2 ^ 59
def prefixEnd_4487500 : Nat := 4983230072969 + 3 ^ 40 * 4487500 * 2
def baseEnd_4487500 : Nat := 2304244437051297869312369

theorem tailTrace_4487500 : CollatzResearch.WordTrace tailWord_4487500 prefixEnd_4487500 2304244437051297869312369 := by
  unfold tailWord_4487500
  simp only [CollatzResearch.WordTrace]
  refine ⟨81836285621280689414285977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109115047495040919219047969 81836285621280689414285977)
  ·
    refine ⟨61377214215960517060714483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81836285621280689414285977 61377214215960517060714483)
    ·
      refine ⟨92065821323940775591071725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61377214215960517060714483 92065821323940775591071725)
      ·
        refine ⟨34524682996477790846651897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92065821323940775591071725 34524682996477790846651897)
        ·
          refine ⟨25893512247358343134988923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34524682996477790846651897 25893512247358343134988923)
          ·
            refine ⟨38840268371037514702483385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25893512247358343134988923 38840268371037514702483385)
            ·
              refine ⟨29130201278278136026862539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38840268371037514702483385 29130201278278136026862539)
              ·
                refine ⟨43695301917417204040293809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29130201278278136026862539 43695301917417204040293809)
                ·
                  refine ⟨32771476438062903030220357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43695301917417204040293809 32771476438062903030220357)
                  ·
                    refine ⟨6144651832136794318166317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32771476438062903030220357 6144651832136794318166317)
                    ·
                      refine ⟨2304244437051297869312369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6144651832136794318166317 2304244437051297869312369)
                      ·
                        rfl

theorem cell23_4487500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_4487500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487500 prefixEnd_4487500 := by exact prefixLift 4487500
  have htrace : WordTrace (prefixWord ++ tailWord_4487500) baseStart_4487500 baseEnd_4487500 := by
    simpa [prefixWord, tailWord_4487500, baseEnd_4487500] using wordTrace_append hprefix tailTrace_4487500
  have hstable : (prefixWord ++ tailWord_4487500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487500).length < 2 ^ (prefixWord ++ tailWord_4487500).sum := by decide
  have hdescent : baseEnd_4487500 < baseStart_4487500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487503 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 7]
def baseStart_4487503 : Nat := 118140960795 + 4487503 * 2 ^ 59
def prefixEnd_4487503 : Nat := 4983230072969 + 3 ^ 40 * 4487503 * 2
def baseEnd_4487503 : Nat := 256027330832584595286095

theorem tailTrace_4487503 : CollatzResearch.WordTrace tailWord_4487503 prefixEnd_4487503 256027330832584595286095 := by
  unfold tailWord_4487503
  simp only [CollatzResearch.WordTrace]
  refine ⟨163672680661550510340931163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109115120441033673560620775 163672680661550510340931163)
  ·
    refine ⟨245509020992325765511396745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163672680661550510340931163 245509020992325765511396745)
    ·
      refine ⟨184131765744244324133547559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245509020992325765511396745 184131765744244324133547559)
      ·
        refine ⟨276197648616366486200321339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184131765744244324133547559 276197648616366486200321339)
        ·
          refine ⟨414296472924549729300482009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276197648616366486200321339 414296472924549729300482009)
          ·
            refine ⟨310722354693412296975361507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414296472924549729300482009 310722354693412296975361507)
            ·
              refine ⟨466083532040118445463042261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310722354693412296975361507 466083532040118445463042261)
              ·
                refine ⟨10923832782190276065540053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 466083532040118445463042261 10923832782190276065540053)
                ·
                  refine ⟨256027330832584595286095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10923832782190276065540053 256027330832584595286095)
                  ·
                    rfl

theorem cell23_4487503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 7].length) (baseStart_4487503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487503 prefixEnd_4487503 := by exact prefixLift 4487503
  have htrace : WordTrace (prefixWord ++ tailWord_4487503) baseStart_4487503 baseEnd_4487503 := by
    simpa [prefixWord, tailWord_4487503, baseEnd_4487503] using wordTrace_append hprefix tailTrace_4487503
  have hstable : (prefixWord ++ tailWord_4487503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487503).length < 2 ^ (prefixWord ++ tailWord_4487503).sum := by decide
  have hdescent : baseEnd_4487503 < baseStart_4487503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487560 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4487560 : Nat := 118140960795 + 4487560 * 2 ^ 59
def prefixEnd_4487560 : Nat := 4983230072969 + 3 ^ 40 * 4487560 * 2
def baseEnd_4487560 : Nat := 2304275245890567634562093

theorem tailTrace_4487560 : CollatzResearch.WordTrace tailWord_4487560 prefixEnd_4487560 2304275245890567634562093 := by
  unfold tailWord_4487560
  simp only [CollatzResearch.WordTrace]
  refine ⟨81837379811172004537878067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109116506414896006050504089 81837379811172004537878067)
  ·
    refine ⟨122756069716758006806817101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81837379811172004537878067 122756069716758006806817101)
    ·
      refine ⟨46033526143784252552556413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122756069716758006806817101 46033526143784252552556413)
      ·
        refine ⟨17262572303919094707208655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46033526143784252552556413 17262572303919094707208655)
        ·
          refine ⟨25893858455878642060812983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17262572303919094707208655 25893858455878642060812983)
          ·
            refine ⟨38840787683817963091219475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25893858455878642060812983 38840787683817963091219475)
            ·
              refine ⟨58261181525726944636829213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38840787683817963091219475 58261181525726944636829213)
              ·
                refine ⟨21847943072147604238810955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58261181525726944636829213 21847943072147604238810955)
                ·
                  refine ⟨32771914608221406358216433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21847943072147604238810955 32771914608221406358216433)
                  ·
                    refine ⟨24578935956166054768662325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32771914608221406358216433 24578935956166054768662325)
                    ·
                      refine ⟨2304275245890567634562093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24578935956166054768662325 2304275245890567634562093)
                      ·
                        rfl

theorem cell23_4487560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4487560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487560 prefixEnd_4487560 := by exact prefixLift 4487560
  have htrace : WordTrace (prefixWord ++ tailWord_4487560) baseStart_4487560 baseEnd_4487560 := by
    simpa [prefixWord, tailWord_4487560, baseEnd_4487560] using wordTrace_append hprefix tailTrace_4487560
  have hstable : (prefixWord ++ tailWord_4487560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487560).length < 2 ^ (prefixWord ++ tailWord_4487560).sum := by decide
  have hdescent : baseEnd_4487560 < baseStart_4487560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487587 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 4]
def baseStart_4487587 : Nat := 118140960795 + 4487587 * 2 ^ 59
def prefixEnd_4487587 : Nat := 4983230072969 + 3 ^ 40 * 4487587 * 2
def baseEnd_4487587 : Nat := 2304289109868239028924469

theorem tailTrace_4487587 : CollatzResearch.WordTrace tailWord_4487587 prefixEnd_4487587 2304289109868239028924469 := by
  unfold tailWord_4487587
  simp only [CollatzResearch.WordTrace]
  refine ⟨163675744393246192686989015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109117162928830795124659343 163675744393246192686989015)
  ·
    refine ⟨245513616589869289030483523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163675744393246192686989015 245513616589869289030483523)
    ·
      refine ⟨368270424884803933545725285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245513616589869289030483523 368270424884803933545725285)
      ·
        refine ⟨69050704665900737539823491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 368270424884803933545725285 69050704665900737539823491)
        ·
          refine ⟨103576056998851106309735237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69050704665900737539823491 103576056998851106309735237)
          ·
            refine ⟨19420510687284582433075357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103576056998851106309735237 19420510687284582433075357)
            ·
              refine ⟨7282691507731718412403259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19420510687284582433075357 7282691507731718412403259)
              ·
                refine ⟨10924037261597577618604889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282691507731718412403259 10924037261597577618604889)
                ·
                  refine ⟨8193027946198183213953667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10924037261597577618604889 8193027946198183213953667)
                  ·
                    refine ⟨12289541919297274820930501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8193027946198183213953667 12289541919297274820930501)
                    ·
                      refine ⟨2304289109868239028924469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12289541919297274820930501 2304289109868239028924469)
                      ·
                        rfl

theorem cell23_4487587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_4487587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487587 prefixEnd_4487587 := by exact prefixLift 4487587
  have htrace : WordTrace (prefixWord ++ tailWord_4487587) baseStart_4487587 baseEnd_4487587 := by
    simpa [prefixWord, tailWord_4487587, baseEnd_4487587] using wordTrace_append hprefix tailTrace_4487587
  have hstable : (prefixWord ++ tailWord_4487587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487587).length < 2 ^ (prefixWord ++ tailWord_4487587).sum := by decide
  have hdescent : baseEnd_4487587 < baseStart_4487587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487630 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_4487630 : Nat := 118140960795 + 4487630 * 2 ^ 59
def prefixEnd_4487630 : Nat := 4983230072969 + 3 ^ 40 * 4487630 * 2
def baseEnd_4487630 : Nat := 2304311189536382360686771

theorem tailTrace_4487630 : CollatzResearch.WordTrace tailWord_4487630 prefixEnd_4487630 2304311189536382360686771 := by
  unfold tailWord_4487630
  simp only [CollatzResearch.WordTrace]
  refine ⟨20459664091511301378850543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109118208488060274020536229 20459664091511301378850543)
  ·
    refine ⟨30689496137266952068275815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20459664091511301378850543 30689496137266952068275815)
    ·
      refine ⟨46034244205900428102413723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30689496137266952068275815 46034244205900428102413723)
      ·
        refine ⟨69051366308850642153620585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46034244205900428102413723 69051366308850642153620585)
        ·
          refine ⟨51788524731637981615215439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69051366308850642153620585 51788524731637981615215439)
          ·
            refine ⟨77682787097456972422823159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51788524731637981615215439 77682787097456972422823159)
            ·
              refine ⟨116524180646185458634234739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77682787097456972422823159 116524180646185458634234739)
              ·
                refine ⟨174786270969278187951352109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116524180646185458634234739 174786270969278187951352109)
                ·
                  refine ⟨65544851613479320481757041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174786270969278187951352109 65544851613479320481757041)
                  ·
                    refine ⟨49158638710109490361317781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65544851613479320481757041 49158638710109490361317781)
                    ·
                      refine ⟨2304311189536382360686771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49158638710109490361317781 2304311189536382360686771)
                      ·
                        rfl

theorem cell23_4487630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_4487630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487630 prefixEnd_4487630 := by exact prefixLift 4487630
  have htrace : WordTrace (prefixWord ++ tailWord_4487630) baseStart_4487630 baseEnd_4487630 := by
    simpa [prefixWord, tailWord_4487630, baseEnd_4487630] using wordTrace_append hprefix tailTrace_4487630
  have hstable : (prefixWord ++ tailWord_4487630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487630).length < 2 ^ (prefixWord ++ tailWord_4487630).sum := by decide
  have hdescent : baseEnd_4487630 < baseStart_4487630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487664 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 2, 3, 2]
def baseStart_4487664 : Nat := 118140960795 + 4487664 * 2 ^ 59
def prefixEnd_4487664 : Nat := 4983230072969 + 3 ^ 40 * 4487664 * 2
def baseEnd_4487664 : Nat := 2304328647878635227661615

theorem tailTrace_4487664 : CollatzResearch.WordTrace tailWord_4487664 prefixEnd_4487664 2304328647878635227661615 := by
  unfold tailWord_4487664
  simp only [CollatzResearch.WordTrace]
  refine ⟨81839276406983617418771023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109119035209311489891694697 81839276406983617418771023)
  ·
    refine ⟨122758914610475426128156535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81839276406983617418771023 122758914610475426128156535)
    ·
      refine ⟨184138371915713139192234803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122758914610475426128156535 184138371915713139192234803)
      ·
        refine ⟨276207557873569708788352205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184138371915713139192234803 276207557873569708788352205)
        ·
          refine ⟨103577834202588640795632077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276207557873569708788352205 103577834202588640795632077)
          ·
            refine ⟨38841687825970740298362029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103577834202588640795632077 38841687825970740298362029)
            ·
              refine ⟨14565632934739027611885761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38841687825970740298362029 14565632934739027611885761)
              ·
                refine ⟨10924224701054270708914321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14565632934739027611885761 10924224701054270708914321)
                ·
                  refine ⟨8193168525790703031685741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10924224701054270708914321 8193168525790703031685741)
                  ·
                    refine ⟨3072438197171513636882153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8193168525790703031685741 3072438197171513636882153)
                    ·
                      refine ⟨2304328647878635227661615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072438197171513636882153 2304328647878635227661615)
                      ·
                        rfl

theorem cell23_4487664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 3, 2].length) (baseStart_4487664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487664 prefixEnd_4487664 := by exact prefixLift 4487664
  have htrace : WordTrace (prefixWord ++ tailWord_4487664) baseStart_4487664 baseEnd_4487664 := by
    simpa [prefixWord, tailWord_4487664, baseEnd_4487664] using wordTrace_append hprefix tailTrace_4487664
  have hstable : (prefixWord ++ tailWord_4487664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487664).length < 2 ^ (prefixWord ++ tailWord_4487664).sum := by decide
  have hdescent : baseEnd_4487664 < baseStart_4487664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487677 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4487677 : Nat := 118140960795 + 4487677 * 2 ^ 59
def prefixEnd_4487677 : Nat := 4983230072969 + 3 ^ 40 * 4487677 * 2
def baseEnd_4487677 : Nat := 2304335323127143676799055

theorem tailTrace_4487677 : CollatzResearch.WordTrace tailWord_4487677 prefixEnd_4487677 2304335323127143676799055 := by
  unfold tailWord_4487677
  simp only [CollatzResearch.WordTrace]
  refine ⟨163679026962920138057765285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109119351308613425371843523 163679026962920138057765285)
  ·
    refine ⟨30689817555547525885830991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163679026962920138057765285 30689817555547525885830991)
    ·
      refine ⟨46034726333321288828746487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30689817555547525885830991 46034726333321288828746487)
      ·
        refine ⟨69052089499981933243119731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46034726333321288828746487 69052089499981933243119731)
        ·
          refine ⟨103578134249972899864679597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69052089499981933243119731 103578134249972899864679597)
          ·
            refine ⟨38841800343739837449254849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103578134249972899864679597 38841800343739837449254849)
            ·
              refine ⟨29131350257804878086941137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38841800343739837449254849 29131350257804878086941137)
              ·
                refine ⟨21848512693353658565205853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29131350257804878086941137 21848512693353658565205853)
                ·
                  refine ⟨8193192260007621961952195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21848512693353658565205853 8193192260007621961952195)
                  ·
                    refine ⟨12289788390011432942928293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8193192260007621961952195 12289788390011432942928293)
                    ·
                      refine ⟨2304335323127143676799055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12289788390011432942928293 2304335323127143676799055)
                      ·
                        rfl

theorem cell23_4487677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4487677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487677 prefixEnd_4487677 := by exact prefixLift 4487677
  have htrace : WordTrace (prefixWord ++ tailWord_4487677) baseStart_4487677 baseEnd_4487677 := by
    simpa [prefixWord, tailWord_4487677, baseEnd_4487677] using wordTrace_append hprefix tailTrace_4487677
  have hstable : (prefixWord ++ tailWord_4487677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487677).length < 2 ^ (prefixWord ++ tailWord_4487677).sum := by decide
  have hdescent : baseEnd_4487677 < baseStart_4487677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487694 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4487694 : Nat := 118140960795 + 4487694 * 2 ^ 59
def prefixEnd_4487694 : Nat := 4983230072969 + 3 ^ 40 * 4487694 * 2
def baseEnd_4487694 : Nat := 2304344052298270110286477

theorem tailTrace_4487694 : CollatzResearch.WordTrace tailWord_4487694 prefixEnd_4487694 2304344052298270110286477 := by
  unfold tailWord_4487694
  simp only [CollatzResearch.WordTrace]
  refine ⟨20459955875482318745141767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109119764669239033307422757 20459955875482318745141767)
  ·
    refine ⟨30689933813223478117712651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20459955875482318745141767 30689933813223478117712651)
    ·
      refine ⟨46034900719835217176568977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30689933813223478117712651 46034900719835217176568977)
      ·
        refine ⟨34526175539876412882426733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46034900719835217176568977 34526175539876412882426733)
        ·
          refine ⟨12947315827453654830910025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34526175539876412882426733 12947315827453654830910025)
          ·
            refine ⟨9710486870590241123182519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12947315827453654830910025 9710486870590241123182519)
            ·
              refine ⟨14565730305885361684773779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9710486870590241123182519 14565730305885361684773779)
              ·
                refine ⟨21848595458828042527160669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14565730305885361684773779 21848595458828042527160669)
                ·
                  refine ⟨8193223297060515947685251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21848595458828042527160669 8193223297060515947685251)
                  ·
                    refine ⟨12289834945590773921527877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8193223297060515947685251 12289834945590773921527877)
                    ·
                      refine ⟨2304344052298270110286477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12289834945590773921527877 2304344052298270110286477)
                      ·
                        rfl

theorem cell23_4487694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4487694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487694 prefixEnd_4487694 := by exact prefixLift 4487694
  have htrace : WordTrace (prefixWord ++ tailWord_4487694) baseStart_4487694 baseEnd_4487694 := by
    simpa [prefixWord, tailWord_4487694, baseEnd_4487694] using wordTrace_append hprefix tailTrace_4487694
  have hstable : (prefixWord ++ tailWord_4487694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487694).length < 2 ^ (prefixWord ++ tailWord_4487694).sum := by decide
  have hdescent : baseEnd_4487694 < baseStart_4487694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487734 : List Nat := [5, 1, 2, 1, 2, 1, 3, 8]
def baseStart_4487734 : Nat := 118140960795 + 4487734 * 2 ^ 59
def prefixEnd_4487734 : Nat := 4983230072969 + 3 ^ 40 * 4487734 * 2
def baseEnd_4487734 : Nat := 85346836723127776066159

theorem tailTrace_4487734 : CollatzResearch.WordTrace tailWord_4487734 prefixEnd_4487734 85346836723127776066159 := by
  unfold tailWord_4487734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10230069120232102299536891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109120737282475757861726837 10230069120232102299536891)
  ·
    refine ⟨15345103680348153449305337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10230069120232102299536891 15345103680348153449305337)
    ·
      refine ⟨11508827760261115086979003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15345103680348153449305337 11508827760261115086979003)
      ·
        refine ⟨17263241640391672630468505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11508827760261115086979003 17263241640391672630468505)
        ·
          refine ⟨12947431230293754472851379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17263241640391672630468505 12947431230293754472851379)
          ·
            refine ⟨19421146845440631709277069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12947431230293754472851379 19421146845440631709277069)
            ·
              refine ⟨7282930067040236890978901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19421146845440631709277069 7282930067040236890978901)
              ·
                refine ⟨85346836723127776066159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7282930067040236890978901 85346836723127776066159)
                ·
                  rfl

theorem cell23_4487734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_4487734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487734 prefixEnd_4487734 := by exact prefixLift 4487734
  have htrace : WordTrace (prefixWord ++ tailWord_4487734) baseStart_4487734 baseEnd_4487734 := by
    simpa [prefixWord, tailWord_4487734, baseEnd_4487734] using wordTrace_append hprefix tailTrace_4487734
  have hstable : (prefixWord ++ tailWord_4487734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487734).length < 2 ^ (prefixWord ++ tailWord_4487734).sum := by decide
  have hdescent : baseEnd_4487734 < baseStart_4487734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487777 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 2, 6]
def baseStart_4487777 : Nat := 118140960795 + 4487777 * 2 ^ 59
def prefixEnd_4487777 : Nat := 4983230072969 + 3 ^ 40 * 4487777 * 2
def baseEnd_4487777 : Nat := 768128890397531095182865

theorem tailTrace_4487777 : CollatzResearch.WordTrace tailWord_4487777 prefixEnd_4487777 768128890397531095182865 := by
  unfold tailWord_4487777
  simp only [CollatzResearch.WordTrace]
  refine ⟨163682674262557855136405585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109121782841705236757603723 163682674262557855136405585)
  ·
    refine ⟨122762005696918391352304189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163682674262557855136405585 122762005696918391352304189)
    ·
      refine ⟨46035752136344396757114071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122762005696918391352304189 46035752136344396757114071)
      ·
        refine ⟨69053628204516595135671107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46035752136344396757114071 69053628204516595135671107)
        ·
          refine ⟨103580442306774892703506661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69053628204516595135671107 103580442306774892703506661)
          ·
            refine ⟨19421332932520292381907499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103580442306774892703506661 19421332932520292381907499)
            ·
              refine ⟨29131999398780438572861249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19421332932520292381907499 29131999398780438572861249)
              ·
                refine ⟨21848999549085328929645937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29131999398780438572861249 21848999549085328929645937)
                ·
                  refine ⟨16386749661813996697234453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21848999549085328929645937 16386749661813996697234453)
                  ·
                    refine ⟨768128890397531095182865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16386749661813996697234453 768128890397531095182865)
                    ·
                      rfl

theorem cell23_4487777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_4487777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487777 prefixEnd_4487777 := by exact prefixLift 4487777
  have htrace : WordTrace (prefixWord ++ tailWord_4487777) baseStart_4487777 baseEnd_4487777 := by
    simpa [prefixWord, tailWord_4487777, baseEnd_4487777] using wordTrace_append hprefix tailTrace_4487777
  have hstable : (prefixWord ++ tailWord_4487777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487777).length < 2 ^ (prefixWord ++ tailWord_4487777).sum := by decide
  have hdescent : baseEnd_4487777 < baseStart_4487777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487787 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 3]
def baseStart_4487787 : Nat := 118140960795 + 4487787 * 2 ^ 59
def prefixEnd_4487787 : Nat := 4983230072969 + 3 ^ 40 * 4487787 * 2
def baseEnd_4487787 : Nat := 2304391805999138246423549

theorem tailTrace_4487787 : CollatzResearch.WordTrace tailWord_4487787 prefixEnd_4487787 2304391805999138246423549 := by
  unfold tailWord_4487787
  simp only [CollatzResearch.WordTrace]
  refine ⟨163683038992521626844269615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109122025995014417896179743 163683038992521626844269615)
  ·
    refine ⟨245524558488782440266404423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163683038992521626844269615 245524558488782440266404423)
    ·
      refine ⟨368286837733173660399606635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245524558488782440266404423 368286837733173660399606635)
      ·
        refine ⟨552430256599760490599409953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368286837733173660399606635 552430256599760490599409953)
        ·
          refine ⟨414322692449820367949557465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552430256599760490599409953 414322692449820367949557465)
          ·
            refine ⟨310742019337365275962168099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414322692449820367949557465 310742019337365275962168099)
            ·
              refine ⟨466113029006047913943252149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310742019337365275962168099 466113029006047913943252149)
              ·
                refine ⟨43698096469316991932179889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466113029006047913943252149 43698096469316991932179889)
                ·
                  refine ⟨32773572351987743949134917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43698096469316991932179889 32773572351987743949134917)
                  ·
                    refine ⟨6145044815997701990462797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32773572351987743949134917 6145044815997701990462797)
                    ·
                      refine ⟨2304391805999138246423549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145044815997701990462797 2304391805999138246423549)
                      ·
                        rfl

theorem cell23_4487787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 3].length) (baseStart_4487787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487787 prefixEnd_4487787 := by exact prefixLift 4487787
  have htrace : WordTrace (prefixWord ++ tailWord_4487787) baseStart_4487787 baseEnd_4487787 := by
    simpa [prefixWord, tailWord_4487787, baseEnd_4487787] using wordTrace_append hprefix tailTrace_4487787
  have hstable : (prefixWord ++ tailWord_4487787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487787).length < 2 ^ (prefixWord ++ tailWord_4487787).sum := by decide
  have hdescent : baseEnd_4487787 < baseStart_4487787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487801 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 1, 4, 2]
def baseStart_4487801 : Nat := 118140960795 + 4487801 * 2 ^ 59
def prefixEnd_4487801 : Nat := 4983230072969 + 3 ^ 40 * 4487801 * 2
def baseEnd_4487801 : Nat := 2304398994728301191648485

theorem tailTrace_4487801 : CollatzResearch.WordTrace tailWord_4487801 prefixEnd_4487801 2304398994728301191648485 := by
  unfold tailWord_4487801
  simp only [CollatzResearch.WordTrace]
  refine ⟨163683549614470907235279257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109122366409647271490186171 163683549614470907235279257)
  ·
    refine ⟨122762662210853180426459443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163683549614470907235279257 122762662210853180426459443)
    ·
      refine ⟨184143993316279770639689165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122762662210853180426459443 184143993316279770639689165)
      ·
        refine ⟨69053997493604913989883437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184143993316279770639689165 69053997493604913989883437)
        ·
          refine ⟨25895249060101842746206289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69053997493604913989883437 25895249060101842746206289)
          ·
            refine ⟨19421436795076382059654717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25895249060101842746206289 19421436795076382059654717)
            ·
              refine ⟨7283038798153643272370519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19421436795076382059654717 7283038798153643272370519)
              ·
                refine ⟨10924558197230464908555779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7283038798153643272370519 10924558197230464908555779)
                ·
                  refine ⟨16386837295845697362833669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10924558197230464908555779 16386837295845697362833669)
                  ·
                    refine ⟨3072531992971068255531313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16386837295845697362833669 3072531992971068255531313)
                    ·
                      refine ⟨2304398994728301191648485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072531992971068255531313 2304398994728301191648485)
                      ·
                        rfl

theorem cell23_4487801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_4487801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487801 prefixEnd_4487801 := by exact prefixLift 4487801
  have htrace : WordTrace (prefixWord ++ tailWord_4487801) baseStart_4487801 baseEnd_4487801 := by
    simpa [prefixWord, tailWord_4487801, baseEnd_4487801] using wordTrace_append hprefix tailTrace_4487801
  have hstable : (prefixWord ++ tailWord_4487801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487801).length < 2 ^ (prefixWord ++ tailWord_4487801).sum := by decide
  have hdescent : baseEnd_4487801 < baseStart_4487801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487841 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 7]
def baseStart_4487841 : Nat := 118140960795 + 4487841 * 2 ^ 59
def prefixEnd_4487841 : Nat := 4983230072969 + 3 ^ 40 * 4487841 * 2
def baseEnd_4487841 : Nat := 256046614883831226127589

theorem tailTrace_4487841 : CollatzResearch.WordTrace tailWord_4487841 prefixEnd_4487841 256046614883831226127589 := by
  unfold tailWord_4487841
  simp only [CollatzResearch.WordTrace]
  refine ⟨163685008534325994066735377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109123339022883996044490251 163685008534325994066735377)
  ·
    refine ⟨122763756400744495550051533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163685008534325994066735377 122763756400744495550051533)
    ·
      refine ⟨46036408650279185831269325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122763756400744495550051533 46036408650279185831269325)
      ·
        refine ⟨17263653243854694686725997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46036408650279185831269325 17263653243854694686725997)
        ·
          refine ⟨6473869966445510507522249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17263653243854694686725997 6473869966445510507522249)
          ·
            refine ⟨4855402474834132880641687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6473869966445510507522249 4855402474834132880641687)
            ·
              refine ⟨7283103712251199320962531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4855402474834132880641687 7283103712251199320962531)
              ·
                refine ⟨10924655568376798981443797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7283103712251199320962531 10924655568376798981443797)
                ·
                  refine ⟨256046614883831226127589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10924655568376798981443797 256046614883831226127589)
                  ·
                    rfl

theorem cell23_4487841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 7].length) (baseStart_4487841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487841 prefixEnd_4487841 := by exact prefixLift 4487841
  have htrace : WordTrace (prefixWord ++ tailWord_4487841) baseStart_4487841 baseEnd_4487841 := by
    simpa [prefixWord, tailWord_4487841, baseEnd_4487841] using wordTrace_append hprefix tailTrace_4487841
  have hstable : (prefixWord ++ tailWord_4487841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487841).length < 2 ^ (prefixWord ++ tailWord_4487841).sum := by decide
  have hdescent : baseEnd_4487841 < baseStart_4487841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487877 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_4487877 : Nat := 118140960795 + 4487877 * 2 ^ 59
def prefixEnd_4487877 : Nat := 4983230072969 + 3 ^ 40 * 4487877 * 2
def baseEnd_4487877 : Nat := 2304438019258042894298135

theorem tailTrace_4487877 : CollatzResearch.WordTrace tailWord_4487877 prefixEnd_4487877 2304438019258042894298135 := by
  unfold tailWord_4487877
  simp only [CollatzResearch.WordTrace]
  refine ⟨163686321562195572215045885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109124214374797048143363923 163686321562195572215045885)
  ·
    refine ⟨61382370585823339580642207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163686321562195572215045885 61382370585823339580642207)
    ·
      refine ⟨92073555878735009370963311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61382370585823339580642207 92073555878735009370963311)
      ·
        refine ⟨138110333818102514056444967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92073555878735009370963311 138110333818102514056444967)
        ·
          refine ⟨207165500727153771084667451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138110333818102514056444967 207165500727153771084667451)
          ·
            refine ⟨310748251090730656627001177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207165500727153771084667451 310748251090730656627001177)
            ·
              refine ⟨233061188318047992470250883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310748251090730656627001177 233061188318047992470250883)
              ·
                refine ⟨349591782477071988705376325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233061188318047992470250883 349591782477071988705376325)
                ·
                  refine ⟨65548459214450997882258061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 349591782477071988705376325 65548459214450997882258061)
                  ·
                    refine ⟨24580672205419124205846773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65548459214450997882258061 24580672205419124205846773)
                    ·
                      refine ⟨2304438019258042894298135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24580672205419124205846773 2304438019258042894298135)
                      ·
                        rfl

theorem cell23_4487877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_4487877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487877 prefixEnd_4487877 := by exact prefixLift 4487877
  have htrace : WordTrace (prefixWord ++ tailWord_4487877) baseStart_4487877 baseEnd_4487877 := by
    simpa [prefixWord, tailWord_4487877, baseEnd_4487877] using wordTrace_append hprefix tailTrace_4487877
  have hstable : (prefixWord ++ tailWord_4487877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487877).length < 2 ^ (prefixWord ++ tailWord_4487877).sum := by decide
  have hdescent : baseEnd_4487877 < baseStart_4487877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487892 : List Nat := [2, 4, 1, 3, 3, 1, 2, 2, 5]
def baseStart_4487892 : Nat := 118140960795 + 4487892 * 2 ^ 59
def prefixEnd_4487892 : Nat := 4983230072969 + 3 ^ 40 * 4487892 * 2
def baseEnd_4487892 : Nat := 256049524607540037290063

theorem tailTrace_4487892 : CollatzResearch.WordTrace tailWord_4487892 prefixEnd_4487892 256049524607540037290063 := by
  unfold tailWord_4487892
  simp only [CollatzResearch.WordTrace]
  refine ⟨81843434328570614888420965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109124579104760819851227953 81843434328570614888420965)
  ·
    refine ⟨15345643936606990291578931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81843434328570614888420965 15345643936606990291578931)
    ·
      refine ⟨23018465904910485437368397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15345643936606990291578931 23018465904910485437368397)
      ·
        refine ⟨8631924714341432039013149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23018465904910485437368397 8631924714341432039013149)
        ·
          refine ⟨3236971767878037014629931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8631924714341432039013149 3236971767878037014629931)
          ·
            refine ⟨4855457651817055521944897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236971767878037014629931 4855457651817055521944897)
            ·
              refine ⟨3641593238862791641458673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855457651817055521944897 3641593238862791641458673)
              ·
                refine ⟨2731194929147093731094005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3641593238862791641458673 2731194929147093731094005)
                ·
                  refine ⟨256049524607540037290063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731194929147093731094005 256049524607540037290063)
                  ·
                    rfl

theorem cell23_4487892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_4487892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487892 prefixEnd_4487892 := by exact prefixLift 4487892
  have htrace : WordTrace (prefixWord ++ tailWord_4487892) baseStart_4487892 baseEnd_4487892 := by
    simpa [prefixWord, tailWord_4487892, baseEnd_4487892] using wordTrace_append hprefix tailTrace_4487892
  have hstable : (prefixWord ++ tailWord_4487892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487892).length < 2 ^ (prefixWord ++ tailWord_4487892).sum := by decide
  have hdescent : baseEnd_4487892 < baseStart_4487892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487925 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4487925 : Nat := 118140960795 + 4487925 * 2 ^ 59
def prefixEnd_4487925 : Nat := 4983230072969 + 3 ^ 40 * 4487925 * 2
def baseEnd_4487925 : Nat := 2304462666329458706497915

theorem tailTrace_4487925 : CollatzResearch.WordTrace tailWord_4487925 prefixEnd_4487925 2304462666329458706497915 := by
  unfold tailWord_4487925
  simp only [CollatzResearch.WordTrace]
  refine ⟨163688072266021676412793229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109125381510681117608528819 163688072266021676412793229)
  ·
    refine ⟨61383027099758128654797461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163688072266021676412793229 61383027099758128654797461)
    ·
      refine ⟨2877329395301162280693631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61383027099758128654797461 2877329395301162280693631)
      ·
        refine ⟨4315994092951743421040447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877329395301162280693631 4315994092951743421040447)
        ·
          refine ⟨6473991139427615131560671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315994092951743421040447 6473991139427615131560671)
          ·
            refine ⟨9710986709141422697341007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6473991139427615131560671 9710986709141422697341007)
            ·
              refine ⟨14566480063712134046011511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9710986709141422697341007 14566480063712134046011511)
              ·
                refine ⟨21849720095568201069017267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14566480063712134046011511 21849720095568201069017267)
                ·
                  refine ⟨32774580143352301603525901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21849720095568201069017267 32774580143352301603525901)
                  ·
                    refine ⟨12290467553757113101322213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32774580143352301603525901 12290467553757113101322213)
                    ·
                      refine ⟨2304462666329458706497915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12290467553757113101322213 2304462666329458706497915)
                      ·
                        rfl

theorem cell23_4487925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4487925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487925 prefixEnd_4487925 := by exact prefixLift 4487925
  have htrace : WordTrace (prefixWord ++ tailWord_4487925) baseStart_4487925 baseEnd_4487925 := by
    simpa [prefixWord, tailWord_4487925, baseEnd_4487925] using wordTrace_append hprefix tailTrace_4487925
  have hstable : (prefixWord ++ tailWord_4487925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487925).length < 2 ^ (prefixWord ++ tailWord_4487925).sum := by decide
  have hdescent : baseEnd_4487925 < baseStart_4487925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487951 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 4, 3, 2]
def baseStart_4487951 : Nat := 118140960795 + 4487951 * 2 ^ 59
def prefixEnd_4487951 : Nat := 4983230072969 + 3 ^ 40 * 4487951 * 2
def baseEnd_4487951 : Nat := 2304476016826475604772795

theorem tailTrace_4487951 : CollatzResearch.WordTrace tailWord_4487951 prefixEnd_4487951 2304476016826475604772795 := by
  unfold tailWord_4487951
  simp only [CollatzResearch.WordTrace]
  refine ⟨163689020563927482853239707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109126013709284988568826471 163689020563927482853239707)
  ·
    refine ⟨245533530845891224279859561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163689020563927482853239707 245533530845891224279859561)
    ·
      refine ⟨184150148134418418209894671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245533530845891224279859561 184150148134418418209894671)
      ·
        refine ⟨276225222201627627314842007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184150148134418418209894671 276225222201627627314842007)
        ·
          refine ⟨414337833302441440972263011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276225222201627627314842007 414337833302441440972263011)
          ·
            refine ⟨621506749953662161458394517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414337833302441440972263011 621506749953662161458394517)
            ·
              refine ⟨29133128904077913818362243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 621506749953662161458394517 29133128904077913818362243)
              ·
                refine ⟨43699693356116870727543365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29133128904077913818362243 43699693356116870727543365)
                ·
                  refine ⟨8193692504271913261414381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43699693356116870727543365 8193692504271913261414381)
                  ·
                    refine ⟨3072634689101967473030393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8193692504271913261414381 3072634689101967473030393)
                    ·
                      refine ⟨2304476016826475604772795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072634689101967473030393 2304476016826475604772795)
                      ·
                        rfl

theorem cell23_4487951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3, 2].length) (baseStart_4487951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487951 prefixEnd_4487951 := by exact prefixLift 4487951
  have htrace : WordTrace (prefixWord ++ tailWord_4487951) baseStart_4487951 baseEnd_4487951 := by
    simpa [prefixWord, tailWord_4487951, baseEnd_4487951] using wordTrace_append hprefix tailTrace_4487951
  have hstable : (prefixWord ++ tailWord_4487951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487951).length < 2 ^ (prefixWord ++ tailWord_4487951).sum := by decide
  have hdescent : baseEnd_4487951 < baseStart_4487951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487965 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 6]
def baseStart_4487965 : Nat := 118140960795 + 4487965 * 2 ^ 59
def prefixEnd_4487965 : Nat := 4983230072969 + 3 ^ 40 * 4487965 * 2
def baseEnd_4487965 : Nat := 256053689506182061110859

theorem tailTrace_4487965 : CollatzResearch.WordTrace tailWord_4487965 prefixEnd_4487965 256053689506182061110859 := by
  unfold tailWord_4487965
  simp only [CollatzResearch.WordTrace]
  refine ⟨163689531185876763244249349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109126354123917842162832899 163689531185876763244249349)
  ·
    refine ⟨30691787097351893108296753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163689531185876763244249349 30691787097351893108296753)
    ·
      refine ⟨23018840323013919831222565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30691787097351893108296753 23018840323013919831222565)
      ·
        refine ⟨4316032560565109968354231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23018840323013919831222565 4316032560565109968354231)
        ·
          refine ⟨6474048840847664952531347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316032560565109968354231 6474048840847664952531347)
          ·
            refine ⟨9711073261271497428797021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6474048840847664952531347 9711073261271497428797021)
            ·
              refine ⟨3641652472976811535798883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9711073261271497428797021 3641652472976811535798883)
              ·
                refine ⟨5462478709465217303698325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641652472976811535798883 5462478709465217303698325)
                ·
                  refine ⟨256053689506182061110859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5462478709465217303698325 256053689506182061110859)
                  ·
                    rfl

theorem cell23_4487965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_4487965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487965 prefixEnd_4487965 := by exact prefixLift 4487965
  have htrace : WordTrace (prefixWord ++ tailWord_4487965) baseStart_4487965 baseEnd_4487965 := by
    simpa [prefixWord, tailWord_4487965, baseEnd_4487965] using wordTrace_append hprefix tailTrace_4487965
  have hstable : (prefixWord ++ tailWord_4487965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487965).length < 2 ^ (prefixWord ++ tailWord_4487965).sum := by decide
  have hdescent : baseEnd_4487965 < baseStart_4487965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4487984 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3]
def baseStart_4487984 : Nat := 118140960795 + 4487984 * 2 ^ 59
def prefixEnd_4487984 : Nat := 4983230072969 + 3 ^ 40 * 4487984 * 2
def baseEnd_4487984 : Nat := 2304492961688073975660143

theorem tailTrace_4487984 : CollatzResearch.WordTrace tailWord_4487984 prefixEnd_4487984 2304492961688073975660143 := by
  unfold tailWord_4487984
  simp only [CollatzResearch.WordTrace]
  refine ⟨81845112086403964744595503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109126816115205286326127337 81845112086403964744595503)
  ·
    refine ⟨122767668129605947116893255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81845112086403964744595503 122767668129605947116893255)
    ·
      refine ⟨184151502194408920675339883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122767668129605947116893255 184151502194408920675339883)
      ·
        refine ⟨276227253291613381013009825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184151502194408920675339883 276227253291613381013009825)
        ·
          refine ⟨207170439968710035759757369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276227253291613381013009825 207170439968710035759757369)
          ·
            refine ⟨155377829976532526819818027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207170439968710035759757369 155377829976532526819818027)
            ·
              refine ⟨233066744964798790229727041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155377829976532526819818027 233066744964798790229727041)
              ·
                refine ⟨174800058723599092672295281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233066744964798790229727041 174800058723599092672295281)
                ·
                  refine ⟨131100044042699319504221461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174800058723599092672295281 131100044042699319504221461)
                  ·
                    refine ⟨6145314564501530601760381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131100044042699319504221461 6145314564501530601760381)
                    ·
                      refine ⟨2304492961688073975660143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145314564501530601760381 2304492961688073975660143)
                      ·
                        rfl

theorem cell23_4487984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_4487984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4487984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4487984 prefixEnd_4487984 := by exact prefixLift 4487984
  have htrace : WordTrace (prefixWord ++ tailWord_4487984) baseStart_4487984 baseEnd_4487984 := by
    simpa [prefixWord, tailWord_4487984, baseEnd_4487984] using wordTrace_append hprefix tailTrace_4487984
  have hstable : (prefixWord ++ tailWord_4487984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4487984).length < 2 ^ (prefixWord ++ tailWord_4487984).sum := by decide
  have hdescent : baseEnd_4487984 < baseStart_4487984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4487984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488025 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 2, 4]
def baseStart_4488025 : Nat := 118140960795 + 4488025 * 2 ^ 59
def prefixEnd_4488025 : Nat := 4983230072969 + 3 ^ 40 * 4488025 * 2
def baseEnd_4488025 : Nat := 768171338131636105082485

theorem tailTrace_4488025 : CollatzResearch.WordTrace tailWord_4488025 prefixEnd_4488025 768171338131636105082485 := by
  unfold tailWord_4488025
  simp only [CollatzResearch.WordTrace]
  refine ⟨163691719565659393491433529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109127813043772928994289019 163691719565659393491433529)
  ·
    refine ⟨122768789674244545118575147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163691719565659393491433529 122768789674244545118575147)
    ·
      refine ⟨184153184511366817677862721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122768789674244545118575147 184153184511366817677862721)
      ·
        refine ⟨138114888383525113258397041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184153184511366817677862721 138114888383525113258397041)
        ·
          refine ⟨103586166287643834943797781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138114888383525113258397041 103586166287643834943797781)
          ·
            refine ⟨4855601544733304762990521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103586166287643834943797781 4855601544733304762990521)
            ·
              refine ⟨3641701158549978572242891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855601544733304762990521 3641701158549978572242891)
              ·
                refine ⟨5462551737824967858364337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641701158549978572242891 5462551737824967858364337)
                ·
                  refine ⟨4096913803368725893773253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5462551737824967858364337 4096913803368725893773253)
                  ·
                    refine ⟨768171338131636105082485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4096913803368725893773253 768171338131636105082485)
                    ·
                      rfl

theorem cell23_4488025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 4].length) (baseStart_4488025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488025 prefixEnd_4488025 := by exact prefixLift 4488025
  have htrace : WordTrace (prefixWord ++ tailWord_4488025) baseStart_4488025 baseEnd_4488025 := by
    simpa [prefixWord, tailWord_4488025, baseEnd_4488025] using wordTrace_append hprefix tailTrace_4488025
  have hstable : (prefixWord ++ tailWord_4488025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488025).length < 2 ^ (prefixWord ++ tailWord_4488025).sum := by decide
  have hdescent : baseEnd_4488025 < baseStart_4488025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488031 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 3]
def baseStart_4488031 : Nat := 118140960795 + 4488031 * 2 ^ 59
def prefixEnd_4488031 : Nat := 4983230072969 + 3 ^ 40 * 4488031 * 2
def baseEnd_4488031 : Nat := 2304517095278835291772427

theorem tailTrace_4488031 : CollatzResearch.WordTrace tailWord_4488031 prefixEnd_4488031 2304517095278835291772427 := by
  unfold tailWord_4488031
  simp only [CollatzResearch.WordTrace]
  refine ⟨163691938403637656516151947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109127958935758437677434631 163691938403637656516151947)
  ·
    refine ⟨245537907605456484774227921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163691938403637656516151947 245537907605456484774227921)
    ·
      refine ⟨184153430704092363580670941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245537907605456484774227921 184153430704092363580670941)
      ·
        refine ⟨69057536514034636342751603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184153430704092363580670941 69057536514034636342751603)
        ·
          refine ⟨103586304771051954514127405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69057536514034636342751603 103586304771051954514127405)
          ·
            refine ⟨38844864289144482942797777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103586304771051954514127405 38844864289144482942797777)
            ·
              refine ⟨29133648216858362207098333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38844864289144482942797777 29133648216858362207098333)
              ·
                refine ⟨10925118081321885827661875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29133648216858362207098333 10925118081321885827661875)
                ·
                  refine ⟨16387677121982828741492813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10925118081321885827661875 16387677121982828741492813)
                  ·
                    refine ⟨6145378920743560778059805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16387677121982828741492813 6145378920743560778059805)
                    ·
                      refine ⟨2304517095278835291772427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145378920743560778059805 2304517095278835291772427)
                      ·
                        rfl

theorem cell23_4488031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_4488031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488031 prefixEnd_4488031 := by exact prefixLift 4488031
  have htrace : WordTrace (prefixWord ++ tailWord_4488031) baseStart_4488031 baseEnd_4488031 := by
    simpa [prefixWord, tailWord_4488031, baseEnd_4488031] using wordTrace_append hprefix tailTrace_4488031
  have hstable : (prefixWord ++ tailWord_4488031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488031).length < 2 ^ (prefixWord ++ tailWord_4488031).sum := by decide
  have hdescent : baseEnd_4488031 < baseStart_4488031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488035 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 3]
def baseStart_4488035 : Nat := 118140960795 + 4488035 * 2 ^ 59
def prefixEnd_4488035 : Nat := 4983230072969 + 3 ^ 40 * 4488035 * 2
def baseEnd_4488035 : Nat := 2304519149201453276122409

theorem tailTrace_4488035 : CollatzResearch.WordTrace tailWord_4488035 prefixEnd_4488035 2304519149201453276122409 := by
  unfold tailWord_4488035
  simp only [CollatzResearch.WordTrace]
  refine ⟨163692084295623165199297559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109128056197082110132865039 163692084295623165199297559)
  ·
    refine ⟨245538126443434747798946339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163692084295623165199297559 245538126443434747798946339)
    ·
      refine ⟨368307189665152121698419509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245538126443434747798946339 368307189665152121698419509)
      ·
        refine ⟨34528799031108011409226829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 368307189665152121698419509 34528799031108011409226829)
        ·
          refine ⟨12948299636665504278460061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34528799031108011409226829 12948299636665504278460061)
          ·
            refine ⟨4855612363749564104422523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12948299636665504278460061 4855612363749564104422523)
            ·
              refine ⟨7283418545624346156633785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4855612363749564104422523 7283418545624346156633785)
              ·
                refine ⟨5462563909218259617475339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7283418545624346156633785 5462563909218259617475339)
                ·
                  refine ⟨8193845863827389426213009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5462563909218259617475339 8193845863827389426213009)
                  ·
                    refine ⟨6145384397870542069659757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8193845863827389426213009 6145384397870542069659757)
                    ·
                      refine ⟨2304519149201453276122409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145384397870542069659757 2304519149201453276122409)
                      ·
                        rfl

theorem cell23_4488035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_4488035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488035 prefixEnd_4488035 := by exact prefixLift 4488035
  have htrace : WordTrace (prefixWord ++ tailWord_4488035) baseStart_4488035 baseEnd_4488035 := by
    simpa [prefixWord, tailWord_4488035, baseEnd_4488035] using wordTrace_append hprefix tailTrace_4488035
  have hstable : (prefixWord ++ tailWord_4488035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488035).length < 2 ^ (prefixWord ++ tailWord_4488035).sum := by decide
  have hdescent : baseEnd_4488035 < baseStart_4488035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488071 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4488071 : Nat := 118140960795 + 4488071 * 2 ^ 59
def prefixEnd_4488071 : Nat := 4983230072969 + 3 ^ 40 * 4488071 * 2
def baseEnd_4488071 : Nat := 2304537634505015135272243

theorem tailTrace_4488071 : CollatzResearch.WordTrace tailWord_4488071 prefixEnd_4488071 2304537634505015135272243 := by
  unfold tailWord_4488071
  simp only [CollatzResearch.WordTrace]
  refine ⟨163693397323492743347608067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109128931548995162231738711 163693397323492743347608067)
  ·
    refine ⟨245540095985239115021412101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163693397323492743347608067 245540095985239115021412101)
    ·
      refine ⟨46038767997232334066514769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245540095985239115021412101 46038767997232334066514769)
      ·
        refine ⟨34529075997924250549886077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46038767997232334066514769 34529075997924250549886077)
        ·
          refine ⟨12948403499221593956207279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34529075997924250549886077 12948403499221593956207279)
          ·
            refine ⟨19422605248832390934310919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12948403499221593956207279 19422605248832390934310919)
            ·
              refine ⟨29133907873248586401466379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19422605248832390934310919 29133907873248586401466379)
              ·
                refine ⟨43700861809872879602199569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29133907873248586401466379 43700861809872879602199569)
                ·
                  refine ⟨32775646357404659701649677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43700861809872879602199569 32775646357404659701649677)
                  ·
                    refine ⟨12290867384026747388118629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32775646357404659701649677 12290867384026747388118629)
                    ·
                      refine ⟨2304537634505015135272243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12290867384026747388118629 2304537634505015135272243)
                      ·
                        rfl

theorem cell23_4488071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4488071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488071 prefixEnd_4488071 := by exact prefixLift 4488071
  have htrace : WordTrace (prefixWord ++ tailWord_4488071) baseStart_4488071 baseEnd_4488071 := by
    simpa [prefixWord, tailWord_4488071, baseEnd_4488071] using wordTrace_append hprefix tailTrace_4488071
  have hstable : (prefixWord ++ tailWord_4488071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488071).length < 2 ^ (prefixWord ++ tailWord_4488071).sum := by decide
  have hdescent : baseEnd_4488071 < baseStart_4488071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488109 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4488109 : Nat := 118140960795 + 4488109 * 2 ^ 59
def prefixEnd_4488109 : Nat := 4983230072969 + 3 ^ 40 * 4488109 * 2
def baseEnd_4488109 : Nat := 2304557146769885986597069

theorem tailTrace_4488109 : CollatzResearch.WordTrace tailWord_4488109 prefixEnd_4488109 2304557146769885986597069 := by
  unfold tailWord_4488109
  simp only [CollatzResearch.WordTrace]
  refine ⟨163694783297355075837491381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109129855531570050558327587 163694783297355075837491381)
  ·
    refine ⟨15346385934127038359764817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163694783297355075837491381 15346385934127038359764817)
    ·
      refine ⟨11509789450595278769823613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15346385934127038359764817 11509789450595278769823613)
      ·
        refine ⟨4316171043973229538683855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11509789450595278769823613 4316171043973229538683855)
        ·
          refine ⟨6474256565959844308025783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316171043973229538683855 6474256565959844308025783)
          ·
            refine ⟨9711384848939766462038675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6474256565959844308025783 9711384848939766462038675)
            ·
              refine ⟨14567077273409649693058013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9711384848939766462038675 14567077273409649693058013)
              ·
                refine ⟨5462653977528618634896755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14567077273409649693058013 5462653977528618634896755)
                ·
                  refine ⟨8193980966292927952345133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5462653977528618634896755 8193980966292927952345133)
                  ·
                    refine ⟨3072742862359847982129425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8193980966292927952345133 3072742862359847982129425)
                    ·
                      refine ⟨2304557146769885986597069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072742862359847982129425 2304557146769885986597069)
                      ·
                        rfl

theorem cell23_4488109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4488109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488109 prefixEnd_4488109 := by exact prefixLift 4488109
  have htrace : WordTrace (prefixWord ++ tailWord_4488109) baseStart_4488109 baseEnd_4488109 := by
    simpa [prefixWord, tailWord_4488109, baseEnd_4488109] using wordTrace_append hprefix tailTrace_4488109
  have hstable : (prefixWord ++ tailWord_4488109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488109).length < 2 ^ (prefixWord ++ tailWord_4488109).sum := by decide
  have hdescent : baseEnd_4488109 < baseStart_4488109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488128 : List Nat := [2, 1, 1, 2, 3, 3, 2, 4, 5]
def baseStart_4488128 : Nat := 118140960795 + 4488128 * 2 ^ 59
def prefixEnd_4488128 : Nat := 4983230072969 + 3 ^ 40 * 4488128 * 2
def baseEnd_4488128 : Nat := 256062989211369045806609

theorem tailTrace_4488128 : CollatzResearch.WordTrace tailWord_4488128 prefixEnd_4488128 256062989211369045806609 := by
  unfold tailWord_4488128
  simp only [CollatzResearch.WordTrace]
  refine ⟨81847738142143121041216519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109130317522857494721622025 81847738142143121041216519)
  ·
    refine ⟨122771607213214681561824779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81847738142143121041216519 122771607213214681561824779)
    ·
      refine ⟨184157410819822022342737169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122771607213214681561824779 184157410819822022342737169)
      ·
        refine ⟨138118058114866516757052877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184157410819822022342737169 138118058114866516757052877)
        ·
          refine ⟨51794271793074943783894829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138118058114866516757052877 51794271793074943783894829)
          ·
            refine ⟨19422851922403103918960561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51794271793074943783894829 19422851922403103918960561)
            ·
              refine ⟨14567138941802327939220421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19422851922403103918960561 14567138941802327939220421)
              ·
                refine ⟨2731338551587936488603829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14567138941802327939220421 2731338551587936488603829)
                ·
                  refine ⟨256062989211369045806609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731338551587936488603829 256062989211369045806609)
                  ·
                    rfl

theorem cell23_4488128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 5].length) (baseStart_4488128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488128 prefixEnd_4488128 := by exact prefixLift 4488128
  have htrace : WordTrace (prefixWord ++ tailWord_4488128) baseStart_4488128 baseEnd_4488128 := by
    simpa [prefixWord, tailWord_4488128, baseEnd_4488128] using wordTrace_append hprefix tailTrace_4488128
  have hstable : (prefixWord ++ tailWord_4488128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488128).length < 2 ^ (prefixWord ++ tailWord_4488128).sum := by decide
  have hdescent : baseEnd_4488128 < baseStart_4488128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488162 : List Nat := [3, 3, 3, 1, 1, 1, 3, 3, 5]
def baseStart_4488162 : Nat := 118140960795 + 4488162 * 2 ^ 59
def prefixEnd_4488162 : Nat := 4983230072969 + 3 ^ 40 * 4488162 * 2
def baseEnd_4488162 : Nat := 256064929027174919914925

theorem tailTrace_4488162 : CollatzResearch.WordTrace tailWord_4488162 prefixEnd_4488162 256064929027174919914925 := by
  unfold tailWord_4488162
  simp only [CollatzResearch.WordTrace]
  refine ⟨40924179091540766472292685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109131144244108710592780493 40924179091540766472292685)
  ·
    refine ⟨15346567159327787427109757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40924179091540766472292685 15346567159327787427109757)
    ·
      refine ⟨5754962684747920285166159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15346567159327787427109757 5754962684747920285166159)
      ·
        refine ⟨8632444027121880427749239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5754962684747920285166159 8632444027121880427749239)
        ·
          refine ⟨12948666040682820641623859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8632444027121880427749239 12948666040682820641623859)
          ·
            refine ⟨19422999061024230962435789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12948666040682820641623859 19422999061024230962435789)
            ·
              refine ⟨7283624647884086610913421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19422999061024230962435789 7283624647884086610913421)
              ·
                refine ⟨2731359242956532479092533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7283624647884086610913421 2731359242956532479092533)
                ·
                  refine ⟨256064929027174919914925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731359242956532479092533 256064929027174919914925)
                  ·
                    rfl

theorem cell23_4488162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_4488162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488162 prefixEnd_4488162 := by exact prefixLift 4488162
  have htrace : WordTrace (prefixWord ++ tailWord_4488162) baseStart_4488162 baseEnd_4488162 := by
    simpa [prefixWord, tailWord_4488162, baseEnd_4488162] using wordTrace_append hprefix tailTrace_4488162
  have hstable : (prefixWord ++ tailWord_4488162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488162).length < 2 ^ (prefixWord ++ tailWord_4488162).sum := by decide
  have hdescent : baseEnd_4488162 < baseStart_4488162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488215 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4488215 : Nat := 118140960795 + 4488215 * 2 ^ 59
def prefixEnd_4488215 : Nat := 4983230072969 + 3 ^ 40 * 4488215 * 2
def baseEnd_4488215 : Nat := 2304611575719262571871581

theorem tailTrace_4488215 : CollatzResearch.WordTrace tailWord_4488215 prefixEnd_4488215 2304611575719262571871581 := by
  unfold tailWord_4488215
  simp only [CollatzResearch.WordTrace]
  refine ⟨163698649434971055940850099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109132432956647370627233399 163698649434971055940850099)
  ·
    refine ⟨245547974152456583911275149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163698649434971055940850099 245547974152456583911275149)
    ·
      refine ⟨92080490307171218966728181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245547974152456583911275149 92080490307171218966728181)
      ·
        refine ⟨8632545966297301778130767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92080490307171218966728181 8632545966297301778130767)
        ·
          refine ⟨12948818949445952667196151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8632545966297301778130767 12948818949445952667196151)
          ·
            refine ⟨19423228424168929000794227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12948818949445952667196151 19423228424168929000794227)
            ·
              refine ⟨29134842636253393501191341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19423228424168929000794227 29134842636253393501191341)
              ·
                refine ⟨10925565988595022562946753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29134842636253393501191341 10925565988595022562946753)
                ·
                  refine ⟨8194174491446266922210065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10925565988595022562946753 8194174491446266922210065)
                  ·
                    refine ⟨6145630868584700191657549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8194174491446266922210065 6145630868584700191657549)
                    ·
                      refine ⟨2304611575719262571871581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145630868584700191657549 2304611575719262571871581)
                      ·
                        rfl

theorem cell23_4488215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4488215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488215 prefixEnd_4488215 := by exact prefixLift 4488215
  have htrace : WordTrace (prefixWord ++ tailWord_4488215) baseStart_4488215 baseEnd_4488215 := by
    simpa [prefixWord, tailWord_4488215, baseEnd_4488215] using wordTrace_append hprefix tailTrace_4488215
  have hstable : (prefixWord ++ tailWord_4488215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488215).length < 2 ^ (prefixWord ++ tailWord_4488215).sum := by decide
  have hdescent : baseEnd_4488215 < baseStart_4488215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488238 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4488238 : Nat := 118140960795 + 4488238 * 2 ^ 59
def prefixEnd_4488238 : Nat := 4983230072969 + 3 ^ 40 * 4488238 * 2
def baseEnd_4488238 : Nat := 2304623385774315981883975

theorem tailTrace_4488238 : CollatzResearch.WordTrace tailWord_4488238 prefixEnd_4488238 2304623385774315981883975 := by
  unfold tailWord_4488238
  simp only [CollatzResearch.WordTrace]
  refine ⟨20462436039235966358617171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109132992209258487245958245 20462436039235966358617171)
  ·
    refine ⟨30693654058853949537925757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20462436039235966358617171 30693654058853949537925757)
    ·
      refine ⟨11510120272070231076722159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30693654058853949537925757 11510120272070231076722159)
      ·
        refine ⟨17265180408105346615083239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11510120272070231076722159 17265180408105346615083239)
        ·
          refine ⟨25897770612158019922624859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17265180408105346615083239 25897770612158019922624859)
          ·
            refine ⟨38846655918237029883937289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25897770612158019922624859 38846655918237029883937289)
            ·
              refine ⟨29134991938677772412952967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38846655918237029883937289 29134991938677772412952967)
              ·
                refine ⟨43702487908016658619429451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29134991938677772412952967 43702487908016658619429451)
                ·
                  refine ⟨65553731862024987929144177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43702487908016658619429451 65553731862024987929144177)
                  ·
                    refine ⟨49165298896518740946858133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65553731862024987929144177 49165298896518740946858133)
                    ·
                      refine ⟨2304623385774315981883975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49165298896518740946858133 2304623385774315981883975)
                      ·
                        rfl

theorem cell23_4488238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4488238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488238 prefixEnd_4488238 := by exact prefixLift 4488238
  have htrace : WordTrace (prefixWord ++ tailWord_4488238) baseStart_4488238 baseEnd_4488238 := by
    simpa [prefixWord, tailWord_4488238, baseEnd_4488238] using wordTrace_append hprefix tailTrace_4488238
  have hstable : (prefixWord ++ tailWord_4488238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488238).length < 2 ^ (prefixWord ++ tailWord_4488238).sum := by decide
  have hdescent : baseEnd_4488238 < baseStart_4488238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488245 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_4488245 : Nat := 118140960795 + 4488245 * 2 ^ 59
def prefixEnd_4488245 : Nat := 4983230072969 + 3 ^ 40 * 4488245 * 2
def baseEnd_4488245 : Nat := 2304626980138897454496443

theorem tailTrace_4488245 : CollatzResearch.WordTrace tailWord_4488245 prefixEnd_4488245 2304626980138897454496443 := by
  unfold tailWord_4488245
  simp only [CollatzResearch.WordTrace]
  refine ⟨163699743624862371064442189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109133162416574914042961459 163699743624862371064442189)
  ·
    refine ⟨61387403859323389149165821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163699743624862371064442189 61387403859323389149165821)
    ·
      refine ⟨23020276447246270930937183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61387403859323389149165821 23020276447246270930937183)
      ·
        refine ⟨34530414670869406396405775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23020276447246270930937183 34530414670869406396405775)
        ·
          refine ⟨51795622006304109594608663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34530414670869406396405775 51795622006304109594608663)
          ·
            refine ⟨77693433009456164391912995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51795622006304109594608663 77693433009456164391912995)
            ·
              refine ⟨116540149514184246587869493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77693433009456164391912995 116540149514184246587869493)
              ·
                refine ⟨10925639016954773117612765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116540149514184246587869493 10925639016954773117612765)
                ·
                  refine ⟨4097114631358039919104787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10925639016954773117612765 4097114631358039919104787)
                  ·
                    refine ⟨6145671947037059878657181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4097114631358039919104787 6145671947037059878657181)
                    ·
                      refine ⟨2304626980138897454496443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145671947037059878657181 2304626980138897454496443)
                      ·
                        rfl

theorem cell23_4488245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_4488245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488245 prefixEnd_4488245 := by exact prefixLift 4488245
  have htrace : WordTrace (prefixWord ++ tailWord_4488245) baseStart_4488245 baseEnd_4488245 := by
    simpa [prefixWord, tailWord_4488245, baseEnd_4488245] using wordTrace_append hprefix tailTrace_4488245
  have hstable : (prefixWord ++ tailWord_4488245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488245).length < 2 ^ (prefixWord ++ tailWord_4488245).sum := by decide
  have hdescent : baseEnd_4488245 < baseStart_4488245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488248 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 3, 5]
def baseStart_4488248 : Nat := 118140960795 + 4488248 * 2 ^ 59
def prefixEnd_4488248 : Nat := 4983230072969 + 3 ^ 40 * 4488248 * 2
def baseEnd_4488248 : Nat := 768209506860286980919643

theorem tailTrace_4488248 : CollatzResearch.WordTrace tailWord_4488248 prefixEnd_4488248 768209506860286980919643 := by
  unfold tailWord_4488248
  simp only [CollatzResearch.WordTrace]
  refine ⟨81849926521925751288400699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109133235362567668384534265 81849926521925751288400699)
  ·
    refine ⟨122774889782888626932601049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81849926521925751288400699 122774889782888626932601049)
    ·
      refine ⟨92081167337166470199450787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122774889782888626932601049 92081167337166470199450787)
      ·
        refine ⟨138121751005749705299176181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92081167337166470199450787 138121751005749705299176181)
        ·
          refine ⟨12948914156789034871797767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138121751005749705299176181 12948914156789034871797767)
          ·
            refine ⟨19423371235183552307696651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12948914156789034871797767 19423371235183552307696651)
            ·
              refine ⟨29135056852775328461544977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19423371235183552307696651 29135056852775328461544977)
              ·
                refine ⟨21851292639581496346158733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29135056852775328461544977 21851292639581496346158733)
                ·
                  refine ⟨8194234739843061129809525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21851292639581496346158733 8194234739843061129809525)
                  ·
                    refine ⟨768209506860286980919643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8194234739843061129809525 768209506860286980919643)
                    ·
                      rfl

theorem cell23_4488248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_4488248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488248 prefixEnd_4488248 := by exact prefixLift 4488248
  have htrace : WordTrace (prefixWord ++ tailWord_4488248) baseStart_4488248 baseEnd_4488248 := by
    simpa [prefixWord, tailWord_4488248, baseEnd_4488248] using wordTrace_append hprefix tailTrace_4488248
  have hstable : (prefixWord ++ tailWord_4488248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488248).length < 2 ^ (prefixWord ++ tailWord_4488248).sum := by decide
  have hdescent : baseEnd_4488248 < baseStart_4488248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488251 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4]
def baseStart_4488251 : Nat := 118140960795 + 4488251 * 2 ^ 59
def prefixEnd_4488251 : Nat := 4983230072969 + 3 ^ 40 * 4488251 * 2
def baseEnd_4488251 : Nat := 2304630061022824431021415

theorem tailTrace_4488251 : CollatzResearch.WordTrace tailWord_4488251 prefixEnd_4488251 2304630061022824431021415 := by
  unfold tailWord_4488251
  simp only [CollatzResearch.WordTrace]
  refine ⟨163699962462840634089160607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109133308308560422726107071 163699962462840634089160607)
  ·
    refine ⟨245549943694260951133740911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163699962462840634089160607 245549943694260951133740911)
    ·
      refine ⟨368324915541391426700611367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245549943694260951133740911 368324915541391426700611367)
      ·
        refine ⟨552487373312087140050917051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368324915541391426700611367 552487373312087140050917051)
        ·
          refine ⟨828731059968130710076375577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552487373312087140050917051 828731059968130710076375577)
          ·
            refine ⟨621548294976098032557281683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828731059968130710076375577 621548294976098032557281683)
            ·
              refine ⟨932322442464147048835922525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621548294976098032557281683 932322442464147048835922525)
              ·
                refine ⟨349620915924055143313470947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 932322442464147048835922525 349620915924055143313470947)
                ·
                  refine ⟨524431373886082714970206421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349620915924055143313470947 524431373886082714970206421)
                  ·
                    refine ⟨12291360325455063632114213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 524431373886082714970206421 12291360325455063632114213)
                    ·
                      refine ⟨2304630061022824431021415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12291360325455063632114213 2304630061022824431021415)
                      ·
                        rfl

theorem cell23_4488251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_4488251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488251 prefixEnd_4488251 := by exact prefixLift 4488251
  have htrace : WordTrace (prefixWord ++ tailWord_4488251) baseStart_4488251 baseEnd_4488251 := by
    simpa [prefixWord, tailWord_4488251, baseEnd_4488251] using wordTrace_append hprefix tailTrace_4488251
  have hstable : (prefixWord ++ tailWord_4488251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488251).length < 2 ^ (prefixWord ++ tailWord_4488251).sum := by decide
  have hdescent : baseEnd_4488251 < baseStart_4488251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488271 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_4488271 : Nat := 118140960795 + 4488271 * 2 ^ 59
def prefixEnd_4488271 : Nat := 4983230072969 + 3 ^ 40 * 4488271 * 2
def baseEnd_4488271 : Nat := 2304640330635914352771323

theorem tailTrace_4488271 : CollatzResearch.WordTrace tailWord_4488271 prefixEnd_4488271 2304640330635914352771323 := by
  unfold tailWord_4488271
  simp only [CollatzResearch.WordTrace]
  refine ⟨163700691922768177504888667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109133794615178785003259111 163700691922768177504888667)
  ·
    refine ⟨245551037884152266257333001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163700691922768177504888667 245551037884152266257333001)
    ·
      refine ⟨184163278413114199692999751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245551037884152266257333001 184163278413114199692999751)
      ·
        refine ⟨276244917619671299539499627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184163278413114199692999751 276244917619671299539499627)
        ·
          refine ⟨414367376429506949309249441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276244917619671299539499627 414367376429506949309249441)
          ·
            refine ⟨310775532322130211981937081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414367376429506949309249441 310775532322130211981937081)
            ·
              refine ⟨233081649241597658986452811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310775532322130211981937081 233081649241597658986452811)
              ·
                refine ⟨349622473862396488479679217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233081649241597658986452811 349622473862396488479679217)
                ·
                  refine ⟨262216855396797366359759413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349622473862396488479679217 262216855396797366359759413)
                  ·
                    refine ⟨24582830193449753096227445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 262216855396797366359759413 24582830193449753096227445)
                    ·
                      refine ⟨2304640330635914352771323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24582830193449753096227445 2304640330635914352771323)
                      ·
                        rfl

theorem cell23_4488271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_4488271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488271 prefixEnd_4488271 := by exact prefixLift 4488271
  have htrace : WordTrace (prefixWord ++ tailWord_4488271) baseStart_4488271 baseEnd_4488271 := by
    simpa [prefixWord, tailWord_4488271, baseEnd_4488271] using wordTrace_append hprefix tailTrace_4488271
  have hstable : (prefixWord ++ tailWord_4488271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488271).length < 2 ^ (prefixWord ++ tailWord_4488271).sum := by decide
  have hdescent : baseEnd_4488271 < baseStart_4488271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488288 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_4488288 : Nat := 118140960795 + 4488288 * 2 ^ 59
def prefixEnd_4488288 : Nat := 4983230072969 + 3 ^ 40 * 4488288 * 2
def baseEnd_4488288 : Nat := 2304649059807040786258745

theorem tailTrace_4488288 : CollatzResearch.WordTrace tailWord_4488288 prefixEnd_4488288 2304649059807040786258745 := by
  unfold tailWord_4488288
  simp only [CollatzResearch.WordTrace]
  refine ⟨81850655981853294704128759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109134207975804392938838345 81850655981853294704128759)
  ·
    refine ⟨122775983972779942056193139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81850655981853294704128759 122775983972779942056193139)
    ·
      refine ⟨184163975959169913084289709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122775983972779942056193139 184163975959169913084289709)
      ·
        refine ⟨69061490984688717406608641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184163975959169913084289709 69061490984688717406608641)
        ·
          refine ⟨51796118238516538054956481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69061490984688717406608641 51796118238516538054956481)
          ·
            refine ⟨38847088678887403541217361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51796118238516538054956481 38847088678887403541217361)
            ·
              refine ⟨29135316509165552655913021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38847088678887403541217361 29135316509165552655913021)
              ·
                refine ⟨10925743690937082245967383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29135316509165552655913021 10925743690937082245967383)
                ·
                  refine ⟨16388615536405623368951075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10925743690937082245967383 16388615536405623368951075)
                  ·
                    refine ⟨24582923304608435053426613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16388615536405623368951075 24582923304608435053426613)
                    ·
                      refine ⟨2304649059807040786258745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24582923304608435053426613 2304649059807040786258745)
                      ·
                        rfl

theorem cell23_4488288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_4488288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488288 prefixEnd_4488288 := by exact prefixLift 4488288
  have htrace : WordTrace (prefixWord ++ tailWord_4488288) baseStart_4488288 baseEnd_4488288 := by
    simpa [prefixWord, tailWord_4488288, baseEnd_4488288] using wordTrace_append hprefix tailTrace_4488288
  have hstable : (prefixWord ++ tailWord_4488288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488288).length < 2 ^ (prefixWord ++ tailWord_4488288).sum := by decide
  have hdescent : baseEnd_4488288 < baseStart_4488288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488295 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 4, 4]
def baseStart_4488295 : Nat := 118140960795 + 4488295 * 2 ^ 59
def prefixEnd_4488295 : Nat := 4983230072969 + 3 ^ 40 * 4488295 * 2
def baseEnd_4488295 : Nat := 768217551390540752957071

theorem tailTrace_4488295 : CollatzResearch.WordTrace tailWord_4488295 prefixEnd_4488295 768217551390540752957071 := by
  unfold tailWord_4488295
  simp only [CollatzResearch.WordTrace]
  refine ⟨163701567274681229603762339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109134378183120819735841559 163701567274681229603762339)
  ·
    refine ⟨245552350912021844405643509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163701567274681229603762339 245552350912021844405643509)
    ·
      refine ⟨23020532898002047913029079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245552350912021844405643509 23020532898002047913029079)
      ·
        refine ⟨34530799347003071869543619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23020532898002047913029079 34530799347003071869543619)
        ·
          refine ⟨51796199020504607804315429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34530799347003071869543619 51796199020504607804315429)
          ·
            refine ⟨9711787316344613963309143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51796199020504607804315429 9711787316344613963309143)
            ·
              refine ⟨14567680974516920944963715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9711787316344613963309143 14567680974516920944963715)
              ·
                refine ⟨21851521461775381417445573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14567680974516920944963715 21851521461775381417445573)
                ·
                  refine ⟨4097160274082884015771045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21851521461775381417445573 4097160274082884015771045)
                  ·
                    refine ⟨768217551390540752957071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4097160274082884015771045 768217551390540752957071)
                    ·
                      rfl

theorem cell23_4488295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_4488295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488295 prefixEnd_4488295 := by exact prefixLift 4488295
  have htrace : WordTrace (prefixWord ++ tailWord_4488295) baseStart_4488295 baseEnd_4488295 := by
    simpa [prefixWord, tailWord_4488295, baseEnd_4488295] using wordTrace_append hprefix tailTrace_4488295
  have hstable : (prefixWord ++ tailWord_4488295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488295).length < 2 ^ (prefixWord ++ tailWord_4488295).sum := by decide
  have hdescent : baseEnd_4488295 < baseStart_4488295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488345 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 7, 3, 2]
def baseStart_4488345 : Nat := 118140960795 + 4488345 * 2 ^ 59
def prefixEnd_4488345 : Nat := 4983230072969 + 3 ^ 40 * 4488345 * 2
def baseEnd_4488345 : Nat := 2304678328204347063245983

theorem tailTrace_4488345 : CollatzResearch.WordTrace tailWord_4488345 prefixEnd_4488345 2304678328204347063245983 := by
  unfold tailWord_4488345
  simp only [CollatzResearch.WordTrace]
  refine ⟨163703390924500088143082489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109135593949666725428721659 163703390924500088143082489)
  ·
    refine ⟨122777543193375066107311867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163703390924500088143082489 122777543193375066107311867)
    ·
      refine ⟨184166314790062599160967801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122777543193375066107311867 184166314790062599160967801)
      ·
        refine ⟨138124736092546949370725851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184166314790062599160967801 138124736092546949370725851)
        ·
          refine ⟨207187104138820424056088777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138124736092546949370725851 207187104138820424056088777)
          ·
            refine ⟨155390328104115318042066583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207187104138820424056088777 155390328104115318042066583)
            ·
              refine ⟨233085492156172977063099875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155390328104115318042066583 233085492156172977063099875)
              ·
                refine ⟨349628238234259465594649813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233085492156172977063099875 349628238234259465594649813)
                ·
                  refine ⟨8194411833615456224874605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 349628238234259465594649813 8194411833615456224874605)
                  ·
                    refine ⟨3072904437605796084327977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8194411833615456224874605 3072904437605796084327977)
                    ·
                      refine ⟨2304678328204347063245983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072904437605796084327977 2304678328204347063245983)
                      ·
                        rfl

theorem cell23_4488345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_4488345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488345 prefixEnd_4488345 := by exact prefixLift 4488345
  have htrace : WordTrace (prefixWord ++ tailWord_4488345) baseStart_4488345 baseEnd_4488345 := by
    simpa [prefixWord, tailWord_4488345, baseEnd_4488345] using wordTrace_append hprefix tailTrace_4488345
  have hstable : (prefixWord ++ tailWord_4488345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488345).length < 2 ^ (prefixWord ++ tailWord_4488345).sum := by decide
  have hdescent : baseEnd_4488345 < baseStart_4488345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488352 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 2, 1, 3]
def baseStart_4488352 : Nat := 118140960795 + 4488352 * 2 ^ 59
def prefixEnd_4488352 : Nat := 4983230072969 + 3 ^ 40 * 4488352 * 2
def baseEnd_4488352 : Nat := 2304681922568928535858451

theorem tailTrace_4488352 : CollatzResearch.WordTrace tailWord_4488352 prefixEnd_4488352 2304681922568928535858451 := by
  unfold tailWord_4488352
  simp only [CollatzResearch.WordTrace]
  refine ⟨81851823117737364169293655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109135764156983152225724873 81851823117737364169293655)
  ·
    refine ⟨122777734676606046253940483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81851823117737364169293655 122777734676606046253940483)
    ·
      refine ⟨184166602014909069380910725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122777734676606046253940483 184166602014909069380910725)
      ·
        refine ⟨34531237877795450508920761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184166602014909069380910725 34531237877795450508920761)
        ·
          refine ⟨25898428408346587881690571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34531237877795450508920761 25898428408346587881690571)
          ·
            refine ⟨38847642612519881822535857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25898428408346587881690571 38847642612519881822535857)
            ·
              refine ⟨29135731959389911366901893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38847642612519881822535857 29135731959389911366901893)
              ·
                refine ⟨5462949742385608381294105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29135731959389911366901893 5462949742385608381294105)
                ·
                  refine ⟨4097212306789206285970579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5462949742385608381294105 4097212306789206285970579)
                  ·
                    refine ⟨6145818460183809428955869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4097212306789206285970579 6145818460183809428955869)
                    ·
                      refine ⟨2304681922568928535858451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145818460183809428955869 2304681922568928535858451)
                      ·
                        rfl

theorem cell23_4488352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_4488352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488352 prefixEnd_4488352 := by exact prefixLift 4488352
  have htrace : WordTrace (prefixWord ++ tailWord_4488352) baseStart_4488352 baseEnd_4488352 := by
    simpa [prefixWord, tailWord_4488352, baseEnd_4488352] using wordTrace_append hprefix tailTrace_4488352
  have hstable : (prefixWord ++ tailWord_4488352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488352).length < 2 ^ (prefixWord ++ tailWord_4488352).sum := by decide
  have hdescent : baseEnd_4488352 < baseStart_4488352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488369 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4488369 : Nat := 118140960795 + 4488369 * 2 ^ 59
def prefixEnd_4488369 : Nat := 4983230072969 + 3 ^ 40 * 4488369 * 2
def baseEnd_4488369 : Nat := 2304690651740054969345873

theorem tailTrace_4488369 : CollatzResearch.WordTrace tailWord_4488369 prefixEnd_4488369 2304690651740054969345873 := by
  unfold tailWord_4488369
  simp only [CollatzResearch.WordTrace]
  refine ⟨163704266276413140241956161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109136177517608760161304107 163704266276413140241956161)
  ·
    refine ⟨122778199707309855181467121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163704266276413140241956161 122778199707309855181467121)
    ·
      refine ⟨92083649780482391386100341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122778199707309855181467121 92083649780482391386100341)
      ·
        refine ⟨8632842166920224192446907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92083649780482391386100341 8632842166920224192446907)
        ·
          refine ⟨12949263250380336288670361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8632842166920224192446907 12949263250380336288670361)
          ·
            refine ⟨9711947437785252216502771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12949263250380336288670361 9711947437785252216502771)
            ·
              refine ⟨14567921156677878324754157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9711947437785252216502771 14567921156677878324754157)
              ·
                refine ⟨5462970433754204371782809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14567921156677878324754157 5462970433754204371782809)
                ·
                  refine ⟨4097227825315653278837107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5462970433754204371782809 4097227825315653278837107)
                  ·
                    refine ⟨6145841737973479918255661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4097227825315653278837107 6145841737973479918255661)
                    ·
                      refine ⟨2304690651740054969345873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145841737973479918255661 2304690651740054969345873)
                      ·
                        rfl

theorem cell23_4488369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4488369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488369 prefixEnd_4488369 := by exact prefixLift 4488369
  have htrace : WordTrace (prefixWord ++ tailWord_4488369) baseStart_4488369 baseEnd_4488369 := by
    simpa [prefixWord, tailWord_4488369, baseEnd_4488369] using wordTrace_append hprefix tailTrace_4488369
  have hstable : (prefixWord ++ tailWord_4488369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488369).length < 2 ^ (prefixWord ++ tailWord_4488369).sum := by decide
  have hdescent : baseEnd_4488369 < baseStart_4488369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488386 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_4488386 : Nat := 118140960795 + 4488386 * 2 ^ 59
def prefixEnd_4488386 : Nat := 4983230072969 + 3 ^ 40 * 4488386 * 2
def baseEnd_4488386 : Nat := 2304699380911181402833295

theorem tailTrace_4488386 : CollatzResearch.WordTrace tailWord_4488386 prefixEnd_4488386 2304699380911181402833295 := by
  unfold tailWord_4488386
  simp only [CollatzResearch.WordTrace]
  refine ⟨40926221579337888036331253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109136590878234368096883341 40926221579337888036331253)
  ·
    refine ⟨3836833273062927003406055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40926221579337888036331253 3836833273062927003406055)
    ·
      refine ⟨5755249909594390505109083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3836833273062927003406055 5755249909594390505109083)
      ·
        refine ⟨8632874864391585757663625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5755249909594390505109083 8632874864391585757663625)
        ·
          refine ⟨6474656148293689318247719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8632874864391585757663625 6474656148293689318247719)
          ·
            refine ⟨9711984222440533977371579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6474656148293689318247719 9711984222440533977371579)
            ·
              refine ⟨14567976333660800966057369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9711984222440533977371579 14567976333660800966057369)
              ·
                refine ⟨10925982250245600724543027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14567976333660800966057369 10925982250245600724543027)
                ·
                  refine ⟨16388973375368401086814541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10925982250245600724543027 16388973375368401086814541)
                  ·
                    refine ⟨6145865015763150407555453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16388973375368401086814541 6145865015763150407555453)
                    ·
                      refine ⟨2304699380911181402833295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145865015763150407555453 2304699380911181402833295)
                      ·
                        rfl

theorem cell23_4488386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_4488386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488386 prefixEnd_4488386 := by exact prefixLift 4488386
  have htrace : WordTrace (prefixWord ++ tailWord_4488386) baseStart_4488386 baseEnd_4488386 := by
    simpa [prefixWord, tailWord_4488386, baseEnd_4488386] using wordTrace_append hprefix tailTrace_4488386
  have hstable : (prefixWord ++ tailWord_4488386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488386).length < 2 ^ (prefixWord ++ tailWord_4488386).sum := by decide
  have hdescent : baseEnd_4488386 < baseStart_4488386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488390 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4488390 : Nat := 118140960795 + 4488390 * 2 ^ 59
def prefixEnd_4488390 : Nat := 4983230072969 + 3 ^ 40 * 4488390 * 2
def baseEnd_4488390 : Nat := 2304701434833799387183277

theorem tailTrace_4488390 : CollatzResearch.WordTrace tailWord_4488390 prefixEnd_4488390 2304701434833799387183277 := by
  unfold tailWord_4488390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115782256541783150889707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109136688139558040552313749 5115782256541783150889707)
  ·
    refine ⟨7673673384812674726334561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5115782256541783150889707 7673673384812674726334561)
    ·
      refine ⟨5755255038609506044750921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7673673384812674726334561 5755255038609506044750921)
      ·
        refine ⟨4316441278957129533563191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5755255038609506044750921 4316441278957129533563191)
        ·
          refine ⟨6474661918435694300344787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316441278957129533563191 6474661918435694300344787)
          ·
            refine ⟨9711992877653541450517181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6474661918435694300344787 9711992877653541450517181)
            ·
              refine ⟨3641997329120078043943943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9711992877653541450517181 3641997329120078043943943)
              ·
                refine ⟨5462995993680117065915915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641997329120078043943943 5462995993680117065915915)
                ·
                  refine ⟨8194493990520175598873873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5462995993680117065915915 8194493990520175598873873)
                  ·
                    refine ⟨6145870492890131699155405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8194493990520175598873873 6145870492890131699155405)
                    ·
                      refine ⟨2304701434833799387183277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6145870492890131699155405 2304701434833799387183277)
                      ·
                        rfl

theorem cell23_4488390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4488390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488390 prefixEnd_4488390 := by exact prefixLift 4488390
  have htrace : WordTrace (prefixWord ++ tailWord_4488390) baseStart_4488390 baseEnd_4488390 := by
    simpa [prefixWord, tailWord_4488390, baseEnd_4488390] using wordTrace_append hprefix tailTrace_4488390
  have hstable : (prefixWord ++ tailWord_4488390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488390).length < 2 ^ (prefixWord ++ tailWord_4488390).sum := by decide
  have hdescent : baseEnd_4488390 < baseStart_4488390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
