import V185TrunkScan23Chunk0146

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_869282 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_869282 : Nat := 118140960795 + 869282 * 2 ^ 59
def prefixEnd_869282 : Nat := 4983230072969 + 3 ^ 40 * 869282 * 2
def baseEnd_869282 : Nat := 148786496767257721292417

theorem tailTrace_869282 : CollatzResearch.WordTrace tailWord_869282 prefixEnd_869282 148786496767257721292417 := by
  unfold tailWord_869282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926329809186812597770525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21136879491164833594054733 7926329809186812597770525)
  ·
    refine ⟨2972373678445054724163947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7926329809186812597770525 2972373678445054724163947)
    ·
      refine ⟨4458560517667582086245921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2972373678445054724163947 4458560517667582086245921)
      ·
        refine ⟨3343920388250686564684441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4458560517667582086245921 3343920388250686564684441)
        ·
          refine ⟨2507940291188014923513331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3343920388250686564684441 2507940291188014923513331)
          ·
            refine ⟨3761910436782022385269997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507940291188014923513331 3761910436782022385269997)
            ·
              refine ⟨1410716413793258394476249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3761910436782022385269997 1410716413793258394476249)
              ·
                refine ⟨1058037310344943795857187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410716413793258394476249 1058037310344943795857187)
                ·
                  refine ⟨1587055965517415693785781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058037310344943795857187 1587055965517415693785781)
                  ·
                    refine ⟨148786496767257721292417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1587055965517415693785781 148786496767257721292417)
                    ·
                      rfl

theorem cell23_869282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_869282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869282 prefixEnd_869282 := by exact prefixLift 869282
  have htrace : WordTrace (prefixWord ++ tailWord_869282) baseStart_869282 baseEnd_869282 := by
    simpa [prefixWord, tailWord_869282, baseEnd_869282] using wordTrace_append hprefix tailTrace_869282
  have hstable : (prefixWord ++ tailWord_869282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869282).length < 2 ^ (prefixWord ++ tailWord_869282).sum := by decide
  have hdescent : baseEnd_869282 < baseStart_869282 := by decide
  rcases family_descends (prefixWord ++ tailWord_869282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869305 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 5]
def baseStart_869305 : Nat := 118140960795 + 869305 * 2 ^ 59
def prefixEnd_869305 : Nat := 4983230072969 + 3 ^ 40 * 869305 * 2
def baseEnd_869305 : Nat := 446371300356826573889645

theorem tailTrace_869305 : CollatzResearch.WordTrace tailWord_869305 prefixEnd_869305 446371300356826573889645 := by
  unfold tailWord_869305
  simp only [CollatzResearch.WordTrace]
  refine ⟨31706158115663925319169369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21137438743775950212779579 31706158115663925319169369)
  ·
    refine ⟨23779618586747943989377027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31706158115663925319169369 23779618586747943989377027)
    ·
      refine ⟨35669427880121915984065541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23779618586747943989377027 35669427880121915984065541)
      ·
        refine ⟨6688017727522859247012289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35669427880121915984065541 6688017727522859247012289)
        ·
          refine ⟨5016013295642144435259217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6688017727522859247012289 5016013295642144435259217)
          ·
            refine ⟨3762009971731608326444413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5016013295642144435259217 3762009971731608326444413)
            ·
              refine ⟨1410753739399353122416655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3762009971731608326444413 1410753739399353122416655)
              ·
                refine ⟨2116130609099029683624983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410753739399353122416655 2116130609099029683624983)
                ·
                  refine ⟨3174195913648544525437475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116130609099029683624983 3174195913648544525437475)
                  ·
                    refine ⟨4761293870472816788156213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174195913648544525437475 4761293870472816788156213)
                    ·
                      refine ⟨446371300356826573889645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4761293870472816788156213 446371300356826573889645)
                      ·
                        rfl

theorem cell23_869305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_869305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869305 prefixEnd_869305 := by exact prefixLift 869305
  have htrace : WordTrace (prefixWord ++ tailWord_869305) baseStart_869305 baseEnd_869305 := by
    simpa [prefixWord, tailWord_869305, baseEnd_869305] using wordTrace_append hprefix tailTrace_869305
  have hstable : (prefixWord ++ tailWord_869305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869305).length < 2 ^ (prefixWord ++ tailWord_869305).sum := by decide
  have hdescent : baseEnd_869305 < baseStart_869305 := by decide
  rcases family_descends (prefixWord ++ tailWord_869305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869312 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 2, 4]
def baseStart_869312 : Nat := 118140960795 + 869312 * 2 ^ 59
def prefixEnd_869312 : Nat := 4983230072969 + 3 ^ 40 * 869312 * 2
def baseEnd_869312 : Nat := 148791631573802682167371

theorem tailTrace_869312 : CollatzResearch.WordTrace tailWord_869312 prefixEnd_869312 148791631573802682167371 := by
  unfold tailWord_869312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15853206713319282757337095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21137608951092377009782793 15853206713319282757337095)
  ·
    refine ⟨23779810069978924136005643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15853206713319282757337095 23779810069978924136005643)
    ·
      refine ⟨35669715104968386204008465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23779810069978924136005643 35669715104968386204008465)
      ·
        refine ⟨26752286328726289653006349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35669715104968386204008465 26752286328726289653006349)
        ·
          refine ⟨10032107373272358619877381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26752286328726289653006349 10032107373272358619877381)
          ·
            refine ⟨1881020132488567241227009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10032107373272358619877381 1881020132488567241227009)
            ·
              refine ⟨1410765099366425430920257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881020132488567241227009 1410765099366425430920257)
              ·
                refine ⟨1058073824524819073190193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410765099366425430920257 1058073824524819073190193)
                ·
                  refine ⟨793555368393614304892645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058073824524819073190193 793555368393614304892645)
                  ·
                    refine ⟨148791631573802682167371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793555368393614304892645 148791631573802682167371)
                    ·
                      rfl

theorem cell23_869312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_869312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869312 prefixEnd_869312 := by exact prefixLift 869312
  have htrace : WordTrace (prefixWord ++ tailWord_869312) baseStart_869312 baseEnd_869312 := by
    simpa [prefixWord, tailWord_869312, baseEnd_869312] using wordTrace_append hprefix tailTrace_869312
  have hstable : (prefixWord ++ tailWord_869312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869312).length < 2 ^ (prefixWord ++ tailWord_869312).sum := by decide
  have hdescent : baseEnd_869312 < baseStart_869312 := by decide
  rcases family_descends (prefixWord ++ tailWord_869312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869332 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_869332 : Nat := 118140960795 + 869332 * 2 ^ 59
def prefixEnd_869332 : Nat := 4983230072969 + 3 ^ 40 * 869332 * 2
def baseEnd_869332 : Nat := 446385164334497968252021

theorem tailTrace_869332 : CollatzResearch.WordTrace tailWord_869332 prefixEnd_869332 446385164334497968252021 := by
  unfold tailWord_869332
  simp only [CollatzResearch.WordTrace]
  refine ⟨15853571443283054465201125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21138095257710739286934833 15853571443283054465201125)
  ·
    refine ⟨2972544645615572712225211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15853571443283054465201125 2972544645615572712225211)
    ·
      refine ⟨4458816968423359068337817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2972544645615572712225211 4458816968423359068337817)
      ·
        refine ⟨3344112726317519301253363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4458816968423359068337817 3344112726317519301253363)
        ·
          refine ⟨5016169089476278951880045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344112726317519301253363 5016169089476278951880045)
          ·
            refine ⟨1881063408553604606955017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5016169089476278951880045 1881063408553604606955017)
            ·
              refine ⟨1410797556415203455216263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881063408553604606955017 1410797556415203455216263)
              ·
                refine ⟨2116196334622805182824395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410797556415203455216263 2116196334622805182824395)
                ·
                  refine ⟨3174294501934207774236593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116196334622805182824395 3174294501934207774236593)
                  ·
                    refine ⟨2380720876450655830677445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3174294501934207774236593 2380720876450655830677445)
                    ·
                      refine ⟨446385164334497968252021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2380720876450655830677445 446385164334497968252021)
                      ·
                        rfl

theorem cell23_869332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_869332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869332 prefixEnd_869332 := by exact prefixLift 869332
  have htrace : WordTrace (prefixWord ++ tailWord_869332) baseStart_869332 baseEnd_869332 := by
    simpa [prefixWord, tailWord_869332, baseEnd_869332] using wordTrace_append hprefix tailTrace_869332
  have hstable : (prefixWord ++ tailWord_869332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869332).length < 2 ^ (prefixWord ++ tailWord_869332).sum := by decide
  have hdescent : baseEnd_869332 < baseStart_869332 := by decide
  rcases family_descends (prefixWord ++ tailWord_869332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869375 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 8, 2]
def baseStart_869375 : Nat := 118140960795 + 869375 * 2 ^ 59
def prefixEnd_869375 : Nat := 4983230072969 + 3 ^ 40 * 869375 * 2
def baseEnd_869375 : Nat := 446407244002641300014323

theorem tailTrace_869375 : CollatzResearch.WordTrace tailWord_869375 prefixEnd_869375 446407244002641300014323 := by
  unfold tailWord_869375
  simp only [CollatzResearch.WordTrace]
  refine ⟨31708711225410327274217579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21139140816940218182811719 31708711225410327274217579)
  ·
    refine ⟨47563066838115490911326369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31708711225410327274217579 47563066838115490911326369)
    ·
      refine ⟨35672300128586618183494777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47563066838115490911326369 35672300128586618183494777)
      ·
        refine ⟨26754225096439963637621083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35672300128586618183494777 26754225096439963637621083)
        ·
          refine ⟨40131337644659945456431625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26754225096439963637621083 40131337644659945456431625)
          ·
            refine ⟨30098503233494959092323719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40131337644659945456431625 30098503233494959092323719)
            ·
              refine ⟨45147754850242438638485579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30098503233494959092323719 45147754850242438638485579)
              ·
                refine ⟨67721632275363657957728369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45147754850242438638485579 67721632275363657957728369)
                ·
                  refine ⟨50791224206522743468296277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67721632275363657957728369 50791224206522743468296277)
                  ·
                    refine ⟨595209658670188400019097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50791224206522743468296277 595209658670188400019097)
                    ·
                      refine ⟨446407244002641300014323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595209658670188400019097 446407244002641300014323)
                      ·
                        rfl

theorem cell23_869375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_869375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869375 prefixEnd_869375 := by exact prefixLift 869375
  have htrace : WordTrace (prefixWord ++ tailWord_869375) baseStart_869375 baseEnd_869375 := by
    simpa [prefixWord, tailWord_869375, baseEnd_869375] using wordTrace_append hprefix tailTrace_869375
  have hstable : (prefixWord ++ tailWord_869375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869375).length < 2 ^ (prefixWord ++ tailWord_869375).sum := by decide
  have hdescent : baseEnd_869375 < baseStart_869375 := by decide
  rcases family_descends (prefixWord ++ tailWord_869375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869386 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_869386 : Nat := 118140960795 + 869386 * 2 ^ 59
def prefixEnd_869386 : Nat := 4983230072969 + 3 ^ 40 * 869386 * 2
def baseEnd_869386 : Nat := 446412892289840756976773

theorem tailTrace_869386 : CollatzResearch.WordTrace tailWord_869386 prefixEnd_869386 446412892289840756976773 := by
  unfold tailWord_869386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927278107092619038217003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21139408285580317435245341 7927278107092619038217003)
  ·
    refine ⟨11890917160638928557325505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7927278107092619038217003 11890917160638928557325505)
    ·
      refine ⟨8918187870479196417994129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11890917160638928557325505 8918187870479196417994129)
      ·
        refine ⟨6688640902859397313495597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8918187870479196417994129 6688640902859397313495597)
        ·
          refine ⟨2508240338572273992560849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6688640902859397313495597 2508240338572273992560849)
          ·
            refine ⟨1881180253929205494420637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508240338572273992560849 1881180253929205494420637)
            ·
              refine ⟨705442595223452060407739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1881180253929205494420637 705442595223452060407739)
              ·
                refine ⟨1058163892835178090611609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705442595223452060407739 1058163892835178090611609)
                ·
                  refine ⟨793622919626383567958707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058163892835178090611609 793622919626383567958707)
                  ·
                    refine ⟨1190434379439575351938061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 793622919626383567958707 1190434379439575351938061)
                    ·
                      refine ⟨446412892289840756976773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1190434379439575351938061 446412892289840756976773)
                      ·
                        rfl

theorem cell23_869386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_869386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869386 prefixEnd_869386 := by exact prefixLift 869386
  have htrace : WordTrace (prefixWord ++ tailWord_869386) baseStart_869386 baseEnd_869386 := by
    simpa [prefixWord, tailWord_869386, baseEnd_869386] using wordTrace_append hprefix tailTrace_869386
  have hstable : (prefixWord ++ tailWord_869386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869386).length < 2 ^ (prefixWord ++ tailWord_869386).sum := by decide
  have hdescent : baseEnd_869386 < baseStart_869386 := by decide
  rcases family_descends (prefixWord ++ tailWord_869386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869392 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 8, 2, 2]
def baseStart_869392 : Nat := 118140960795 + 869392 * 2 ^ 59
def prefixEnd_869392 : Nat := 4983230072969 + 3 ^ 40 * 869392 * 2
def baseEnd_869392 : Nat := 446415973173767733501745

theorem tailTrace_869392 : CollatzResearch.WordTrace tailWord_869392 prefixEnd_869392 446415973173767733501745 := by
  unfold tailWord_869392
  simp only [CollatzResearch.WordTrace]
  refine ⟨15854665633174369588793215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21139554177565826118390953 15854665633174369588793215)
  ·
    refine ⟨23781998449761554383189823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15854665633174369588793215 23781998449761554383189823)
    ·
      refine ⟨35672997674642331574784735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23781998449761554383189823 35672997674642331574784735)
      ·
        refine ⟨53509496511963497362177103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35672997674642331574784735 53509496511963497362177103)
        ·
          refine ⟨80264244767945246043265655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53509496511963497362177103 80264244767945246043265655)
          ·
            refine ⟨120396367151917869064898483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80264244767945246043265655 120396367151917869064898483)
            ·
              refine ⟨180594550727876803597347725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120396367151917869064898483 180594550727876803597347725)
              ·
                refine ⟨67722956522953801349005397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180594550727876803597347725 67722956522953801349005397)
                ·
                  refine ⟨793628396753364859558657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 67722956522953801349005397 793628396753364859558657)
                  ·
                    refine ⟨595221297565023644668993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 793628396753364859558657 595221297565023644668993)
                    ·
                      refine ⟨446415973173767733501745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595221297565023644668993 446415973173767733501745)
                      ·
                        rfl

theorem cell23_869392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 2, 2].length) (baseStart_869392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869392 prefixEnd_869392 := by exact prefixLift 869392
  have htrace : WordTrace (prefixWord ++ tailWord_869392) baseStart_869392 baseEnd_869392 := by
    simpa [prefixWord, tailWord_869392, baseEnd_869392] using wordTrace_append hprefix tailTrace_869392
  have hstable : (prefixWord ++ tailWord_869392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869392).length < 2 ^ (prefixWord ++ tailWord_869392).sum := by decide
  have hdescent : baseEnd_869392 < baseStart_869392 := by decide
  rcases family_descends (prefixWord ++ tailWord_869392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869409 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_869409 : Nat := 118140960795 + 869409 * 2 ^ 59
def prefixEnd_869409 : Nat := 4983230072969 + 3 ^ 40 * 869409 * 2
def baseEnd_869409 : Nat := 446424702344894166989167

theorem tailTrace_869409 : CollatzResearch.WordTrace tailWord_869409 prefixEnd_869409 446424702344894166989167 := by
  unfold tailWord_869409
  simp only [CollatzResearch.WordTrace]
  refine ⟨31709951307287151080955281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21139967538191434053970187 31709951307287151080955281)
  ·
    refine ⟨23782463480465363310716461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31709951307287151080955281 23782463480465363310716461)
    ·
      refine ⟨8918423805174511241518673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23782463480465363310716461 8918423805174511241518673)
      ·
        refine ⟨6688817853880883431139005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8918423805174511241518673 6688817853880883431139005)
        ·
          refine ⟨2508306695205331286677127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6688817853880883431139005 2508306695205331286677127)
          ·
            refine ⟨3762460042807996930015691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508306695205331286677127 3762460042807996930015691)
            ·
              refine ⟨5643690064211995395023537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762460042807996930015691 5643690064211995395023537)
              ·
                refine ⟨4232767548158996546267653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643690064211995395023537 4232767548158996546267653)
                ·
                  refine ⟨793643915279811852425185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4232767548158996546267653 793643915279811852425185)
                  ·
                    refine ⟨595232936459858889318889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 793643915279811852425185 595232936459858889318889)
                    ·
                      refine ⟨446424702344894166989167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595232936459858889318889 446424702344894166989167)
                      ·
                        rfl

theorem cell23_869409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_869409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869409 prefixEnd_869409 := by exact prefixLift 869409
  have htrace : WordTrace (prefixWord ++ tailWord_869409) baseStart_869409 baseEnd_869409 := by
    simpa [prefixWord, tailWord_869409, baseEnd_869409] using wordTrace_append hprefix tailTrace_869409
  have hstable : (prefixWord ++ tailWord_869409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869409).length < 2 ^ (prefixWord ++ tailWord_869409).sum := by decide
  have hdescent : baseEnd_869409 < baseStart_869409 := by decide
  rcases family_descends (prefixWord ++ tailWord_869409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869412 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_869412 : Nat := 118140960795 + 869412 * 2 ^ 59
def prefixEnd_869412 : Nat := 4983230072969 + 3 ^ 40 * 869412 * 2
def baseEnd_869412 : Nat := 446426242786857655251653

theorem tailTrace_869412 : CollatzResearch.WordTrace tailWord_869412 prefixEnd_869412 446426242786857655251653 := by
  unfold tailWord_869412
  simp only [CollatzResearch.WordTrace]
  refine ⟨15855030363138141296657245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21140040484184188395542993 15855030363138141296657245)
  ·
    refine ⟨5945636386176802986246467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15855030363138141296657245 5945636386176802986246467)
    ·
      refine ⟨8918454579265204479369701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5945636386176802986246467 8918454579265204479369701)
      ·
        refine ⟨1672210233612225839881819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8918454579265204479369701 1672210233612225839881819)
        ·
          refine ⟨2508315350418338759822729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672210233612225839881819 2508315350418338759822729)
          ·
            refine ⟨1881236512813754069867047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508315350418338759822729 1881236512813754069867047)
            ·
              refine ⟨2821854769220631104800571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881236512813754069867047 2821854769220631104800571)
              ·
                refine ⟨4232782153830946657200857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821854769220631104800571 4232782153830946657200857)
                ·
                  refine ⟨3174586615373209992900643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232782153830946657200857 3174586615373209992900643)
                  ·
                    refine ⟨4761879923059814989350965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174586615373209992900643 4761879923059814989350965)
                    ·
                      refine ⟨446426242786857655251653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4761879923059814989350965 446426242786857655251653)
                      ·
                        rfl

theorem cell23_869412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_869412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869412 prefixEnd_869412 := by exact prefixLift 869412
  have htrace : WordTrace (prefixWord ++ tailWord_869412) baseStart_869412 baseEnd_869412 := by
    simpa [prefixWord, tailWord_869412, baseEnd_869412] using wordTrace_append hprefix tailTrace_869412
  have hstable : (prefixWord ++ tailWord_869412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869412).length < 2 ^ (prefixWord ++ tailWord_869412).sum := by decide
  have hdescent : baseEnd_869412 < baseStart_869412 := by decide
  rcases family_descends (prefixWord ++ tailWord_869412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869432 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 7]
def baseStart_869432 : Nat := 118140960795 + 869432 * 2 ^ 59
def prefixEnd_869432 : Nat := 4983230072969 + 3 ^ 40 * 869432 * 2
def baseEnd_869432 : Nat := 49604056933327508555729

theorem tailTrace_869432 : CollatzResearch.WordTrace tailWord_869432 prefixEnd_869432 49604056933327508555729 := by
  unfold tailWord_869432
  simp only [CollatzResearch.WordTrace]
  refine ⟨15855395093101913004521275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21140526790802550672695033 15855395093101913004521275)
  ·
    refine ⟨23783092639652869506781913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15855395093101913004521275 23783092639652869506781913)
    ·
      refine ⟨17837319479739652130086435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23783092639652869506781913 17837319479739652130086435)
      ·
        refine ⟨26755979219609478195129653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17837319479739652130086435 26755979219609478195129653)
        ·
          refine ⟨2508373051838388580793405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26755979219609478195129653 2508373051838388580793405)
          ·
            refine ⟨940639894439395717797527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2508373051838388580793405 940639894439395717797527)
            ·
              refine ⟨1410959841659093576696291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940639894439395717797527 1410959841659093576696291)
              ·
                refine ⟨2116439762488640365044437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410959841659093576696291 2116439762488640365044437)
                ·
                  refine ⟨49604056933327508555729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2116439762488640365044437 49604056933327508555729)
                  ·
                    rfl

theorem cell23_869432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 7].length) (baseStart_869432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869432 prefixEnd_869432 := by exact prefixLift 869432
  have htrace : WordTrace (prefixWord ++ tailWord_869432) baseStart_869432 baseEnd_869432 := by
    simpa [prefixWord, tailWord_869432, baseEnd_869432] using wordTrace_append hprefix tailTrace_869432
  have hstable : (prefixWord ++ tailWord_869432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869432).length < 2 ^ (prefixWord ++ tailWord_869432).sum := by decide
  have hdescent : baseEnd_869432 < baseStart_869432 := by decide
  rcases family_descends (prefixWord ++ tailWord_869432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869509 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_869509 : Nat := 118140960795 + 869509 * 2 ^ 59
def prefixEnd_869509 : Nat := 4983230072969 + 3 ^ 40 * 869509 * 2
def baseEnd_869509 : Nat := 148825350136781258579569

theorem tailTrace_869509 : CollatzResearch.WordTrace tailWord_869509 prefixEnd_869509 148825350136781258579569 := by
  unfold tailWord_869509
  simp only [CollatzResearch.WordTrace]
  refine ⟨31713598606924868159595581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21142399071283245439730387 31713598606924868159595581)
  ·
    refine ⟨11892599477596825559848343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31713598606924868159595581 11892599477596825559848343)
    ·
      refine ⟨17838899216395238339772515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11892599477596825559848343 17838899216395238339772515)
      ·
        refine ⟨26758348824592857509658773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17838899216395238339772515 26758348824592857509658773)
        ·
          refine ⟨1254297601152790195765255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26758348824592857509658773 1254297601152790195765255)
          ·
            refine ⟨1881446401729185293647883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254297601152790195765255 1881446401729185293647883)
            ·
              refine ⟨2822169602593777940471825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881446401729185293647883 2822169602593777940471825)
              ·
                refine ⟨2116627201945333455353869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822169602593777940471825 2116627201945333455353869)
                ·
                  refine ⟨793735200729500045757701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2116627201945333455353869 793735200729500045757701)
                  ·
                    refine ⟨148825350136781258579569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793735200729500045757701 148825350136781258579569)
                    ·
                      rfl

theorem cell23_869509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_869509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869509 prefixEnd_869509 := by exact prefixLift 869509
  have htrace : WordTrace (prefixWord ++ tailWord_869509) baseStart_869509 baseEnd_869509 := by
    simpa [prefixWord, tailWord_869509, baseEnd_869509] using wordTrace_append hprefix tailTrace_869509
  have hstable : (prefixWord ++ tailWord_869509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869509).length < 2 ^ (prefixWord ++ tailWord_869509).sum := by decide
  have hdescent : baseEnd_869509 < baseStart_869509 := by decide
  rcases family_descends (prefixWord ++ tailWord_869509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869566 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_869566 : Nat := 118140960795 + 869566 * 2 ^ 59
def prefixEnd_869566 : Nat := 4983230072969 + 3 ^ 40 * 869566 * 2
def baseEnd_869566 : Nat := 446505318807650052725945

theorem tailTrace_869566 : CollatzResearch.WordTrace tailWord_869566 prefixEnd_869566 446505318807650052725945 := by
  unfold tailWord_869566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964459695964795861802569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21143785045145577929613701 3964459695964795861802569)
  ·
    refine ⟨2973344771973596896351927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3964459695964795861802569 2973344771973596896351927)
    ·
      refine ⟨4460017157960395344527891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2973344771973596896351927 4460017157960395344527891)
      ·
        refine ⟨6690025736940593016791837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4460017157960395344527891 6690025736940593016791837)
        ·
          refine ⟨2508759651352722381296939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6690025736940593016791837 2508759651352722381296939)
          ·
            refine ⟨3763139477029083571945409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508759651352722381296939 3763139477029083571945409)
            ·
              refine ⟨2822354607771812678959057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763139477029083571945409 2822354607771812678959057)
              ·
                refine ⟨2116765955828859509219293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822354607771812678959057 2116765955828859509219293)
                ·
                  refine ⟨793787233435822315957235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2116765955828859509219293 793787233435822315957235)
                  ·
                    refine ⟨1190680850153733473935853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 793787233435822315957235 1190680850153733473935853)
                    ·
                      refine ⟨446505318807650052725945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1190680850153733473935853 446505318807650052725945)
                      ·
                        rfl

theorem cell23_869566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_869566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869566 prefixEnd_869566 := by exact prefixLift 869566
  have htrace : WordTrace (prefixWord ++ tailWord_869566) baseStart_869566 baseEnd_869566 := by
    simpa [prefixWord, tailWord_869566, baseEnd_869566] using wordTrace_append hprefix tailTrace_869566
  have hstable : (prefixWord ++ tailWord_869566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869566).length < 2 ^ (prefixWord ++ tailWord_869566).sum := by decide
  have hdescent : baseEnd_869566 < baseStart_869566 := by decide
  rcases family_descends (prefixWord ++ tailWord_869566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869612 : List Nat := [2, 2, 1, 1, 2, 5, 2, 8]
def baseStart_869612 : Nat := 118140960795 + 869612 * 2 ^ 59
def prefixEnd_869612 : Nat := 4983230072969 + 3 ^ 40 * 869612 * 2
def baseEnd_869612 : Nat := 16538108848805810101879

theorem tailTrace_869612 : CollatzResearch.WordTrace tailWord_869612 prefixEnd_869612 16538108848805810101879 := by
  unfold tailWord_869612
  simp only [CollatzResearch.WordTrace]
  refine ⟨15858677662775858375297545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21144903550367811167063393 15858677662775858375297545)
  ·
    refine ⟨11894008247081893781473159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15858677662775858375297545 11894008247081893781473159)
    ·
      refine ⟨17841012370622840672209739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894008247081893781473159 17841012370622840672209739)
      ·
        refine ⟨26761518555934261008314609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17841012370622840672209739 26761518555934261008314609)
        ·
          refine ⟨20071138916950695756235957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26761518555934261008314609 20071138916950695756235957)
          ·
            refine ⟨1881669273464127727147121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20071138916950695756235957 1881669273464127727147121)
            ·
              refine ⟨1411251955098095795360341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881669273464127727147121 1411251955098095795360341)
              ·
                refine ⟨16538108848805810101879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1411251955098095795360341 16538108848805810101879)
                ·
                  rfl

theorem cell23_869612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 8].length) (baseStart_869612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869612 prefixEnd_869612 := by exact prefixLift 869612
  have htrace : WordTrace (prefixWord ++ tailWord_869612) baseStart_869612 baseEnd_869612 := by
    simpa [prefixWord, tailWord_869612, baseEnd_869612] using wordTrace_append hprefix tailTrace_869612
  have hstable : (prefixWord ++ tailWord_869612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869612).length < 2 ^ (prefixWord ++ tailWord_869612).sum := by decide
  have hdescent : baseEnd_869612 < baseStart_869612 := by decide
  rcases family_descends (prefixWord ++ tailWord_869612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869650 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_869650 : Nat := 118140960795 + 869650 * 2 ^ 59
def prefixEnd_869650 : Nat := 4983230072969 + 3 ^ 40 * 869650 * 2
def baseEnd_869650 : Nat := 148849483727542574691853

theorem tailTrace_869650 : CollatzResearch.WordTrace tailWord_869650 prefixEnd_869650 148849483727542574691853 := by
  unfold tailWord_869650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929685324853512310119601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21145827532942699493652269 7929685324853512310119601)
  ·
    refine ⟨5947263993640134232589701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7929685324853512310119601 5947263993640134232589701)
    ·
      refine ⟨1115111998807525168610569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5947263993640134232589701 1115111998807525168610569)
      ·
        refine ⟨836333999105643876457927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1115111998807525168610569 836333999105643876457927)
        ·
          refine ⟨1254500998658465814686891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836333999105643876457927 1254500998658465814686891)
          ·
            refine ⟨1881751497987698722030337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254500998658465814686891 1881751497987698722030337)
            ·
              refine ⟨1411313623490774041522753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881751497987698722030337 1411313623490774041522753)
              ·
                refine ⟨1058485217618080531142065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411313623490774041522753 1058485217618080531142065)
                ·
                  refine ⟨793863913213560398356549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058485217618080531142065 793863913213560398356549)
                  ·
                    refine ⟨148849483727542574691853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793863913213560398356549 148849483727542574691853)
                    ·
                      rfl

theorem cell23_869650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_869650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869650 prefixEnd_869650 := by exact prefixLift 869650
  have htrace : WordTrace (prefixWord ++ tailWord_869650) baseStart_869650 baseEnd_869650 := by
    simpa [prefixWord, tailWord_869650, baseEnd_869650] using wordTrace_append hprefix tailTrace_869650
  have hstable : (prefixWord ++ tailWord_869650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869650).length < 2 ^ (prefixWord ++ tailWord_869650).sum := by decide
  have hdescent : baseEnd_869650 < baseStart_869650 := by decide
  rcases family_descends (prefixWord ++ tailWord_869650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869656 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_869656 : Nat := 118140960795 + 869656 * 2 ^ 59
def prefixEnd_869656 : Nat := 4983230072969 + 3 ^ 40 * 869656 * 2
def baseEnd_869656 : Nat := 446551532066554700600531

theorem tailTrace_869656 : CollatzResearch.WordTrace tailWord_869656 prefixEnd_869656 446551532066554700600531 := by
  unfold tailWord_869656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15859480068696156132598411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21145973424928208176797881 15859480068696156132598411)
  ·
    refine ⟨23789220103044234198897617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15859480068696156132598411 23789220103044234198897617)
    ·
      refine ⟨17841915077283175649173213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23789220103044234198897617 17841915077283175649173213)
      ·
        refine ⟨6690718153981190868439955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17841915077283175649173213 6690718153981190868439955)
        ·
          refine ⟨10036077230971786302659933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6690718153981190868439955 10036077230971786302659933)
          ·
            refine ⟨3763528961614419863497475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10036077230971786302659933 3763528961614419863497475)
            ·
              refine ⟨5645293442421629795246213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763528961614419863497475 5645293442421629795246213)
              ·
                refine ⟨1058492520454055586608665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5645293442421629795246213 1058492520454055586608665)
                ·
                  refine ⟨793869390340541689956499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058492520454055586608665 793869390340541689956499)
                  ·
                    refine ⟨1190804085510812534934749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 793869390340541689956499 1190804085510812534934749)
                    ·
                      refine ⟨446551532066554700600531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1190804085510812534934749 446551532066554700600531)
                      ·
                        rfl

theorem cell23_869656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_869656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869656 prefixEnd_869656 := by exact prefixLift 869656
  have htrace : WordTrace (prefixWord ++ tailWord_869656) baseStart_869656 baseEnd_869656 := by
    simpa [prefixWord, tailWord_869656, baseEnd_869656] using wordTrace_append hprefix tailTrace_869656
  have hstable : (prefixWord ++ tailWord_869656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869656).length < 2 ^ (prefixWord ++ tailWord_869656).sum := by decide
  have hdescent : baseEnd_869656 < baseStart_869656 := by decide
  rcases family_descends (prefixWord ++ tailWord_869656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869696 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 4, 2, 2]
def baseStart_869696 : Nat := 118140960795 + 869696 * 2 ^ 59
def prefixEnd_869696 : Nat := 4983230072969 + 3 ^ 40 * 869696 * 2
def baseEnd_869696 : Nat := 446572071292734544100347

theorem tailTrace_869696 : CollatzResearch.WordTrace tailWord_869696 prefixEnd_869696 446572071292734544100347 := by
  unfold tailWord_869696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860209528623699548326471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21146946038164932731101961 15860209528623699548326471)
  ·
    refine ⟨23790314292935549322489707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15860209528623699548326471 23790314292935549322489707)
    ·
      refine ⟨35685471439403323983734561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23790314292935549322489707 35685471439403323983734561)
      ·
        refine ⟨26764103579552492987800921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35685471439403323983734561 26764103579552492987800921)
        ·
          refine ⟨20073077684664369740850691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26764103579552492987800921 20073077684664369740850691)
          ·
            refine ⟨30109616526996554611276037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20073077684664369740850691 30109616526996554611276037)
            ·
              refine ⟨5645553098811853989614257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30109616526996554611276037 5645553098811853989614257)
              ·
                refine ⟨4234164824108890492210693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5645553098811853989614257 4234164824108890492210693)
                ·
                  refine ⟨793905904520416967289505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4234164824108890492210693 793905904520416967289505)
                  ·
                    refine ⟨595429428390312725467129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 793905904520416967289505 595429428390312725467129)
                    ·
                      refine ⟨446572071292734544100347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595429428390312725467129 446572071292734544100347)
                      ·
                        rfl

theorem cell23_869696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_869696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869696 prefixEnd_869696 := by exact prefixLift 869696
  have htrace : WordTrace (prefixWord ++ tailWord_869696) baseStart_869696 baseEnd_869696 := by
    simpa [prefixWord, tailWord_869696, baseEnd_869696] using wordTrace_append hprefix tailTrace_869696
  have hstable : (prefixWord ++ tailWord_869696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869696).length < 2 ^ (prefixWord ++ tailWord_869696).sum := by decide
  have hdescent : baseEnd_869696 < baseStart_869696 := by decide
  rcases family_descends (prefixWord ++ tailWord_869696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869700 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_869700 : Nat := 118140960795 + 869700 * 2 ^ 59
def prefixEnd_869700 : Nat := 4983230072969 + 3 ^ 40 * 869700 * 2
def baseEnd_869700 : Nat := 446574125215352528450329

theorem tailTrace_869700 : CollatzResearch.WordTrace tailWord_869700 prefixEnd_869700 446574125215352528450329 := by
  unfold tailWord_869700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860282474616453889899277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21147043299488605186532369 15860282474616453889899277)
  ·
    refine ⟨5947605927981170208712229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15860282474616453889899277 5947605927981170208712229)
    ·
      refine ⟨1115176111496469414133543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5947605927981170208712229 1115176111496469414133543)
      ·
        refine ⟨1672764167244704121200315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115176111496469414133543 1672764167244704121200315)
        ·
          refine ⟨2509146250867056181800473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672764167244704121200315 2509146250867056181800473)
          ·
            refine ⟨1881859688150292136350355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509146250867056181800473 1881859688150292136350355)
            ·
              refine ⟨2822789532225438204525533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881859688150292136350355 2822789532225438204525533)
              ·
                refine ⟨1058546074584539326697075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2822789532225438204525533 1058546074584539326697075)
                ·
                  refine ⟨1587819111876808990045613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058546074584539326697075 1587819111876808990045613)
                  ·
                    refine ⟨595432166953803371267105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587819111876808990045613 595432166953803371267105)
                    ·
                      refine ⟨446574125215352528450329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595432166953803371267105 446574125215352528450329)
                      ·
                        rfl

theorem cell23_869700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_869700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869700 prefixEnd_869700 := by exact prefixLift 869700
  have htrace : WordTrace (prefixWord ++ tailWord_869700) baseStart_869700 baseEnd_869700 := by
    simpa [prefixWord, tailWord_869700, baseEnd_869700] using wordTrace_append hprefix tailTrace_869700
  have hstable : (prefixWord ++ tailWord_869700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869700).length < 2 ^ (prefixWord ++ tailWord_869700).sum := by decide
  have hdescent : baseEnd_869700 < baseStart_869700 := by decide
  rcases family_descends (prefixWord ++ tailWord_869700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869719 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 7]
def baseStart_869719 : Nat := 118140960795 + 869719 * 2 ^ 59
def prefixEnd_869719 : Nat := 4983230072969 + 3 ^ 40 * 869719 * 2
def baseEnd_869719 : Nat := 49620431260865328234749

theorem tailTrace_869719 : CollatzResearch.WordTrace tailWord_869719 prefixEnd_869719 49620431260865328234749 := by
  unfold tailWord_869719
  simp only [CollatzResearch.WordTrace]
  refine ⟨31721257936164074024740211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21147505290776049349826807 31721257936164074024740211)
  ·
    refine ⟨47581886904246111037110317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31721257936164074024740211 47581886904246111037110317)
    ·
      refine ⟨17843207589092291638916369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47581886904246111037110317 17843207589092291638916369)
      ·
        refine ⟨13382405691819218729187277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17843207589092291638916369 13382405691819218729187277)
        ·
          refine ⟨5018402134432207023445229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13382405691819218729187277 5018402134432207023445229)
          ·
            refine ⟨1881900800412077633791961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5018402134432207023445229 1881900800412077633791961)
            ·
              refine ⟨1411425600309058225343971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881900800412077633791961 1411425600309058225343971)
              ·
                refine ⟨2117138400463587338015957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411425600309058225343971 2117138400463587338015957)
                ·
                  refine ⟨49620431260865328234749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2117138400463587338015957 49620431260865328234749)
                  ·
                    rfl

theorem cell23_869719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 7].length) (baseStart_869719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869719 prefixEnd_869719 := by exact prefixLift 869719
  have htrace : WordTrace (prefixWord ++ tailWord_869719) baseStart_869719 baseEnd_869719 := by
    simpa [prefixWord, tailWord_869719, baseEnd_869719] using wordTrace_append hprefix tailTrace_869719
  have hstable : (prefixWord ++ tailWord_869719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869719).length < 2 ^ (prefixWord ++ tailWord_869719).sum := by decide
  have hdescent : baseEnd_869719 < baseStart_869719 := by decide
  rcases family_descends (prefixWord ++ tailWord_869719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869786 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2]
def baseStart_869786 : Nat := 118140960795 + 869786 * 2 ^ 59
def prefixEnd_869786 : Nat := 4983230072969 + 3 ^ 40 * 869786 * 2
def baseEnd_869786 : Nat := 446618284551639191974933

theorem tailTrace_869786 : CollatzResearch.WordTrace tailWord_869786 prefixEnd_869786 446618284551639191974933 := by
  unfold tailWord_869786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7930925406730336116857303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21149134417947562978286141 7930925406730336116857303)
  ·
    refine ⟨11896388110095504175285955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7930925406730336116857303 11896388110095504175285955)
    ·
      refine ⟨17844582165143256262928933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896388110095504175285955 17844582165143256262928933)
      ·
        refine ⟨3345859155964360549299175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17844582165143256262928933 3345859155964360549299175)
        ·
          refine ⟨5018788733946540823948763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345859155964360549299175 5018788733946540823948763)
          ·
            refine ⟨7528183100919811235923145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5018788733946540823948763 7528183100919811235923145)
            ·
              refine ⟨5646137325689858426942359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7528183100919811235923145 5646137325689858426942359)
              ·
                refine ⟨8469205988534787640413539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646137325689858426942359 8469205988534787640413539)
                ·
                  refine ⟨12703808982802181460620309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8469205988534787640413539 12703808982802181460620309)
                  ·
                    refine ⟨595491046068852255966577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12703808982802181460620309 595491046068852255966577)
                    ·
                      refine ⟨446618284551639191974933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595491046068852255966577 446618284551639191974933)
                      ·
                        rfl

theorem cell23_869786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_869786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869786 prefixEnd_869786 := by exact prefixLift 869786
  have htrace : WordTrace (prefixWord ++ tailWord_869786) baseStart_869786 baseEnd_869786 := by
    simpa [prefixWord, tailWord_869786, baseEnd_869786] using wordTrace_append hprefix tailTrace_869786
  have hstable : (prefixWord ++ tailWord_869786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869786).length < 2 ^ (prefixWord ++ tailWord_869786).sum := by decide
  have hdescent : baseEnd_869786 < baseStart_869786 := by decide
  rcases family_descends (prefixWord ++ tailWord_869786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869839 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 3, 5]
def baseStart_869839 : Nat := 118140960795 + 869839 * 2 ^ 59
def prefixEnd_869839 : Nat := 4983230072969 + 3 ^ 40 * 869839 * 2
def baseEnd_869839 : Nat := 148881833008775828204063

theorem tailTrace_869839 : CollatzResearch.WordTrace tailWord_869839 prefixEnd_869839 148881833008775828204063 := by
  unfold tailWord_869839
  simp only [CollatzResearch.WordTrace]
  refine ⟨31725634695729334519108571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21150423130486223012739047 31725634695729334519108571)
  ·
    refine ⟨47588452043594001778662857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31725634695729334519108571 47588452043594001778662857)
    ·
      refine ⟨35691339032695501333997143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47588452043594001778662857 35691339032695501333997143)
      ·
        refine ⟨53537008549043252000995715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35691339032695501333997143 53537008549043252000995715)
        ·
          refine ⟨80305512823564878001493573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53537008549043252000995715 80305512823564878001493573)
          ·
            refine ⟨15057283654418414625280045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80305512823564878001493573 15057283654418414625280045)
            ·
              refine ⟨5646481370406905484480017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15057283654418414625280045 5646481370406905484480017)
              ·
                refine ⟨4234861027805179113360013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5646481370406905484480017 4234861027805179113360013)
                ·
                  refine ⟨1588072885426942167510005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4234861027805179113360013 1588072885426942167510005)
                  ·
                    refine ⟨148881833008775828204063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1588072885426942167510005 148881833008775828204063)
                    ·
                      rfl

theorem cell23_869839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_869839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869839 prefixEnd_869839 := by exact prefixLift 869839
  have htrace : WordTrace (prefixWord ++ tailWord_869839) baseStart_869839 baseEnd_869839 := by
    simpa [prefixWord, tailWord_869839, baseEnd_869839] using wordTrace_append hprefix tailTrace_869839
  have hstable : (prefixWord ++ tailWord_869839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869839).length < 2 ^ (prefixWord ++ tailWord_869839).sum := by decide
  have hdescent : baseEnd_869839 < baseStart_869839 := by decide
  rcases family_descends (prefixWord ++ tailWord_869839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869853 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_869853 : Nat := 118140960795 + 869853 * 2 ^ 59
def prefixEnd_869853 : Nat := 4983230072969 + 3 ^ 40 * 869853 * 2
def baseEnd_869853 : Nat := 446652687755490429837125

theorem tailTrace_869853 : CollatzResearch.WordTrace tailWord_869853 prefixEnd_869853 446652687755490429837125 := by
  unfold tailWord_869853
  simp only [CollatzResearch.WordTrace]
  refine ⟨31726145317678614910118213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21150763545119076606745475 31726145317678614910118213)
  ·
    refine ⟨5948652247064740295647165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31726145317678614910118213 5948652247064740295647165)
    ·
      refine ⟨2230744592649277610867687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5948652247064740295647165 2230744592649277610867687)
      ·
        refine ⟨3346116888973916416301531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230744592649277610867687 3346116888973916416301531)
        ·
          refine ⟨5019175333460874624452297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346116888973916416301531 5019175333460874624452297)
          ·
            refine ⟨3764381500095655968339223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019175333460874624452297 3764381500095655968339223)
            ·
              refine ⟨5646572250143483952508835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764381500095655968339223 5646572250143483952508835)
              ·
                refine ⟨8469858375215225928763253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646572250143483952508835 8469858375215225928763253)
                ·
                  refine ⟨794049222676427430821555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8469858375215225928763253 794049222676427430821555)
                  ·
                    refine ⟨1191073834014641146232333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 794049222676427430821555 1191073834014641146232333)
                    ·
                      refine ⟨446652687755490429837125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1191073834014641146232333 446652687755490429837125)
                      ·
                        rfl

theorem cell23_869853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_869853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869853 prefixEnd_869853 := by exact prefixLift 869853
  have htrace : WordTrace (prefixWord ++ tailWord_869853) baseStart_869853 baseEnd_869853 := by
    simpa [prefixWord, tailWord_869853, baseEnd_869853] using wordTrace_append hprefix tailTrace_869853
  have hstable : (prefixWord ++ tailWord_869853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869853).length < 2 ^ (prefixWord ++ tailWord_869853).sum := by decide
  have hdescent : baseEnd_869853 < baseStart_869853 := by decide
  rcases family_descends (prefixWord ++ tailWord_869853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869863 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_869863 : Nat := 118140960795 + 869863 * 2 ^ 59
def prefixEnd_869863 : Nat := 4983230072969 + 3 ^ 40 * 869863 * 2
def baseEnd_869863 : Nat := 446657822562035390712079

theorem tailTrace_869863 : CollatzResearch.WordTrace tailWord_869863 prefixEnd_869863 446657822562035390712079 := by
  unfold tailWord_869863
  simp only [CollatzResearch.WordTrace]
  refine ⟨31726510047642386617982243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21151006698428257745321495 31726510047642386617982243)
  ·
    refine ⟨47589765071463579926973365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31726510047642386617982243 47589765071463579926973365)
    ·
      refine ⟨4461540475449710618153753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47589765071463579926973365 4461540475449710618153753)
      ·
        refine ⟨3346155356587282963615315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4461540475449710618153753 3346155356587282963615315)
        ·
          refine ⟨5019233034880924445422973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346155356587282963615315 5019233034880924445422973)
          ·
            refine ⟨1882212388080346667033615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5019233034880924445422973 1882212388080346667033615)
            ·
              refine ⟨2823318582120520000550423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882212388080346667033615 2823318582120520000550423)
              ·
                refine ⟨4234977873180780000825635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823318582120520000550423 4234977873180780000825635)
                ·
                  refine ⟨6352466809771170001238453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234977873180780000825635 6352466809771170001238453)
                  ·
                    refine ⟨595543763416047187616105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6352466809771170001238453 595543763416047187616105)
                    ·
                      refine ⟨446657822562035390712079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595543763416047187616105 446657822562035390712079)
                      ·
                        rfl

theorem cell23_869863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_869863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869863 prefixEnd_869863 := by exact prefixLift 869863
  have htrace : WordTrace (prefixWord ++ tailWord_869863) baseStart_869863 baseEnd_869863 := by
    simpa [prefixWord, tailWord_869863, baseEnd_869863] using wordTrace_append hprefix tailTrace_869863
  have hstable : (prefixWord ++ tailWord_869863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869863).length < 2 ^ (prefixWord ++ tailWord_869863).sum := by decide
  have hdescent : baseEnd_869863 < baseStart_869863 := by decide
  rcases family_descends (prefixWord ++ tailWord_869863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869873 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 1, 5]
def baseStart_869873 : Nat := 118140960795 + 869873 * 2 ^ 59
def prefixEnd_869873 : Nat := 4983230072969 + 3 ^ 40 * 869873 * 2
def baseEnd_869873 : Nat := 148887652456193450529011

theorem tailTrace_869873 : CollatzResearch.WordTrace tailWord_869873 prefixEnd_869873 148887652456193450529011 := by
  unfold tailWord_869873
  simp only [CollatzResearch.WordTrace]
  refine ⟨31726874777606158325846273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21151249851737438883897515 31726874777606158325846273)
  ·
    refine ⟨23795156083204618744384705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31726874777606158325846273 23795156083204618744384705)
    ·
      refine ⟨17846367062403464058288529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23795156083204618744384705 17846367062403464058288529)
      ·
        refine ⟨13384775296802598043716397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17846367062403464058288529 13384775296802598043716397)
        ·
          refine ⟨5019290736300974266393649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13384775296802598043716397 5019290736300974266393649)
          ·
            refine ⟨3764468052225730699795237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019290736300974266393649 3764468052225730699795237)
            ·
              refine ⟨705837759792324506211607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3764468052225730699795237 705837759792324506211607)
              ·
                refine ⟨1058756639688486759317411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705837759792324506211607 1058756639688486759317411)
                ·
                  refine ⟨1588134959532730138976117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058756639688486759317411 1588134959532730138976117)
                  ·
                    refine ⟨148887652456193450529011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1588134959532730138976117 148887652456193450529011)
                    ·
                      rfl

theorem cell23_869873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_869873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869873 prefixEnd_869873 := by exact prefixLift 869873
  have htrace : WordTrace (prefixWord ++ tailWord_869873) baseStart_869873 baseEnd_869873 := by
    simpa [prefixWord, tailWord_869873, baseEnd_869873] using wordTrace_append hprefix tailTrace_869873
  have hstable : (prefixWord ++ tailWord_869873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869873).length < 2 ^ (prefixWord ++ tailWord_869873).sum := by decide
  have hdescent : baseEnd_869873 < baseStart_869873 := by decide
  rcases family_descends (prefixWord ++ tailWord_869873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869894 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_869894 : Nat := 118140960795 + 869894 * 2 ^ 59
def prefixEnd_869894 : Nat := 4983230072969 + 3 ^ 40 * 869894 * 2
def baseEnd_869894 : Nat := 49630415606924974380493

theorem tailTrace_869894 : CollatzResearch.WordTrace tailWord_869894 prefixEnd_869894 49630415606924974380493 := by
  unfold tailWord_869894
  simp only [CollatzResearch.WordTrace]
  refine ⟨991488772204064966011273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21151760473686719274907157 991488772204064966011273)
  ·
    refine ⟨743616579153048724508455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 991488772204064966011273 743616579153048724508455)
    ·
      refine ⟨1115424868729573086762683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743616579153048724508455 1115424868729573086762683)
      ·
        refine ⟨1673137303094359630144025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115424868729573086762683 1673137303094359630144025)
        ·
          refine ⟨1254852977320769722608019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1673137303094359630144025 1254852977320769722608019)
          ·
            refine ⟨1882279465981154583912029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254852977320769722608019 1882279465981154583912029)
            ·
              refine ⟨705854799742932968967011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1882279465981154583912029 705854799742932968967011)
              ·
                refine ⟨1058782199614399453450517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705854799742932968967011 1058782199614399453450517)
                ·
                  refine ⟨49630415606924974380493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1058782199614399453450517 49630415606924974380493)
                  ·
                    rfl

theorem cell23_869894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_869894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869894 prefixEnd_869894 := by exact prefixLift 869894
  have htrace : WordTrace (prefixWord ++ tailWord_869894) baseStart_869894 baseEnd_869894 := by
    simpa [prefixWord, tailWord_869894, baseEnd_869894] using wordTrace_append hprefix tailTrace_869894
  have hstable : (prefixWord ++ tailWord_869894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869894).length < 2 ^ (prefixWord ++ tailWord_869894).sum := by decide
  have hdescent : baseEnd_869894 < baseStart_869894 := by decide
  rcases family_descends (prefixWord ++ tailWord_869894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869896 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_869896 : Nat := 118140960795 + 869896 * 2 ^ 59
def prefixEnd_869896 : Nat := 4983230072969 + 3 ^ 40 * 869896 * 2
def baseEnd_869896 : Nat := 446674767423633761599427

theorem tailTrace_869896 : CollatzResearch.WordTrace tailWord_869896 prefixEnd_869896 446674767423633761599427 := by
  unfold tailWord_869896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863856828261416626966771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21151809104348555502622361 15863856828261416626966771)
  ·
    refine ⟨23795785242392124940450157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15863856828261416626966771 23795785242392124940450157)
    ·
      refine ⟨8923419465897046852668809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23795785242392124940450157 8923419465897046852668809)
      ·
        refine ⟨6692564599422785139501607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8923419465897046852668809 6692564599422785139501607)
        ·
          refine ⟨10038846899134177709252411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6692564599422785139501607 10038846899134177709252411)
          ·
            refine ⟨15058270348701266563878617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10038846899134177709252411 15058270348701266563878617)
            ·
              refine ⟨11293702761525949922908963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15058270348701266563878617 11293702761525949922908963)
              ·
                refine ⟨16940554142288924884363445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293702761525949922908963 16940554142288924884363445)
                ·
                  refine ⟨1588176950839586707909073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16940554142288924884363445 1588176950839586707909073)
                  ·
                    refine ⟨1191132713129690030931805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588176950839586707909073 1191132713129690030931805)
                    ·
                      refine ⟨446674767423633761599427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1191132713129690030931805 446674767423633761599427)
                      ·
                        rfl

theorem cell23_869896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_869896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869896 prefixEnd_869896 := by exact prefixLift 869896
  have htrace : WordTrace (prefixWord ++ tailWord_869896) baseStart_869896 baseEnd_869896 := by
    simpa [prefixWord, tailWord_869896, baseEnd_869896] using wordTrace_append hprefix tailTrace_869896
  have hstable : (prefixWord ++ tailWord_869896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869896).length < 2 ^ (prefixWord ++ tailWord_869896).sum := by decide
  have hdescent : baseEnd_869896 < baseStart_869896 := by decide
  rcases family_descends (prefixWord ++ tailWord_869896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869943 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_869943 : Nat := 118140960795 + 869943 * 2 ^ 59
def prefixEnd_869943 : Nat := 4983230072969 + 3 ^ 40 * 869943 * 2
def baseEnd_869943 : Nat := 446698901014395077711711

theorem tailTrace_869943 : CollatzResearch.WordTrace tailWord_869943 prefixEnd_869943 446698901014395077711711 := by
  unfold tailWord_869943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31729427887352560280894483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21152951924901706853929655 31729427887352560280894483)
  ·
    refine ⟨47594141831028840421341725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31729427887352560280894483 47594141831028840421341725)
    ·
      refine ⟨17847803186635815158003147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47594141831028840421341725 17847803186635815158003147)
      ·
        refine ⟨26771704779953722737004721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17847803186635815158003147 26771704779953722737004721)
        ·
          refine ⟨20078778584965292052753541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26771704779953722737004721 20078778584965292052753541)
          ·
            refine ⟨3764770984680992259891289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20078778584965292052753541 3764770984680992259891289)
            ·
              refine ⟨2823578238510744194918467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764770984680992259891289 2823578238510744194918467)
              ·
                refine ⟨4235367357766116292377701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823578238510744194918467 4235367357766116292377701)
                ·
                  refine ⟨794131379581146804820819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4235367357766116292377701 794131379581146804820819)
                  ·
                    refine ⟨1191197069371720207231229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 794131379581146804820819 1191197069371720207231229)
                    ·
                      refine ⟨446698901014395077711711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1191197069371720207231229 446698901014395077711711)
                      ·
                        rfl

theorem cell23_869943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_869943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869943 prefixEnd_869943 := by exact prefixLift 869943
  have htrace : WordTrace (prefixWord ++ tailWord_869943) baseStart_869943 baseEnd_869943 := by
    simpa [prefixWord, tailWord_869943, baseEnd_869943] using wordTrace_append hprefix tailTrace_869943
  have hstable : (prefixWord ++ tailWord_869943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869943).length < 2 ^ (prefixWord ++ tailWord_869943).sum := by decide
  have hdescent : baseEnd_869943 < baseStart_869943 := by decide
  rcases family_descends (prefixWord ++ tailWord_869943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869944 : List Nat := [2, 1, 2, 1, 4, 3, 3, 2, 1, 2, 2]
def baseStart_869944 : Nat := 118140960795 + 869944 * 2 ^ 59
def prefixEnd_869944 : Nat := 4983230072969 + 3 ^ 40 * 869944 * 2
def baseEnd_869944 : Nat := 446699414495049573799207

theorem tailTrace_869944 : CollatzResearch.WordTrace tailWord_869944 prefixEnd_869944 446699414495049573799207 := by
  unfold tailWord_869944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15864732180174468725840443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21152976240232624967787257 15864732180174468725840443)
  ·
    refine ⟨23797098270261703088760665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15864732180174468725840443 23797098270261703088760665)
    ·
      refine ⟨17847823702696277316570499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23797098270261703088760665 17847823702696277316570499)
      ·
        refine ⟨26771735554044415974855749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17847823702696277316570499 26771735554044415974855749)
        ·
          refine ⟨5019700416383327995285453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26771735554044415974855749 5019700416383327995285453)
          ·
            refine ⟨1882387656143747998232045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5019700416383327995285453 1882387656143747998232045)
            ·
              refine ⟨705895371053905499337017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1882387656143747998232045 705895371053905499337017)
              ·
                refine ⟨529421528290429124502763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705895371053905499337017 529421528290429124502763)
                ·
                  refine ⟨794132292435643686754145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529421528290429124502763 794132292435643686754145)
                  ·
                    refine ⟨595599219326732765065609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 794132292435643686754145 595599219326732765065609)
                    ·
                      refine ⟨446699414495049573799207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595599219326732765065609 446699414495049573799207)
                      ·
                        rfl

theorem cell23_869944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_869944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869944 prefixEnd_869944 := by exact prefixLift 869944
  have htrace : WordTrace (prefixWord ++ tailWord_869944) baseStart_869944 baseEnd_869944 := by
    simpa [prefixWord, tailWord_869944, baseEnd_869944] using wordTrace_append hprefix tailTrace_869944
  have hstable : (prefixWord ++ tailWord_869944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869944).length < 2 ^ (prefixWord ++ tailWord_869944).sum := by decide
  have hdescent : baseEnd_869944 < baseStart_869944 := by decide
  rcases family_descends (prefixWord ++ tailWord_869944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869970 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_869970 : Nat := 118140960795 + 869970 * 2 ^ 59
def prefixEnd_869970 : Nat := 4983230072969 + 3 ^ 40 * 869970 * 2
def baseEnd_869970 : Nat := 446712764992066472074087

theorem tailTrace_869970 : CollatzResearch.WordTrace tailWord_869970 prefixEnd_869970 446712764992066472074087 := by
  unfold tailWord_869970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932603164563685973031841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21153608438836495928084909 7932603164563685973031841)
  ·
    refine ⟨5949452373422764479773881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7932603164563685973031841 5949452373422764479773881)
    ·
      refine ⟨4462089280067073359830411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5949452373422764479773881 4462089280067073359830411)
      ·
        refine ⟨6693133920100610039745617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462089280067073359830411 6693133920100610039745617)
        ·
          refine ⟨5019850440075457529809213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6693133920100610039745617 5019850440075457529809213)
          ·
            refine ⟨1882443915028296573678455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5019850440075457529809213 1882443915028296573678455)
            ·
              refine ⟨2823665872542444860517683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882443915028296573678455 2823665872542444860517683)
              ·
                refine ⟨4235498808813667290776525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823665872542444860517683 4235498808813667290776525)
                ·
                  refine ⟨1588312053305125234041197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4235498808813667290776525 1588312053305125234041197)
                  ·
                    refine ⟨595617019989421962765449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1588312053305125234041197 595617019989421962765449)
                    ·
                      refine ⟨446712764992066472074087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595617019989421962765449 446712764992066472074087)
                      ·
                        rfl

theorem cell23_869970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_869970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869970 prefixEnd_869970 := by exact prefixLift 869970
  have htrace : WordTrace (prefixWord ++ tailWord_869970) baseStart_869970 baseEnd_869970 := by
    simpa [prefixWord, tailWord_869970, baseEnd_869970] using wordTrace_append hprefix tailTrace_869970
  have hstable : (prefixWord ++ tailWord_869970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869970).length < 2 ^ (prefixWord ++ tailWord_869970).sum := by decide
  have hdescent : baseEnd_869970 < baseStart_869970 := by decide
  rcases family_descends (prefixWord ++ tailWord_869970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869987 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 1, 3, 2]
def baseStart_869987 : Nat := 118140960795 + 869987 * 2 ^ 59
def prefixEnd_869987 : Nat := 4983230072969 + 3 ^ 40 * 869987 * 2
def baseEnd_869987 : Nat := 446721494163192905561509

theorem tailTrace_869987 : CollatzResearch.WordTrace tailWord_869987 prefixEnd_869987 446721494163192905561509 := by
  unfold tailWord_869987
  simp only [CollatzResearch.WordTrace]
  refine ⟨31731032699193155795496215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21154021799462103863664143 31731032699193155795496215)
  ·
    refine ⟨47596549048789733693244323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31731032699193155795496215 47596549048789733693244323)
    ·
      refine ⟨71394823573184600539866485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47596549048789733693244323 71394823573184600539866485)
      ·
        refine ⟨6693264709986056300612483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71394823573184600539866485 6693264709986056300612483)
        ·
          refine ⟨10039897064979084450918725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6693264709986056300612483 10039897064979084450918725)
          ·
            refine ⟨1882480699683578334547261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10039897064979084450918725 1882480699683578334547261)
            ·
              refine ⟨705930262381341875455223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1882480699683578334547261 705930262381341875455223)
              ·
                refine ⟨1058895393572012813182835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705930262381341875455223 1058895393572012813182835)
                ·
                  refine ⟨1588343090358019219774253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058895393572012813182835 1588343090358019219774253)
                  ·
                    refine ⟨595628658884257207415345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1588343090358019219774253 595628658884257207415345)
                    ·
                      refine ⟨446721494163192905561509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595628658884257207415345 446721494163192905561509)
                      ·
                        rfl

theorem cell23_869987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_869987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869987 prefixEnd_869987 := by exact prefixLift 869987
  have htrace : WordTrace (prefixWord ++ tailWord_869987) baseStart_869987 baseEnd_869987 := by
    simpa [prefixWord, tailWord_869987, baseEnd_869987] using wordTrace_append hprefix tailTrace_869987
  have hstable : (prefixWord ++ tailWord_869987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869987).length < 2 ^ (prefixWord ++ tailWord_869987).sum := by decide
  have hdescent : baseEnd_869987 < baseStart_869987 := by decide
  rcases family_descends (prefixWord ++ tailWord_869987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869996 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_869996 : Nat := 118140960795 + 869996 * 2 ^ 59
def prefixEnd_869996 : Nat := 4983230072969 + 3 ^ 40 * 869996 * 2
def baseEnd_869996 : Nat := 446726115489083370348967

theorem tailTrace_869996 : CollatzResearch.WordTrace tailWord_869996 prefixEnd_869996 446726115489083370348967 := by
  unfold tailWord_869996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15865680478080275166286921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21154240637440366888382561 15865680478080275166286921)
  ·
    refine ⟨11899260358560206374715191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15865680478080275166286921 11899260358560206374715191)
    ·
      refine ⟨17848890537840309562072787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11899260358560206374715191 17848890537840309562072787)
      ·
        refine ⟨26773335806760464343109181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17848890537840309562072787 26773335806760464343109181)
        ·
          refine ⟨10040000927535174128665943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26773335806760464343109181 10040000927535174128665943)
          ·
            refine ⟨15060001391302761192998915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10040000927535174128665943 15060001391302761192998915)
            ·
              refine ⟨22590002086954141789498373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15060001391302761192998915 22590002086954141789498373)
              ·
                refine ⟨4235625391303901585530945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22590002086954141789498373 4235625391303901585530945)
                ·
                  refine ⟨3176719043477926189148209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235625391303901585530945 3176719043477926189148209)
                  ·
                    refine ⟨2382539282608444641861157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176719043477926189148209 2382539282608444641861157)
                    ·
                      refine ⟨446726115489083370348967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2382539282608444641861157 446726115489083370348967)
                      ·
                        rfl

theorem cell23_869996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_869996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869996 prefixEnd_869996 := by exact prefixLift 869996
  have htrace : WordTrace (prefixWord ++ tailWord_869996) baseStart_869996 baseEnd_869996 := by
    simpa [prefixWord, tailWord_869996, baseEnd_869996] using wordTrace_append hprefix tailTrace_869996
  have hstable : (prefixWord ++ tailWord_869996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869996).length < 2 ^ (prefixWord ++ tailWord_869996).sum := by decide
  have hdescent : baseEnd_869996 < baseStart_869996 := by decide
  rcases family_descends (prefixWord ++ tailWord_869996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870013 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_870013 : Nat := 118140960795 + 870013 * 2 ^ 59
def prefixEnd_870013 : Nat := 4983230072969 + 3 ^ 40 * 870013 * 2
def baseEnd_870013 : Nat := 446734844660209803836389

theorem tailTrace_870013 : CollatzResearch.WordTrace tailWord_870013 prefixEnd_870013 446734844660209803836389 := by
  unfold tailWord_870013
  simp only [CollatzResearch.WordTrace]
  refine ⟨31731980997098962235942693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21154653998065974823961795 31731980997098962235942693)
  ·
    refine ⟨5949746436956055419239255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31731980997098962235942693 5949746436956055419239255)
    ·
      refine ⟨8924619655434083128858883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949746436956055419239255 8924619655434083128858883)
      ·
        refine ⟨13386929483151124693288325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924619655434083128858883 13386929483151124693288325)
        ·
          refine ⟨2510049278090835879991561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13386929483151124693288325 2510049278090835879991561)
          ·
            refine ⟨1882536958568126909993671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2510049278090835879991561 1882536958568126909993671)
            ·
              refine ⟨2823805437852190364990507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882536958568126909993671 2823805437852190364990507)
              ·
                refine ⟨4235708156778285547485761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823805437852190364990507 4235708156778285547485761)
                ·
                  refine ⟨3176781117583714160614321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235708156778285547485761 3176781117583714160614321)
                  ·
                    refine ⟨2382585838187785620460741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176781117583714160614321 2382585838187785620460741)
                    ·
                      refine ⟨446734844660209803836389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2382585838187785620460741 446734844660209803836389)
                      ·
                        rfl

theorem cell23_870013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_870013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870013 prefixEnd_870013 := by exact prefixLift 870013
  have htrace : WordTrace (prefixWord ++ tailWord_870013) baseStart_870013 baseEnd_870013 := by
    simpa [prefixWord, tailWord_870013, baseEnd_870013] using wordTrace_append hprefix tailTrace_870013
  have hstable : (prefixWord ++ tailWord_870013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870013).length < 2 ^ (prefixWord ++ tailWord_870013).sum := by decide
  have hdescent : baseEnd_870013 < baseStart_870013 := by decide
  rcases family_descends (prefixWord ++ tailWord_870013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870017 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_870017 : Nat := 118140960795 + 870017 * 2 ^ 59
def prefixEnd_870017 : Nat := 4983230072969 + 3 ^ 40 * 870017 * 2
def baseEnd_870017 : Nat := 446736898582827788186371

theorem tailTrace_870017 : CollatzResearch.WordTrace tailWord_870017 prefixEnd_870017 446736898582827788186371 := by
  unfold tailWord_870017
  simp only [CollatzResearch.WordTrace]
  refine ⟨31732126889084470919088305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21154751259389647279392203 31732126889084470919088305)
  ·
    refine ⟨23799095166813353189316229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31732126889084470919088305 23799095166813353189316229)
    ·
      refine ⟨4462330343777503722996793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23799095166813353189316229 4462330343777503722996793)
      ·
        refine ⟨3346747757833127792247595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4462330343777503722996793 3346747757833127792247595)
        ·
          refine ⟨5020121636749691688371393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346747757833127792247595 5020121636749691688371393)
          ·
            refine ⟨3765091227562268766278545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5020121636749691688371393 3765091227562268766278545)
            ·
              refine ⟨2823818420671701574708909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765091227562268766278545 2823818420671701574708909)
              ·
                refine ⟨1058931907751888090515841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2823818420671701574708909 1058931907751888090515841)
                ·
                  refine ⟨794198930813916067886881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058931907751888090515841 794198930813916067886881)
                  ·
                    refine ⟨595649198110437050915161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 794198930813916067886881 595649198110437050915161)
                    ·
                      refine ⟨446736898582827788186371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595649198110437050915161 446736898582827788186371)
                      ·
                        rfl

theorem cell23_870017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_870017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870017 prefixEnd_870017 := by exact prefixLift 870017
  have htrace : WordTrace (prefixWord ++ tailWord_870017) baseStart_870017 baseEnd_870017 := by
    simpa [prefixWord, tailWord_870017, baseEnd_870017] using wordTrace_append hprefix tailTrace_870017
  have hstable : (prefixWord ++ tailWord_870017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870017).length < 2 ^ (prefixWord ++ tailWord_870017).sum := by decide
  have hdescent : baseEnd_870017 < baseStart_870017 := by decide
  rcases family_descends (prefixWord ++ tailWord_870017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870040 : List Nat := [2, 1, 2, 4, 1, 3, 2, 3, 5]
def baseStart_870040 : Nat := 118140960795 + 870040 * 2 ^ 59
def prefixEnd_870040 : Nat := 4983230072969 + 3 ^ 40 * 870040 * 2
def baseEnd_870040 : Nat := 49638745404209022022085

theorem tailTrace_870040 : CollatzResearch.WordTrace tailWord_870040 prefixEnd_870040 49638745404209022022085 := by
  unfold tailWord_870040
  simp only [CollatzResearch.WordTrace]
  refine ⟨15866482884000572923587787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21155310512000763898117049 15866482884000572923587787)
  ·
    refine ⟨23799724326000859385381681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15866482884000572923587787 23799724326000859385381681)
    ·
      refine ⟨17849793244500644539036261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23799724326000859385381681 17849793244500644539036261)
      ·
        refine ⟨3346836233343870851069299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17849793244500644539036261 3346836233343870851069299)
        ·
          refine ⟨5020254350015806276603949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346836233343870851069299 5020254350015806276603949)
          ·
            refine ⟨1882595381255927353726481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5020254350015806276603949 1882595381255927353726481)
            ·
              refine ⟨1411946535941945515294861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882595381255927353726481 1411946535941945515294861)
              ·
                refine ⟨529479950978229568235573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1411946535941945515294861 529479950978229568235573)
                ·
                  refine ⟨49638745404209022022085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 529479950978229568235573 49638745404209022022085)
                  ·
                    rfl

theorem cell23_870040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 5].length) (baseStart_870040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870040 prefixEnd_870040 := by exact prefixLift 870040
  have htrace : WordTrace (prefixWord ++ tailWord_870040) baseStart_870040 baseEnd_870040 := by
    simpa [prefixWord, tailWord_870040, baseEnd_870040] using wordTrace_append hprefix tailTrace_870040
  have hstable : (prefixWord ++ tailWord_870040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870040).length < 2 ^ (prefixWord ++ tailWord_870040).sum := by decide
  have hdescent : baseEnd_870040 < baseStart_870040 := by decide
  rcases family_descends (prefixWord ++ tailWord_870040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870070 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_870070 : Nat := 118140960795 + 870070 * 2 ^ 59
def prefixEnd_870070 : Nat := 4983230072969 + 3 ^ 40 * 870070 * 2
def baseEnd_870070 : Nat := 148921371019172026941209

theorem tailTrace_870070 : CollatzResearch.WordTrace tailWord_870070 prefixEnd_870070 148921371019172026941209 := by
  unfold tailWord_870070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983378747368278810672979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21156039971928307313845109 1983378747368278810672979)
  ·
    refine ⟨2975068121052418216009469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1983378747368278810672979 2975068121052418216009469)
    ·
      refine ⟨1115650545394656831003551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2975068121052418216009469 1115650545394656831003551)
      ·
        refine ⟨1673475818091985246505327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115650545394656831003551 1673475818091985246505327)
        ·
          refine ⟨2510213727137977869757991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673475818091985246505327 2510213727137977869757991)
          ·
            refine ⟨3765320590706966804636987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510213727137977869757991 3765320590706966804636987)
            ·
              refine ⟨5647980886060450206955481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765320590706966804636987 5647980886060450206955481)
              ·
                refine ⟨4235985664545337655216611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5647980886060450206955481 4235985664545337655216611)
                ·
                  refine ⟨6353978496818006482824917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235985664545337655216611 6353978496818006482824917)
                  ·
                    refine ⟨148921371019172026941209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6353978496818006482824917 148921371019172026941209)
                    ·
                      rfl

theorem cell23_870070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_870070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870070 prefixEnd_870070 := by exact prefixLift 870070
  have htrace : WordTrace (prefixWord ++ tailWord_870070) baseStart_870070 baseEnd_870070 := by
    simpa [prefixWord, tailWord_870070, baseEnd_870070] using wordTrace_append hprefix tailTrace_870070
  have hstable : (prefixWord ++ tailWord_870070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870070).length < 2 ^ (prefixWord ++ tailWord_870070).sum := by decide
  have hdescent : baseEnd_870070 < baseStart_870070 := by decide
  rcases family_descends (prefixWord ++ tailWord_870070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870136 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_870136 : Nat := 118140960795 + 870136 * 2 ^ 59
def prefixEnd_870136 : Nat := 4983230072969 + 3 ^ 40 * 870136 * 2
def baseEnd_870136 : Nat := 446798002780712822598323

theorem tailTrace_870136 : CollatzResearch.WordTrace tailWord_870136 prefixEnd_870136 446798002780712822598323 := by
  unfold tailWord_870136
  simp only [CollatzResearch.WordTrace]
  refine ⟨15868233587826677121335131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21157644783768902828446841 15868233587826677121335131)
  ·
    refine ⟨23802350381740015682002697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15868233587826677121335131 23802350381740015682002697)
    ·
      refine ⟨17851762786305011761502023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23802350381740015682002697 17851762786305011761502023)
      ·
        refine ⟨26777644179457517642253035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17851762786305011761502023 26777644179457517642253035)
        ·
          refine ⟨40166466269186276463379553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26777644179457517642253035 40166466269186276463379553)
          ·
            refine ⟨30124849701889707347534665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40166466269186276463379553 30124849701889707347534665)
            ·
              refine ⟨22593637276417280510650999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30124849701889707347534665 22593637276417280510650999)
              ·
                refine ⟨33890455914625920765976499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22593637276417280510650999 33890455914625920765976499)
                ·
                  refine ⟨50835683871938881148964749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33890455914625920765976499 50835683871938881148964749)
                  ·
                    refine ⟨19063381451977080430861781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50835683871938881148964749 19063381451977080430861781)
                    ·
                      refine ⟨446798002780712822598323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19063381451977080430861781 446798002780712822598323)
                      ·
                        rfl

theorem cell23_870136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_870136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870136 prefixEnd_870136 := by exact prefixLift 870136
  have htrace : WordTrace (prefixWord ++ tailWord_870136) baseStart_870136 baseEnd_870136 := by
    simpa [prefixWord, tailWord_870136, baseEnd_870136] using wordTrace_append hprefix tailTrace_870136
  have hstable : (prefixWord ++ tailWord_870136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870136).length < 2 ^ (prefixWord ++ tailWord_870136).sum := by decide
  have hdescent : baseEnd_870136 < baseStart_870136 := by decide
  rcases family_descends (prefixWord ++ tailWord_870136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870140 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_870140 : Nat := 118140960795 + 870140 * 2 ^ 59
def prefixEnd_870140 : Nat := 4983230072969 + 3 ^ 40 * 870140 * 2
def baseEnd_870140 : Nat := 446800056703330806948305

theorem tailTrace_870140 : CollatzResearch.WordTrace tailWord_870140 prefixEnd_870140 446800056703330806948305 := by
  unfold tailWord_870140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15868306533819431462907937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21157742045092575283877249 15868306533819431462907937)
  ·
    refine ⟨11901229900364573597180953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15868306533819431462907937 11901229900364573597180953)
    ·
      refine ⟨8925922425273430197885715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11901229900364573597180953 8925922425273430197885715)
      ·
        refine ⟨13388883637910145296828573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8925922425273430197885715 13388883637910145296828573)
        ·
          refine ⟨5020831364216304486310715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13388883637910145296828573 5020831364216304486310715)
          ·
            refine ⟨7531247046324456729466073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020831364216304486310715 7531247046324456729466073)
            ·
              refine ⟨5648435284743342547099555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7531247046324456729466073 5648435284743342547099555)
              ·
                refine ⟨8472652927115013820649333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648435284743342547099555 8472652927115013820649333)
                ·
                  refine ⟨794311211917032545685875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8472652927115013820649333 794311211917032545685875)
                  ·
                    refine ⟨1191466817875548818528813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 794311211917032545685875 1191466817875548818528813)
                    ·
                      refine ⟨446800056703330806948305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1191466817875548818528813 446800056703330806948305)
                      ·
                        rfl

theorem cell23_870140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_870140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870140 prefixEnd_870140 := by exact prefixLift 870140
  have htrace : WordTrace (prefixWord ++ tailWord_870140) baseStart_870140 baseEnd_870140 := by
    simpa [prefixWord, tailWord_870140, baseEnd_870140] using wordTrace_append hprefix tailTrace_870140
  have hstable : (prefixWord ++ tailWord_870140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870140).length < 2 ^ (prefixWord ++ tailWord_870140).sum := by decide
  have hdescent : baseEnd_870140 < baseStart_870140 := by decide
  rcases family_descends (prefixWord ++ tailWord_870140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870167 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 2, 3, 2]
def baseStart_870167 : Nat := 118140960795 + 870167 * 2 ^ 59
def prefixEnd_870167 : Nat := 4983230072969 + 3 ^ 40 * 870167 * 2
def baseEnd_870167 : Nat := 446813920681002201310681

theorem tailTrace_870167 : CollatzResearch.WordTrace tailWord_870167 prefixEnd_870167 446813920681002201310681 := by
  unfold tailWord_870167
  simp only [CollatzResearch.WordTrace]
  refine ⟨31737597838541046537048755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21158398559027364358032503 31737597838541046537048755)
  ·
    refine ⟨47606396757811569805573133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31737597838541046537048755 47606396757811569805573133)
    ·
      refine ⟨17852398784179338677089925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47606396757811569805573133 17852398784179338677089925)
      ·
        refine ⟨3347324772033626001954361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17852398784179338677089925 3347324772033626001954361)
        ·
          refine ⟨2510493579025219501465771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3347324772033626001954361 2510493579025219501465771)
          ·
            refine ⟨3765740368537829252198657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510493579025219501465771 3765740368537829252198657)
            ·
              refine ⟨2824305276403371939148993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765740368537829252198657 2824305276403371939148993)
              ·
                refine ⟨2118228957302528954361745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824305276403371939148993 2118228957302528954361745)
                ·
                  refine ⟨1588671717976896715771309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118228957302528954361745 1588671717976896715771309)
                  ·
                    refine ⟨595751894241336268414241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1588671717976896715771309 595751894241336268414241)
                    ·
                      refine ⟨446813920681002201310681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595751894241336268414241 446813920681002201310681)
                      ·
                        rfl

theorem cell23_870167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_870167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870167 prefixEnd_870167 := by exact prefixLift 870167
  have htrace : WordTrace (prefixWord ++ tailWord_870167) baseStart_870167 baseEnd_870167 := by
    simpa [prefixWord, tailWord_870167, baseEnd_870167] using wordTrace_append hprefix tailTrace_870167
  have hstable : (prefixWord ++ tailWord_870167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870167).length < 2 ^ (prefixWord ++ tailWord_870167).sum := by decide
  have hdescent : baseEnd_870167 < baseStart_870167 := by decide
  rcases family_descends (prefixWord ++ tailWord_870167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870180 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_870180 : Nat := 118140960795 + 870180 * 2 ^ 59
def prefixEnd_870180 : Nat := 4983230072969 + 3 ^ 40 * 870180 * 2
def baseEnd_870180 : Nat := 446820595929510650448121

theorem tailTrace_870180 : CollatzResearch.WordTrace tailWord_870180 prefixEnd_870180 446820595929510650448121 := by
  unfold tailWord_870180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15869035993746974878635997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21158714658329299838181329 15869035993746974878635997)
  ·
    refine ⟨5950888497655115579488499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15869035993746974878635997 5950888497655115579488499)
    ·
      refine ⟨8926332746482673369232749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950888497655115579488499 8926332746482673369232749)
      ·
        refine ⟨3347374779931002513462281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8926332746482673369232749 3347374779931002513462281)
        ·
          refine ⟨2510531084948251885096711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3347374779931002513462281 2510531084948251885096711)
          ·
            refine ⟨3765796627422377827645067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510531084948251885096711 3765796627422377827645067)
            ·
              refine ⟨5648694941133566741467601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765796627422377827645067 5648694941133566741467601)
              ·
                refine ⟨4236521205850175056100701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648694941133566741467601 4236521205850175056100701)
                ·
                  refine ⟨1588695452193815646037763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4236521205850175056100701 1588695452193815646037763)
                  ·
                    refine ⟨2383043178290723469056645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1588695452193815646037763 2383043178290723469056645)
                    ·
                      refine ⟨446820595929510650448121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2383043178290723469056645 446820595929510650448121)
                      ·
                        rfl

theorem cell23_870180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_870180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870180 prefixEnd_870180 := by exact prefixLift 870180
  have htrace : WordTrace (prefixWord ++ tailWord_870180) baseStart_870180 baseEnd_870180 := by
    simpa [prefixWord, tailWord_870180, baseEnd_870180] using wordTrace_append hprefix tailTrace_870180
  have hstable : (prefixWord ++ tailWord_870180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870180).length < 2 ^ (prefixWord ++ tailWord_870180).sum := by decide
  have hdescent : baseEnd_870180 < baseStart_870180 := by decide
  rcases family_descends (prefixWord ++ tailWord_870180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870200 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_870200 : Nat := 118140960795 + 870200 * 2 ^ 59
def prefixEnd_870200 : Nat := 4983230072969 + 3 ^ 40 * 870200 * 2
def baseEnd_870200 : Nat := 446830865542600572198029

theorem tailTrace_870200 : CollatzResearch.WordTrace tailWord_870200 prefixEnd_870200 446830865542600572198029 := by
  unfold tailWord_870200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15869400723710746586500027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21159200964947662115333369 15869400723710746586500027)
  ·
    refine ⟨23804101085566119879750041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15869400723710746586500027 23804101085566119879750041)
    ·
      refine ⟨17853075814174589909812531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23804101085566119879750041 17853075814174589909812531)
      ·
        refine ⟨26779613721261884864718797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17853075814174589909812531 26779613721261884864718797)
        ·
          refine ⟨10042355145473206824269549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26779613721261884864718797 10042355145473206824269549)
          ·
            refine ⟨3765883179552452559101081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10042355145473206824269549 3765883179552452559101081)
            ·
              refine ⟨2824412384664339419325811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765883179552452559101081 2824412384664339419325811)
              ·
                refine ⟨4236618576996509128988717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824412384664339419325811 4236618576996509128988717)
                ·
                  refine ⟨1588731966373690923370769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4236618576996509128988717 1588731966373690923370769)
                  ·
                    refine ⟨1191548974780268192528077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588731966373690923370769 1191548974780268192528077)
                    ·
                      refine ⟨446830865542600572198029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1191548974780268192528077 446830865542600572198029)
                      ·
                        rfl

theorem cell23_870200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_870200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870200 prefixEnd_870200 := by exact prefixLift 870200
  have htrace : WordTrace (prefixWord ++ tailWord_870200) baseStart_870200 baseEnd_870200 := by
    simpa [prefixWord, tailWord_870200, baseEnd_870200] using wordTrace_append hprefix tailTrace_870200
  have hstable : (prefixWord ++ tailWord_870200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870200).length < 2 ^ (prefixWord ++ tailWord_870200).sum := by decide
  have hdescent : baseEnd_870200 < baseStart_870200 := by decide
  rcases family_descends (prefixWord ++ tailWord_870200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870201 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 2, 3, 2]
def baseStart_870201 : Nat := 118140960795 + 870201 * 2 ^ 59
def prefixEnd_870201 : Nat := 4983230072969 + 3 ^ 40 * 870201 * 2
def baseEnd_870201 : Nat := 446831379023255068285525

theorem tailTrace_870201 : CollatzResearch.WordTrace tailWord_870201 prefixEnd_870201 446831379023255068285525 := by
  unfold tailWord_870201
  simp only [CollatzResearch.WordTrace]
  refine ⟨31738837920417870343786457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21159225280278580229190971 31738837920417870343786457)
  ·
    refine ⟨23804128440313402757839843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31738837920417870343786457 23804128440313402757839843)
    ·
      refine ⟨35706192660470104136759765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23804128440313402757839843 35706192660470104136759765)
      ·
        refine ⟨836863890479768065705307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35706192660470104136759765 836863890479768065705307)
        ·
          refine ⟨1255295835719652098557961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836863890479768065705307 1255295835719652098557961)
          ·
            refine ⟨941471876789739073918471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255295835719652098557961 941471876789739073918471)
            ·
              refine ⟨1412207815184608610877707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941471876789739073918471 1412207815184608610877707)
              ·
                refine ⟨2118311722776912916316561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412207815184608610877707 2118311722776912916316561)
                ·
                  refine ⟨1588733792082684687237421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118311722776912916316561 1588733792082684687237421)
                  ·
                    refine ⟨595775172031006757714033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1588733792082684687237421 595775172031006757714033)
                    ·
                      refine ⟨446831379023255068285525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595775172031006757714033 446831379023255068285525)
                      ·
                        rfl

theorem cell23_870201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_870201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870201 prefixEnd_870201 := by exact prefixLift 870201
  have htrace : WordTrace (prefixWord ++ tailWord_870201) baseStart_870201 baseEnd_870201 := by
    simpa [prefixWord, tailWord_870201, baseEnd_870201] using wordTrace_append hprefix tailTrace_870201
  have hstable : (prefixWord ++ tailWord_870201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870201).length < 2 ^ (prefixWord ++ tailWord_870201).sum := by decide
  have hdescent : baseEnd_870201 < baseStart_870201 := by decide
  rcases family_descends (prefixWord ++ tailWord_870201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870244 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_870244 : Nat := 118140960795 + 870244 * 2 ^ 59
def prefixEnd_870244 : Nat := 4983230072969 + 3 ^ 40 * 870244 * 2
def baseEnd_870244 : Nat := 446853458691398400047827

theorem tailTrace_870244 : CollatzResearch.WordTrace tailWord_870244 prefixEnd_870244 446853458691398400047827 := by
  unfold tailWord_870244
  simp only [CollatzResearch.WordTrace]
  refine ⟨15870203129631044343800893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21160270839508059125067857 15870203129631044343800893)
  ·
    refine ⟨5951326173611641628925335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15870203129631044343800893 5951326173611641628925335)
    ·
      refine ⟨8926989260417462443388003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5951326173611641628925335 8926989260417462443388003)
      ·
        refine ⟨13390483890626193665082005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8926989260417462443388003 13390483890626193665082005)
        ·
          refine ⟨627678932373102828050719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13390483890626193665082005 627678932373102828050719)
          ·
            refine ⟨941518398559654242076079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627678932373102828050719 941518398559654242076079)
            ·
              refine ⟨1412277597839481363114119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941518398559654242076079 1412277597839481363114119)
              ·
                refine ⟨2118416396759222044671179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412277597839481363114119 2118416396759222044671179)
                ·
                  refine ⟨3177624595138833067006769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118416396759222044671179 3177624595138833067006769)
                  ·
                    refine ⟨2383218446354124800255077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177624595138833067006769 2383218446354124800255077)
                    ·
                      refine ⟨446853458691398400047827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2383218446354124800255077 446853458691398400047827)
                      ·
                        rfl

theorem cell23_870244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_870244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870244 prefixEnd_870244 := by exact prefixLift 870244
  have htrace : WordTrace (prefixWord ++ tailWord_870244) baseStart_870244 baseEnd_870244 := by
    simpa [prefixWord, tailWord_870244, baseEnd_870244] using wordTrace_append hprefix tailTrace_870244
  have hstable : (prefixWord ++ tailWord_870244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870244).length < 2 ^ (prefixWord ++ tailWord_870244).sum := by decide
  have hdescent : baseEnd_870244 < baseStart_870244 := by decide
  rcases family_descends (prefixWord ++ tailWord_870244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870344 : List Nat := [2, 1, 3, 1, 4, 1, 4, 2, 5]
def baseStart_870344 : Nat := 118140960795 + 870344 * 2 ^ 59
def prefixEnd_870344 : Nat := 4983230072969 + 3 ^ 40 * 870344 * 2
def baseEnd_870344 : Nat := 49656089639649778755263

theorem tailTrace_870344 : CollatzResearch.WordTrace tailWord_870344 prefixEnd_870344 49656089639649778755263 := by
  unfold tailWord_870344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872026779449902883121043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21162702372599870510828057 15872026779449902883121043)
  ·
    refine ⟨23808040169174854324681565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15872026779449902883121043 23808040169174854324681565)
    ·
      refine ⟨8928015063440570371755587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23808040169174854324681565 8928015063440570371755587)
      ·
        refine ⟨13392022595160855557633381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928015063440570371755587 13392022595160855557633381)
        ·
          refine ⟨2511004236592660417056259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13392022595160855557633381 2511004236592660417056259)
          ·
            refine ⟨3766506354888990625584389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511004236592660417056259 3766506354888990625584389)
            ·
              refine ⟨706219941541685742297073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3766506354888990625584389 706219941541685742297073)
              ·
                refine ⟨529664956156264306722805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706219941541685742297073 529664956156264306722805)
                ·
                  refine ⟨49656089639649778755263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 529664956156264306722805 49656089639649778755263)
                  ·
                    rfl

theorem cell23_870344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 5].length) (baseStart_870344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870344 prefixEnd_870344 := by exact prefixLift 870344
  have htrace : WordTrace (prefixWord ++ tailWord_870344) baseStart_870344 baseEnd_870344 := by
    simpa [prefixWord, tailWord_870344, baseEnd_870344] using wordTrace_append hprefix tailTrace_870344
  have hstable : (prefixWord ++ tailWord_870344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870344).length < 2 ^ (prefixWord ++ tailWord_870344).sum := by decide
  have hdescent : baseEnd_870344 < baseStart_870344 := by decide
  rcases family_descends (prefixWord ++ tailWord_870344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870350 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_870350 : Nat := 118140960795 + 870350 * 2 ^ 59
def prefixEnd_870350 : Nat := 4983230072969 + 3 ^ 40 * 870350 * 2
def baseEnd_870350 : Nat := 446907887640774985322339

theorem tailTrace_870350 : CollatzResearch.WordTrace tailWord_870350 prefixEnd_870350 446907887640774985322339 := by
  unfold tailWord_870350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968034049609758598870063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21162848264585379193973669 3968034049609758598870063)
  ·
    refine ⟨5952051074414637898305095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3968034049609758598870063 5952051074414637898305095)
    ·
      refine ⟨8928076611621956847457643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952051074414637898305095 8928076611621956847457643)
      ·
        refine ⟨13392114917432935271186465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928076611621956847457643 13392114917432935271186465)
        ·
          refine ⟨10044086188074701453389849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13392114917432935271186465 10044086188074701453389849)
          ·
            refine ⟨7533064641056026090042387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10044086188074701453389849 7533064641056026090042387)
            ·
              refine ⟨11299596961584039135063581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533064641056026090042387 11299596961584039135063581)
              ·
                refine ⟨4237348860594014675648843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11299596961584039135063581 4237348860594014675648843)
                ·
                  refine ⟨6356023290891022013473265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237348860594014675648843 6356023290891022013473265)
                  ·
                    refine ⟨4767017468168266510104949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6356023290891022013473265 4767017468168266510104949)
                    ·
                      refine ⟨446907887640774985322339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4767017468168266510104949 446907887640774985322339)
                      ·
                        rfl

theorem cell23_870350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_870350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870350 prefixEnd_870350 := by exact prefixLift 870350
  have htrace : WordTrace (prefixWord ++ tailWord_870350) baseStart_870350 baseEnd_870350 := by
    simpa [prefixWord, tailWord_870350, baseEnd_870350] using wordTrace_append hprefix tailTrace_870350
  have hstable : (prefixWord ++ tailWord_870350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870350).length < 2 ^ (prefixWord ++ tailWord_870350).sum := by decide
  have hdescent : baseEnd_870350 < baseStart_870350 := by decide
  rcases family_descends (prefixWord ++ tailWord_870350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870354 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_870354 : Nat := 118140960795 + 870354 * 2 ^ 59
def prefixEnd_870354 : Nat := 4983230072969 + 3 ^ 40 * 870354 * 2
def baseEnd_870354 : Nat := 446909941563392969672321

theorem tailTrace_870354 : CollatzResearch.WordTrace tailWord_870354 prefixEnd_870354 446909941563392969672321 := by
  unfold tailWord_870354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7936104572215894368526529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21162945525909051649404077 7936104572215894368526529)
  ·
    refine ⟨5952078429161920776394897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7936104572215894368526529 5952078429161920776394897)
    ·
      refine ⟨4464058821871440582296173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5952078429161920776394897 4464058821871440582296173)
      ·
        refine ⟨1674022058201790218361065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4464058821871440582296173 1674022058201790218361065)
        ·
          refine ⟨1255516543651342663770799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674022058201790218361065 1255516543651342663770799)
          ·
            refine ⟨1883274815477013995656199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255516543651342663770799 1883274815477013995656199)
            ·
              refine ⟨2824912223215520993484299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883274815477013995656199 2824912223215520993484299)
              ·
                refine ⟨4237368334823281490226449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824912223215520993484299 4237368334823281490226449)
                ·
                  refine ⟨3178026251117461117669837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4237368334823281490226449 3178026251117461117669837)
                  ·
                    refine ⟨1191759844169047919126189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3178026251117461117669837 1191759844169047919126189)
                    ·
                      refine ⟨446909941563392969672321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1191759844169047919126189 446909941563392969672321)
                      ·
                        rfl

theorem cell23_870354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_870354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870354 prefixEnd_870354 := by exact prefixLift 870354
  have htrace : WordTrace (prefixWord ++ tailWord_870354) baseStart_870354 baseEnd_870354 := by
    simpa [prefixWord, tailWord_870354, baseEnd_870354] using wordTrace_append hprefix tailTrace_870354
  have hstable : (prefixWord ++ tailWord_870354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870354).length < 2 ^ (prefixWord ++ tailWord_870354).sum := by decide
  have hdescent : baseEnd_870354 < baseStart_870354 := by decide
  rcases family_descends (prefixWord ++ tailWord_870354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870360 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_870360 : Nat := 118140960795 + 870360 * 2 ^ 59
def prefixEnd_870360 : Nat := 4983230072969 + 3 ^ 40 * 870360 * 2
def baseEnd_870360 : Nat := 446913022447319946197293

theorem tailTrace_870360 : CollatzResearch.WordTrace tailWord_870360 prefixEnd_870360 446913022447319946197293 := by
  unfold tailWord_870360
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872318563420920249412267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21163091417894560332549689 15872318563420920249412267)
  ·
    refine ⟨23808477845131380374118401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15872318563420920249412267 23808477845131380374118401)
    ·
      refine ⟨17856358383848535280588801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23808477845131380374118401 17856358383848535280588801)
      ·
        refine ⟨13392268787886401460441601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17856358383848535280588801 13392268787886401460441601)
        ·
          refine ⟨10044201590914801095331201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13392268787886401460441601 10044201590914801095331201)
          ·
            refine ⟨7533151193186100821498401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10044201590914801095331201 7533151193186100821498401)
            ·
              refine ⟨5649863394889575616123801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7533151193186100821498401 5649863394889575616123801)
              ·
                refine ⟨4237397546167181712092851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649863394889575616123801 4237397546167181712092851)
                ·
                  refine ⟨6356096319250772568139277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237397546167181712092851 6356096319250772568139277)
                  ·
                    refine ⟨2383536119719039713052229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6356096319250772568139277 2383536119719039713052229)
                    ·
                      refine ⟨446913022447319946197293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2383536119719039713052229 446913022447319946197293)
                      ·
                        rfl

theorem cell23_870360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_870360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870360 prefixEnd_870360 := by exact prefixLift 870360
  have htrace : WordTrace (prefixWord ++ tailWord_870360) baseStart_870360 baseEnd_870360 := by
    simpa [prefixWord, tailWord_870360, baseEnd_870360] using wordTrace_append hprefix tailTrace_870360
  have hstable : (prefixWord ++ tailWord_870360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870360).length < 2 ^ (prefixWord ++ tailWord_870360).sum := by decide
  have hdescent : baseEnd_870360 < baseStart_870360 := by decide
  rcases family_descends (prefixWord ++ tailWord_870360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870397 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_870397 : Nat := 118140960795 + 870397 * 2 ^ 59
def prefixEnd_870397 : Nat := 4983230072969 + 3 ^ 40 * 870397 * 2
def baseEnd_870397 : Nat := 446932021231536301434623

theorem tailTrace_870397 : CollatzResearch.WordTrace tailWord_870397 prefixEnd_870397 446932021231536301434623 := by
  unfold tailWord_870397
  simp only [CollatzResearch.WordTrace]
  refine ⟨31745986627707795817921445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21163991085138530545280963 31745986627707795817921445)
  ·
    refine ⟨5952372492695211715860271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31745986627707795817921445 5952372492695211715860271)
    ·
      refine ⟨8928558739042817573790407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952372492695211715860271 8928558739042817573790407)
      ·
        refine ⟨13392838108564226360685611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928558739042817573790407 13392838108564226360685611)
        ·
          refine ⟨20089257162846339541028417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13392838108564226360685611 20089257162846339541028417)
          ·
            refine ⟨15066942872134754655771313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20089257162846339541028417 15066942872134754655771313)
            ·
              refine ⟨11300207154101065991828485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15066942872134754655771313 11300207154101065991828485)
              ·
                refine ⟨2118788841393949873467841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11300207154101065991828485 2118788841393949873467841)
                ·
                  refine ⟨1589091631045462405100881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118788841393949873467841 1589091631045462405100881)
                  ·
                    refine ⟨1191818723284096803825661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1589091631045462405100881 1191818723284096803825661)
                    ·
                      refine ⟨446932021231536301434623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1191818723284096803825661 446932021231536301434623)
                      ·
                        rfl

theorem cell23_870397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_870397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870397 prefixEnd_870397 := by exact prefixLift 870397
  have htrace : WordTrace (prefixWord ++ tailWord_870397) baseStart_870397 baseEnd_870397 := by
    simpa [prefixWord, tailWord_870397, baseEnd_870397] using wordTrace_append hprefix tailTrace_870397
  have hstable : (prefixWord ++ tailWord_870397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870397).length < 2 ^ (prefixWord ++ tailWord_870397).sum := by decide
  have hdescent : baseEnd_870397 < baseStart_870397 := by decide
  rcases family_descends (prefixWord ++ tailWord_870397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870400 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 6]
def baseStart_870400 : Nat := 118140960795 + 870400 * 2 ^ 59
def prefixEnd_870400 : Nat := 4983230072969 + 3 ^ 40 * 870400 * 2
def baseEnd_870400 : Nat := 49659284630388865521901

theorem tailTrace_870400 : CollatzResearch.WordTrace tailWord_870400 prefixEnd_870400 49659284630388865521901 := by
  unfold tailWord_870400
  simp only [CollatzResearch.WordTrace]
  refine ⟨15873048023348463665140327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21164064031131284886853769 15873048023348463665140327)
  ·
    refine ⟨23809572035022695497710491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15873048023348463665140327 23809572035022695497710491)
    ·
      refine ⟨35714358052534043246565737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23809572035022695497710491 35714358052534043246565737)
      ·
        refine ⟨26785768539400532434924303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35714358052534043246565737 26785768539400532434924303)
        ·
          refine ⟨40178652809100798652386455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26785768539400532434924303 40178652809100798652386455)
          ·
            refine ⟨60267979213651197978579683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40178652809100798652386455 60267979213651197978579683)
            ·
              refine ⟨90401968820476796967869525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60267979213651197978579683 90401968820476796967869525)
              ·
                refine ⟨1059398072114962464467221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 90401968820476796967869525 1059398072114962464467221)
                ·
                  refine ⟨49659284630388865521901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1059398072114962464467221 49659284630388865521901)
                  ·
                    rfl

theorem cell23_870400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 6].length) (baseStart_870400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870400 prefixEnd_870400 := by exact prefixLift 870400
  have htrace : WordTrace (prefixWord ++ tailWord_870400) baseStart_870400 baseEnd_870400 := by
    simpa [prefixWord, tailWord_870400, baseEnd_870400] using wordTrace_append hprefix tailTrace_870400
  have hstable : (prefixWord ++ tailWord_870400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870400).length < 2 ^ (prefixWord ++ tailWord_870400).sum := by decide
  have hdescent : baseEnd_870400 < baseStart_870400 := by decide
  rcases family_descends (prefixWord ++ tailWord_870400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870427 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 3]
def baseStart_870427 : Nat := 118140960795 + 870427 * 2 ^ 59
def prefixEnd_870427 : Nat := 4983230072969 + 3 ^ 40 * 870427 * 2
def baseEnd_870427 : Nat := 446947425651171184059485

theorem tailTrace_870427 : CollatzResearch.WordTrace tailWord_870427 prefixEnd_870427 446947425651171184059485 := by
  unfold tailWord_870427
  simp only [CollatzResearch.WordTrace]
  refine ⟨31747080817599110941513535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21164720545066073961009023 31747080817599110941513535)
  ·
    refine ⟨47620621226398666412270303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31747080817599110941513535 47620621226398666412270303)
    ·
      refine ⟨71430931839597999618405455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47620621226398666412270303 71430931839597999618405455)
      ·
        refine ⟨107146397759396999427608183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71430931839597999618405455 107146397759396999427608183)
        ·
          refine ⟨160719596639095499141412275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107146397759396999427608183 160719596639095499141412275)
          ·
            refine ⟨241079394958643248712118413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160719596639095499141412275 241079394958643248712118413)
            ·
              refine ⟨90404773109491218267044405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241079394958643248712118413 90404773109491218267044405)
              ·
                refine ⟨8475447479014801712535413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90404773109491218267044405 8475447479014801712535413)
                ·
                  refine ⟨794573201157637660550195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8475447479014801712535413 794573201157637660550195)
                  ·
                    refine ⟨1191859801736456490825293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 794573201157637660550195 1191859801736456490825293)
                    ·
                      refine ⟨446947425651171184059485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1191859801736456490825293 446947425651171184059485)
                      ·
                        rfl

theorem cell23_870427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 3].length) (baseStart_870427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870427 prefixEnd_870427 := by exact prefixLift 870427
  have htrace : WordTrace (prefixWord ++ tailWord_870427) baseStart_870427 baseEnd_870427 := by
    simpa [prefixWord, tailWord_870427, baseEnd_870427] using wordTrace_append hprefix tailTrace_870427
  have hstable : (prefixWord ++ tailWord_870427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870427).length < 2 ^ (prefixWord ++ tailWord_870427).sum := by decide
  have hdescent : baseEnd_870427 < baseStart_870427 := by decide
  rcases family_descends (prefixWord ++ tailWord_870427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870467 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 2, 6, 2]
def baseStart_870467 : Nat := 118140960795 + 870467 * 2 ^ 59
def prefixEnd_870467 : Nat := 4983230072969 + 3 ^ 40 * 870467 * 2
def baseEnd_870467 : Nat := 446967964877351027559301

theorem tailTrace_870467 : CollatzResearch.WordTrace tailWord_870467 prefixEnd_870467 446967964877351027559301 := by
  unfold tailWord_870467
  simp only [CollatzResearch.WordTrace]
  refine ⟨31748539737454197772969655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21165693158302798515313103 31748539737454197772969655)
  ·
    refine ⟨47622809606181296659454483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31748539737454197772969655 47622809606181296659454483)
    ·
      refine ⟨71434214409271944989181725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47622809606181296659454483 71434214409271944989181725)
      ·
        refine ⟨26787830403476979370943147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71434214409271944989181725 26787830403476979370943147)
        ·
          refine ⟨40181745605215469056414721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26787830403476979370943147 40181745605215469056414721)
          ·
            refine ⟨30136309203911601792311041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40181745605215469056414721 30136309203911601792311041)
            ·
              refine ⟨22602231902933701344233281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30136309203911601792311041 22602231902933701344233281)
              ·
                refine ⟨16951673927200276008174961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22602231902933701344233281 16951673927200276008174961)
                ·
                  refine ⟨12713755445400207006131221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16951673927200276008174961 12713755445400207006131221)
                  ·
                    refine ⟨595957286503134703412401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12713755445400207006131221 595957286503134703412401)
                    ·
                      refine ⟨446967964877351027559301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595957286503134703412401 446967964877351027559301)
                      ·
                        rfl

theorem cell23_870467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_870467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870467 prefixEnd_870467 := by exact prefixLift 870467
  have htrace : WordTrace (prefixWord ++ tailWord_870467) baseStart_870467 baseEnd_870467 := by
    simpa [prefixWord, tailWord_870467, baseEnd_870467] using wordTrace_append hprefix tailTrace_870467
  have hstable : (prefixWord ++ tailWord_870467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870467).length < 2 ^ (prefixWord ++ tailWord_870467).sum := by decide
  have hdescent : baseEnd_870467 < baseStart_870467 := by decide
  rcases family_descends (prefixWord ++ tailWord_870467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870490 : List Nat := [3, 1, 1, 2, 1, 1, 3, 11]
def baseStart_870490 : Nat := 118140960795 + 870490 * 2 ^ 59
def prefixEnd_870490 : Nat := 4983230072969 + 3 ^ 40 * 870490 * 2
def baseEnd_870490 : Nat := 16554806478977942132285

theorem tailTrace_870490 : CollatzResearch.WordTrace tailWord_870490 prefixEnd_870490 16554806478977942132285 := by
  unfold tailWord_870490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937344654092718175264231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21166252410913915134037949 7937344654092718175264231)
  ·
    refine ⟨11906016981139077262896347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7937344654092718175264231 11906016981139077262896347)
    ·
      refine ⟨17859025471708615894344521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11906016981139077262896347 17859025471708615894344521)
      ·
        refine ⟨13394269103781461920758391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17859025471708615894344521 13394269103781461920758391)
        ·
          refine ⟨20091403655672192881137587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394269103781461920758391 20091403655672192881137587)
          ·
            refine ⟨30137105483508289321706381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20091403655672192881137587 30137105483508289321706381)
            ·
              refine ⟨11301414556315608495639893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30137105483508289321706381 11301414556315608495639893)
              ·
                refine ⟨16554806478977942132285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 11301414556315608495639893 16554806478977942132285)
                ·
                  rfl

theorem cell23_870490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_870490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870490 prefixEnd_870490 := by exact prefixLift 870490
  have htrace : WordTrace (prefixWord ++ tailWord_870490) baseStart_870490 baseEnd_870490 := by
    simpa [prefixWord, tailWord_870490, baseEnd_870490] using wordTrace_append hprefix tailTrace_870490
  have hstable : (prefixWord ++ tailWord_870490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870490).length < 2 ^ (prefixWord ++ tailWord_870490).sum := by decide
  have hdescent : baseEnd_870490 < baseStart_870490 := by decide
  rcases family_descends (prefixWord ++ tailWord_870490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870498 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_870498 : Nat := 118140960795 + 870498 * 2 ^ 59
def prefixEnd_870498 : Nat := 4983230072969 + 3 ^ 40 * 870498 * 2
def baseEnd_870498 : Nat := 148994627592546802090553

theorem tailTrace_870498 : CollatzResearch.WordTrace tailWord_870498 prefixEnd_870498 148994627592546802090553 := by
  unfold tailWord_870498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937417600085472516837037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21166446933561260044898765 7937417600085472516837037)
  ·
    refine ⟨2976531600032052193813889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7937417600085472516837037 2976531600032052193813889)
    ·
      refine ⟨2232398700024039145360417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2976531600032052193813889 2232398700024039145360417)
      ·
        refine ⟨1674299025018029359020313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2232398700024039145360417 1674299025018029359020313)
        ·
          refine ⟨1255724268763522019265235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674299025018029359020313 1255724268763522019265235)
          ·
            refine ⟨1883586403145283028897853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255724268763522019265235 1883586403145283028897853)
            ·
              refine ⟨706344901179481135836695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1883586403145283028897853 706344901179481135836695)
              ·
                refine ⟨1059517351769221703755043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706344901179481135836695 1059517351769221703755043)
                ·
                  refine ⟨1589276027653832555632565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059517351769221703755043 1589276027653832555632565)
                  ·
                    refine ⟨148994627592546802090553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1589276027653832555632565 148994627592546802090553)
                    ·
                      rfl

theorem cell23_870498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_870498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870498 prefixEnd_870498 := by exact prefixLift 870498
  have htrace : WordTrace (prefixWord ++ tailWord_870498) baseStart_870498 baseEnd_870498 := by
    simpa [prefixWord, tailWord_870498, baseEnd_870498] using wordTrace_append hprefix tailTrace_870498
  have hstable : (prefixWord ++ tailWord_870498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870498).length < 2 ^ (prefixWord ++ tailWord_870498).sum := by decide
  have hdescent : baseEnd_870498 < baseStart_870498 := by decide
  rcases family_descends (prefixWord ++ tailWord_870498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870501 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 1, 1, 4]
def baseStart_870501 : Nat := 118140960795 + 870501 * 2 ^ 59
def prefixEnd_870501 : Nat := 4983230072969 + 3 ^ 40 * 870501 * 2
def baseEnd_870501 : Nat := 446985423219603894534145

theorem tailTrace_870501 : CollatzResearch.WordTrace tailWord_870501 prefixEnd_870501 446985423219603894534145 := by
  unfold tailWord_870501
  simp only [CollatzResearch.WordTrace]
  refine ⟨31749779819331021579707357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21166519879554014386471571 31749779819331021579707357)
  ·
    refine ⟨11906167432249133092390259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31749779819331021579707357 11906167432249133092390259)
    ·
      refine ⟨17859251148373699638585389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11906167432249133092390259 17859251148373699638585389)
      ·
        refine ⟨6697219180640137364469521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17859251148373699638585389 6697219180640137364469521)
        ·
          refine ⟨5022914385480103023352141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6697219180640137364469521 5022914385480103023352141)
          ·
            refine ⟨1883592894555038633757053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5022914385480103023352141 1883592894555038633757053)
            ·
              refine ⟨706347335458139487658895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1883592894555038633757053 706347335458139487658895)
              ·
                refine ⟨1059521003187209231488343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706347335458139487658895 1059521003187209231488343)
                ·
                  refine ⟨1589281504780813847232515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059521003187209231488343 1589281504780813847232515)
                  ·
                    refine ⟨2383922257171220770848773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1589281504780813847232515 2383922257171220770848773)
                    ·
                      refine ⟨446985423219603894534145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2383922257171220770848773 446985423219603894534145)
                      ·
                        rfl

theorem cell23_870501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_870501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870501 prefixEnd_870501 := by exact prefixLift 870501
  have htrace : WordTrace (prefixWord ++ tailWord_870501) baseStart_870501 baseEnd_870501 := by
    simpa [prefixWord, tailWord_870501, baseEnd_870501] using wordTrace_append hprefix tailTrace_870501
  have hstable : (prefixWord ++ tailWord_870501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870501).length < 2 ^ (prefixWord ++ tailWord_870501).sum := by decide
  have hdescent : baseEnd_870501 < baseStart_870501 := by decide
  rcases family_descends (prefixWord ++ tailWord_870501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870544 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 3, 3, 2]
def baseStart_870544 : Nat := 118140960795 + 870544 * 2 ^ 59
def prefixEnd_870544 : Nat := 4983230072969 + 3 ^ 40 * 870544 * 2
def baseEnd_870544 : Nat := 447007502887747226296447

theorem tailTrace_870544 : CollatzResearch.WordTrace tailWord_870544 prefixEnd_870544 447007502887747226296447 := by
  unfold tailWord_870544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15875674079087619961761343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21167565438783493282348457 15875674079087619961761343)
  ·
    refine ⟨23813511118631429942642015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15875674079087619961761343 23813511118631429942642015)
    ·
      refine ⟨35720266677947144913963023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23813511118631429942642015 35720266677947144913963023)
      ·
        refine ⟨53580400016920717370944535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35720266677947144913963023 53580400016920717370944535)
        ·
          refine ⟨80370600025381076056416803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53580400016920717370944535 80370600025381076056416803)
          ·
            refine ⟨120555900038071614084625205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80370600025381076056416803 120555900038071614084625205)
            ·
              refine ⟨11302115628569213820433613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120555900038071614084625205 11302115628569213820433613)
              ·
                refine ⟨4238293360713455182662605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11302115628569213820433613 4238293360713455182662605)
                ·
                  refine ⟨1589360010267545693498477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4238293360713455182662605 1589360010267545693498477)
                  ·
                    refine ⟨596010003850329635061929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589360010267545693498477 596010003850329635061929)
                    ·
                      refine ⟨447007502887747226296447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 596010003850329635061929 447007502887747226296447)
                      ·
                        rfl

theorem cell23_870544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 3, 2].length) (baseStart_870544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870544 prefixEnd_870544 := by exact prefixLift 870544
  have htrace : WordTrace (prefixWord ++ tailWord_870544) baseStart_870544 baseEnd_870544 := by
    simpa [prefixWord, tailWord_870544, baseEnd_870544] using wordTrace_append hprefix tailTrace_870544
  have hstable : (prefixWord ++ tailWord_870544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870544).length < 2 ^ (prefixWord ++ tailWord_870544).sum := by decide
  have hdescent : baseEnd_870544 < baseStart_870544 := by decide
  rcases family_descends (prefixWord ++ tailWord_870544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870587 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4]
def baseStart_870587 : Nat := 118140960795 + 870587 * 2 ^ 59
def prefixEnd_870587 : Nat := 4983230072969 + 3 ^ 40 * 870587 * 2
def baseEnd_870587 : Nat := 447029582555890558058749

theorem tailTrace_870587 : CollatzResearch.WordTrace tailWord_870587 prefixEnd_870587 447029582555890558058749 := by
  unfold tailWord_870587
  simp only [CollatzResearch.WordTrace]
  refine ⟨31752916497019458267338015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21168610998012972178225343 31752916497019458267338015)
  ·
    refine ⟨47629374745529187401007023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31752916497019458267338015 47629374745529187401007023)
    ·
      refine ⟨71444062118293781101510535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47629374745529187401007023 71444062118293781101510535)
      ·
        refine ⟨107166093177440671652265803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71444062118293781101510535 107166093177440671652265803)
        ·
          refine ⟨160749139766161007478398705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107166093177440671652265803 160749139766161007478398705)
          ·
            refine ⟨120561854824620755608799029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160749139766161007478398705 120561854824620755608799029)
            ·
              refine ⟨11302673889808195838324909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120561854824620755608799029 11302673889808195838324909)
              ·
                refine ⟨4238502708678073439371841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11302673889808195838324909 4238502708678073439371841)
                ·
                  refine ⟨3178877031508555079528881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4238502708678073439371841 3178877031508555079528881)
                  ·
                    refine ⟨2384157773631416309646661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3178877031508555079528881 2384157773631416309646661)
                    ·
                      refine ⟨447029582555890558058749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2384157773631416309646661 447029582555890558058749)
                      ·
                        rfl

theorem cell23_870587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_870587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870587 prefixEnd_870587 := by exact prefixLift 870587
  have htrace : WordTrace (prefixWord ++ tailWord_870587) baseStart_870587 baseEnd_870587 := by
    simpa [prefixWord, tailWord_870587, baseEnd_870587] using wordTrace_append hprefix tailTrace_870587
  have hstable : (prefixWord ++ tailWord_870587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870587).length < 2 ^ (prefixWord ++ tailWord_870587).sum := by decide
  have hdescent : baseEnd_870587 < baseStart_870587 := by decide
  rcases family_descends (prefixWord ++ tailWord_870587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870597 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 7]
def baseStart_870597 : Nat := 118140960795 + 870597 * 2 ^ 59
def prefixEnd_870597 : Nat := 4983230072969 + 3 ^ 40 * 870597 * 2
def baseEnd_870597 : Nat := 49670524151381724325967

theorem tailTrace_870597 : CollatzResearch.WordTrace tailWord_870597 prefixEnd_870597 49670524151381724325967 := by
  unfold tailWord_870597
  simp only [CollatzResearch.WordTrace]
  refine ⟨31753281226983229975202045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21168854151322153316801363 31753281226983229975202045)
  ·
    refine ⟨11907480460118711240700767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31753281226983229975202045 11907480460118711240700767)
    ·
      refine ⟨17861220690178066861051151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11907480460118711240700767 17861220690178066861051151)
      ·
        refine ⟨26791831035267100291576727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17861220690178066861051151 26791831035267100291576727)
        ·
          refine ⟨40187746552900650437365091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26791831035267100291576727 40187746552900650437365091)
          ·
            refine ⟨60281619829350975656047637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40187746552900650437365091 60281619829350975656047637)
            ·
              refine ⟨2825700929500826983877233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60281619829350975656047637 2825700929500826983877233)
              ·
                refine ⟨2119275697125620237907925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825700929500826983877233 2119275697125620237907925)
                ·
                  refine ⟨49670524151381724325967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2119275697125620237907925 49670524151381724325967)
                  ·
                    rfl

theorem cell23_870597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_870597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870597 prefixEnd_870597 := by exact prefixLift 870597
  have htrace : WordTrace (prefixWord ++ tailWord_870597) baseStart_870597 baseEnd_870597 := by
    simpa [prefixWord, tailWord_870597, baseEnd_870597] using wordTrace_append hprefix tailTrace_870597
  have hstable : (prefixWord ++ tailWord_870597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870597).length < 2 ^ (prefixWord ++ tailWord_870597).sum := by decide
  have hdescent : baseEnd_870597 < baseStart_870597 := by decide
  rcases family_descends (prefixWord ++ tailWord_870597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870631 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 7]
def baseStart_870631 : Nat := 118140960795 + 870631 * 2 ^ 59
def prefixEnd_870631 : Nat := 4983230072969 + 3 ^ 40 * 870631 * 2
def baseEnd_870631 : Nat := 49672463967187598434283

theorem tailTrace_870631 : CollatzResearch.WordTrace tailWord_870631 prefixEnd_870631 49672463967187598434283 := by
  unfold tailWord_870631
  simp only [CollatzResearch.WordTrace]
  refine ⟨31754521308860053781939747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21169680872573369187959831 31754521308860053781939747)
  ·
    refine ⟨47631781963290080672909621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31754521308860053781939747 47631781963290080672909621)
    ·
      refine ⟨4465479559058445063085277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47631781963290080672909621 4465479559058445063085277)
      ·
        refine ⟨1674554834646916898656979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4465479559058445063085277 1674554834646916898656979)
        ·
          refine ⟨2511832251970375347985469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674554834646916898656979 2511832251970375347985469)
          ·
            refine ⟨941937094488890755494551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2511832251970375347985469 941937094488890755494551)
            ·
              refine ⟨1412905641733336133241827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941937094488890755494551 1412905641733336133241827)
              ·
                refine ⟨2119358462600004199862741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412905641733336133241827 2119358462600004199862741)
                ·
                  refine ⟨49672463967187598434283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2119358462600004199862741 49672463967187598434283)
                  ·
                    rfl

theorem cell23_870631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 7].length) (baseStart_870631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870631 prefixEnd_870631 := by exact prefixLift 870631
  have htrace : WordTrace (prefixWord ++ tailWord_870631) baseStart_870631 baseEnd_870631 := by
    simpa [prefixWord, tailWord_870631, baseEnd_870631] using wordTrace_append hprefix tailTrace_870631
  have hstable : (prefixWord ++ tailWord_870631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870631).length < 2 ^ (prefixWord ++ tailWord_870631).sum := by decide
  have hdescent : baseEnd_870631 < baseStart_870631 := by decide
  rcases family_descends (prefixWord ++ tailWord_870631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870642 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_870642 : Nat := 118140960795 + 870642 * 2 ^ 59
def prefixEnd_870642 : Nat := 4983230072969 + 3 ^ 40 * 870642 * 2
def baseEnd_870642 : Nat := 447057823991887842870997

theorem tailTrace_870642 : CollatzResearch.WordTrace tailWord_870642 prefixEnd_870642 447057823991887842870997 := by
  unfold tailWord_870642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938730627955050665147545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21169948341213468440393453 7938730627955050665147545)
  ·
    refine ⟨5954047970966287998860659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7938730627955050665147545 5954047970966287998860659)
    ·
      refine ⟨8931071956449431998290989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5954047970966287998860659 8931071956449431998290989)
      ·
        refine ⟨3349151983668536999359121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8931071956449431998290989 3349151983668536999359121)
        ·
          refine ⟨2511863987751402749519341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3349151983668536999359121 2511863987751402749519341)
          ·
            refine ⟨941948995406776031069753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2511863987751402749519341 941948995406776031069753)
            ·
              refine ⟨706461746555082023302315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941948995406776031069753 706461746555082023302315)
              ·
                refine ⟨1059692619832623034953473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706461746555082023302315 1059692619832623034953473)
                ·
                  refine ⟨794769464874467276215105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059692619832623034953473 794769464874467276215105)
                  ·
                    refine ⟨596077098655850457161329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 794769464874467276215105 596077098655850457161329)
                    ·
                      refine ⟨447057823991887842870997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 596077098655850457161329 447057823991887842870997)
                      ·
                        rfl

theorem cell23_870642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_870642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870642 prefixEnd_870642 := by exact prefixLift 870642
  have htrace : WordTrace (prefixWord ++ tailWord_870642) baseStart_870642 baseEnd_870642 := by
    simpa [prefixWord, tailWord_870642, baseEnd_870642] using wordTrace_append hprefix tailTrace_870642
  have hstable : (prefixWord ++ tailWord_870642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870642).length < 2 ^ (prefixWord ++ tailWord_870642).sum := by decide
  have hdescent : baseEnd_870642 < baseStart_870642 := by decide
  rcases family_descends (prefixWord ++ tailWord_870642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870654 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_870654 : Nat := 118140960795 + 870654 * 2 ^ 59
def prefixEnd_870654 : Nat := 4983230072969 + 3 ^ 40 * 870654 * 2
def baseEnd_870654 : Nat := 447063985759741795920941

theorem tailTrace_870654 : CollatzResearch.WordTrace tailWord_870654 prefixEnd_870654 447063985759741795920941 := by
  unfold tailWord_870654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969420023472091088753377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21170240125184485806684677 3969420023472091088753377)
  ·
    refine ⟨2977065017604068316565033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3969420023472091088753377 2977065017604068316565033)
    ·
      refine ⟨2232798763203051237423775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2977065017604068316565033 2232798763203051237423775)
      ·
        refine ⟨3349198144804576856135663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232798763203051237423775 3349198144804576856135663)
        ·
          refine ⟨5023797217206865284203495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349198144804576856135663 5023797217206865284203495)
          ·
            refine ⟨7535695825810297926305243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5023797217206865284203495 7535695825810297926305243)
            ·
              refine ⟨11303543738715446889457865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535695825810297926305243 11303543738715446889457865)
              ·
                refine ⟨8477657804036585167093399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11303543738715446889457865 8477657804036585167093399)
                ·
                  refine ⟨12716486706054877750640099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8477657804036585167093399 12716486706054877750640099)
                  ·
                    refine ⟨19074730059082316625960149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12716486706054877750640099 19074730059082316625960149)
                    ·
                      refine ⟨447063985759741795920941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19074730059082316625960149 447063985759741795920941)
                      ·
                        rfl

theorem cell23_870654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_870654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870654 prefixEnd_870654 := by exact prefixLift 870654
  have htrace : WordTrace (prefixWord ++ tailWord_870654) baseStart_870654 baseEnd_870654 := by
    simpa [prefixWord, tailWord_870654, baseEnd_870654] using wordTrace_append hprefix tailTrace_870654
  have hstable : (prefixWord ++ tailWord_870654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870654).length < 2 ^ (prefixWord ++ tailWord_870654).sum := by decide
  have hdescent : baseEnd_870654 < baseStart_870654 := by decide
  rcases family_descends (prefixWord ++ tailWord_870654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870684 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_870684 : Nat := 118140960795 + 870684 * 2 ^ 59
def prefixEnd_870684 : Nat := 4983230072969 + 3 ^ 40 * 870684 * 2
def baseEnd_870684 : Nat := 447079390179376678545803

theorem tailTrace_870684 : CollatzResearch.WordTrace tailWord_870684 prefixEnd_870684 447079390179376678545803 := by
  unfold tailWord_870684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878227188834021916809553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21170969585112029222412737 15878227188834021916809553)
  ·
    refine ⟨11908670391625516437607165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15878227188834021916809553 11908670391625516437607165)
    ·
      refine ⟨4465751396859568664102687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11908670391625516437607165 4465751396859568664102687)
      ·
        refine ⟨6698627095289352996154031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465751396859568664102687 6698627095289352996154031)
        ·
          refine ⟨10047940642934029494231047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6698627095289352996154031 10047940642934029494231047)
          ·
            refine ⟨15071910964401044241346571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10047940642934029494231047 15071910964401044241346571)
            ·
              refine ⟨22607866446601566362019857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15071910964401044241346571 22607866446601566362019857)
              ·
                refine ⟨16955899834951174771514893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22607866446601566362019857 16955899834951174771514893)
                ·
                  refine ⟨6358462438106690539318085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16955899834951174771514893 6358462438106690539318085)
                  ·
                    refine ⟨1192211707145004476122141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358462438106690539318085 1192211707145004476122141)
                    ·
                      refine ⟨447079390179376678545803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192211707145004476122141 447079390179376678545803)
                      ·
                        rfl

theorem cell23_870684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_870684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870684 prefixEnd_870684 := by exact prefixLift 870684
  have htrace : WordTrace (prefixWord ++ tailWord_870684) baseStart_870684 baseEnd_870684 := by
    simpa [prefixWord, tailWord_870684, baseEnd_870684] using wordTrace_append hprefix tailTrace_870684
  have hstable : (prefixWord ++ tailWord_870684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870684).length < 2 ^ (prefixWord ++ tailWord_870684).sum := by decide
  have hdescent : baseEnd_870684 < baseStart_870684 := by decide
  rcases family_descends (prefixWord ++ tailWord_870684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870708 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_870708 : Nat := 118140960795 + 870708 * 2 ^ 59
def prefixEnd_870708 : Nat := 4983230072969 + 3 ^ 40 * 870708 * 2
def baseEnd_870708 : Nat := 149030571238361528215231

theorem tailTrace_870708 : CollatzResearch.WordTrace tailWord_870708 prefixEnd_870708 149030571238361528215231 := by
  unfold tailWord_870708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878664864790547966246389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21171553153054063954995185 15878664864790547966246389)
  ·
    refine ⟨1488624831074113871835599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15878664864790547966246389 1488624831074113871835599)
    ·
      refine ⟨2232937246611170807753399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488624831074113871835599 2232937246611170807753399)
      ·
        refine ⟨3349405869916756211630099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232937246611170807753399 3349405869916756211630099)
        ·
          refine ⟨5024108804875134317445149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349405869916756211630099 5024108804875134317445149)
          ·
            refine ⟨1884040801828175369041931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5024108804875134317445149 1884040801828175369041931)
            ·
              refine ⟨2826061202742263053562897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884040801828175369041931 2826061202742263053562897)
              ·
                refine ⟨2119545902056697290172173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2826061202742263053562897 2119545902056697290172173)
                ·
                  refine ⟨794829713271261483814565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2119545902056697290172173 794829713271261483814565)
                  ·
                    refine ⟨149030571238361528215231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794829713271261483814565 149030571238361528215231)
                    ·
                      rfl

theorem cell23_870708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_870708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870708 prefixEnd_870708 := by exact prefixLift 870708
  have htrace : WordTrace (prefixWord ++ tailWord_870708) baseStart_870708 baseEnd_870708 := by
    simpa [prefixWord, tailWord_870708, baseEnd_870708] using wordTrace_append hprefix tailTrace_870708
  have hstable : (prefixWord ++ tailWord_870708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870708).length < 2 ^ (prefixWord ++ tailWord_870708).sum := by decide
  have hdescent : baseEnd_870708 < baseStart_870708 := by decide
  rcases family_descends (prefixWord ++ tailWord_870708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870718 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_870718 : Nat := 118140960795 + 870718 * 2 ^ 59
def prefixEnd_870718 : Nat := 4983230072969 + 3 ^ 40 * 870718 * 2
def baseEnd_870718 : Nat := 447096848521629545520647

theorem tailTrace_870718 : CollatzResearch.WordTrace tailWord_870718 prefixEnd_870718 447096848521629545520647 := by
  unfold tailWord_870718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969711807443108455044601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21171796306363245093571205 3969711807443108455044601)
  ·
    refine ⟨2977283855582331341283451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3969711807443108455044601 2977283855582331341283451)
    ·
      refine ⟨4465925783373497011925177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977283855582331341283451 4465925783373497011925177)
      ·
        refine ⟨3349444337530122758943883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4465925783373497011925177 3349444337530122758943883)
        ·
          refine ⟨5024166506295184138415825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349444337530122758943883 5024166506295184138415825)
          ·
            refine ⟨3768124879721388103811869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5024166506295184138415825 3768124879721388103811869)
            ·
              refine ⟨1413046829895520538929451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3768124879721388103811869 1413046829895520538929451)
              ·
                refine ⟨2119570244843280808394177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413046829895520538929451 2119570244843280808394177)
                ·
                  refine ⟨1589677683632460606295633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2119570244843280808394177 1589677683632460606295633)
                  ·
                    refine ⟨1192258262724345454721725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1589677683632460606295633 1192258262724345454721725)
                    ·
                      refine ⟨447096848521629545520647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192258262724345454721725 447096848521629545520647)
                      ·
                        rfl

theorem cell23_870718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_870718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870718 prefixEnd_870718 := by exact prefixLift 870718
  have htrace : WordTrace (prefixWord ++ tailWord_870718) baseStart_870718 baseEnd_870718 := by
    simpa [prefixWord, tailWord_870718, baseEnd_870718] using wordTrace_append hprefix tailTrace_870718
  have hstable : (prefixWord ++ tailWord_870718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870718).length < 2 ^ (prefixWord ++ tailWord_870718).sum := by decide
  have hdescent : baseEnd_870718 < baseStart_870718 := by decide
  rcases family_descends (prefixWord ++ tailWord_870718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870734 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_870734 : Nat := 118140960795 + 870734 * 2 ^ 59
def prefixEnd_870734 : Nat := 4983230072969 + 3 ^ 40 * 870734 * 2
def baseEnd_870734 : Nat := 149035021404033827640191

theorem tailTrace_870734 : CollatzResearch.WordTrace tailWord_870734 prefixEnd_870734 149035021404033827640191 := by
  unfold tailWord_870734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969784753435862796617407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21172185351657934915292837 3969784753435862796617407)
  ·
    refine ⟨5954677130153794194926111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3969784753435862796617407 5954677130153794194926111)
    ·
      refine ⟨8932015695230691292389167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5954677130153794194926111 8932015695230691292389167)
      ·
        refine ⟨13398023542846036938583751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8932015695230691292389167 13398023542846036938583751)
        ·
          refine ⟨20097035314269055407875627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13398023542846036938583751 20097035314269055407875627)
          ·
            refine ⟨30145552971403583111813441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20097035314269055407875627 30145552971403583111813441)
            ·
              refine ⟨22609164728552687333860081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30145552971403583111813441 22609164728552687333860081)
              ·
                refine ⟨16956873546414515500395061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22609164728552687333860081 16956873546414515500395061)
                ·
                  refine ⟨1589706894976360828162037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16956873546414515500395061 1589706894976360828162037)
                  ·
                    refine ⟨149035021404033827640191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1589706894976360828162037 149035021404033827640191)
                    ·
                      rfl

theorem cell23_870734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_870734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870734 prefixEnd_870734 := by exact prefixLift 870734
  have htrace : WordTrace (prefixWord ++ tailWord_870734) baseStart_870734 baseEnd_870734 := by
    simpa [prefixWord, tailWord_870734, baseEnd_870734] using wordTrace_append hprefix tailTrace_870734
  have hstable : (prefixWord ++ tailWord_870734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870734).length < 2 ^ (prefixWord ++ tailWord_870734).sum := by decide
  have hdescent : baseEnd_870734 < baseStart_870734 := by decide
  rcases family_descends (prefixWord ++ tailWord_870734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870781 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_870781 : Nat := 118140960795 + 870781 * 2 ^ 59
def prefixEnd_870781 : Nat := 4983230072969 + 3 ^ 40 * 870781 * 2
def baseEnd_870781 : Nat := 149043065934287599677619

theorem tailTrace_870781 : CollatzResearch.WordTrace tailWord_870781 prefixEnd_870781 149043065934287599677619 := by
  unfold tailWord_870781
  simp only [CollatzResearch.WordTrace]
  refine ⟨31759992258316629399900197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21173328172211086266600131 31759992258316629399900197)
  ·
    refine ⟨5954998548434368012481287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31759992258316629399900197 5954998548434368012481287)
    ·
      refine ⟨8932497822651552018721931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5954998548434368012481287 8932497822651552018721931)
      ·
        refine ⟨13398746733977328028082897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8932497822651552018721931 13398746733977328028082897)
        ·
          refine ⟨10049060050482996021062173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13398746733977328028082897 10049060050482996021062173)
          ·
            refine ⟨3768397518931123507898315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10049060050482996021062173 3768397518931123507898315)
            ·
              refine ⟨5652596278396685261847473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3768397518931123507898315 5652596278396685261847473)
              ·
                refine ⟨4239447208797513946385605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5652596278396685261847473 4239447208797513946385605)
                ·
                  refine ⟨794896351649533864947301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4239447208797513946385605 794896351649533864947301)
                  ·
                    refine ⟨149043065934287599677619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794896351649533864947301 149043065934287599677619)
                    ·
                      rfl

theorem cell23_870781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_870781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870781 prefixEnd_870781 := by exact prefixLift 870781
  have htrace : WordTrace (prefixWord ++ tailWord_870781) baseStart_870781 baseEnd_870781 := by
    simpa [prefixWord, tailWord_870781, baseEnd_870781] using wordTrace_append hprefix tailTrace_870781
  have hstable : (prefixWord ++ tailWord_870781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870781).length < 2 ^ (prefixWord ++ tailWord_870781).sum := by decide
  have hdescent : baseEnd_870781 < baseStart_870781 := by decide
  rcases family_descends (prefixWord ++ tailWord_870781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870791 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_870791 : Nat := 118140960795 + 870791 * 2 ^ 59
def prefixEnd_870791 : Nat := 4983230072969 + 3 ^ 40 * 870791 * 2
def baseEnd_870791 : Nat := 447134332609407759907811

theorem tailTrace_870791 : CollatzResearch.WordTrace tailWord_870791 prefixEnd_870791 447134332609407759907811 := by
  unfold tailWord_870791
  simp only [CollatzResearch.WordTrace]
  refine ⟨31760356988280401107764227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21173571325520267405176151 31760356988280401107764227)
  ·
    refine ⟨47640535482420601661646341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31760356988280401107764227 47640535482420601661646341)
    ·
      refine ⟨8932600402953862811558689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47640535482420601661646341 8932600402953862811558689)
      ·
        refine ⟨6699450302215397108669017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8932600402953862811558689 6699450302215397108669017)
        ·
          refine ⟨5024587726661547831501763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699450302215397108669017 5024587726661547831501763)
          ·
            refine ⟨7536881589992321747252645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024587726661547831501763 7536881589992321747252645)
            ·
              refine ⟨1413165298123560327609871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7536881589992321747252645 1413165298123560327609871)
              ·
                refine ⟨2119747947185340491414807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413165298123560327609871 2119747947185340491414807)
                ·
                  refine ⟨3179621920778010737122211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119747947185340491414807 3179621920778010737122211)
                  ·
                    refine ⟨4769432881167016105683317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3179621920778010737122211 4769432881167016105683317)
                    ·
                      refine ⟨447134332609407759907811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4769432881167016105683317 447134332609407759907811)
                      ·
                        rfl

theorem cell23_870791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_870791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870791 prefixEnd_870791 := by exact prefixLift 870791
  have htrace : WordTrace (prefixWord ++ tailWord_870791) baseStart_870791 baseEnd_870791 := by
    simpa [prefixWord, tailWord_870791, baseEnd_870791] using wordTrace_append hprefix tailTrace_870791
  have hstable : (prefixWord ++ tailWord_870791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870791).length < 2 ^ (prefixWord ++ tailWord_870791).sum := by decide
  have hdescent : baseEnd_870791 < baseStart_870791 := by decide
  rcases family_descends (prefixWord ++ tailWord_870791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870798 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_870798 : Nat := 118140960795 + 870798 * 2 ^ 59
def prefixEnd_870798 : Nat := 4983230072969 + 3 ^ 40 * 870798 * 2
def baseEnd_870798 : Nat := 149045975657996410840093

theorem tailTrace_870798 : CollatzResearch.WordTrace tailWord_870798 prefixEnd_870798 149045975657996410840093 := by
  unfold tailWord_870798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970076537406880162908631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21173741532836694202179365 3970076537406880162908631)
  ·
    refine ⟨5955114806110320244362947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3970076537406880162908631 5955114806110320244362947)
    ·
      refine ⟨8932672209165480366544421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5955114806110320244362947 8932672209165480366544421)
      ·
        refine ⟨1674876039218527568727079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8932672209165480366544421 1674876039218527568727079)
        ·
          refine ⟨2512314058827791353090619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674876039218527568727079 2512314058827791353090619)
          ·
            refine ⟨3768471088241687029635929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512314058827791353090619 3768471088241687029635929)
            ·
              refine ⟨2826353316181265272226947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3768471088241687029635929 2826353316181265272226947)
              ·
                refine ⟨4239529974271897908340421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826353316181265272226947 4239529974271897908340421)
                ·
                  refine ⟨794911870175980857813829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4239529974271897908340421 794911870175980857813829)
                  ·
                    refine ⟨149045975657996410840093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794911870175980857813829 149045975657996410840093)
                    ·
                      rfl

theorem cell23_870798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_870798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870798 prefixEnd_870798 := by exact prefixLift 870798
  have htrace : WordTrace (prefixWord ++ tailWord_870798) baseStart_870798 baseEnd_870798 := by
    simpa [prefixWord, tailWord_870798, baseEnd_870798] using wordTrace_append hprefix tailTrace_870798
  have hstable : (prefixWord ++ tailWord_870798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870798).length < 2 ^ (prefixWord ++ tailWord_870798).sum := by decide
  have hdescent : baseEnd_870798 < baseStart_870798 := by decide
  rcases family_descends (prefixWord ++ tailWord_870798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870806 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_870806 : Nat := 118140960795 + 870806 * 2 ^ 59
def prefixEnd_870806 : Nat := 4983230072969 + 3 ^ 40 * 870806 * 2
def baseEnd_870806 : Nat := 49682448313247244580027

theorem tailTrace_870806 : CollatzResearch.WordTrace tailWord_870806 prefixEnd_870806 49682448313247244580027 := by
  unfold tailWord_870806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985056505201628666847517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21173936055484039113040181 1985056505201628666847517)
  ·
    refine ⟨744396189450610750067819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1985056505201628666847517 744396189450610750067819)
    ·
      refine ⟨1116594284175916125101729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 744396189450610750067819 1116594284175916125101729)
      ·
        refine ⟨837445713131937093826297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1116594284175916125101729 837445713131937093826297)
        ·
          refine ⟨628084284848952820369723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837445713131937093826297 628084284848952820369723)
          ·
            refine ⟨942126427273429230554585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628084284848952820369723 942126427273429230554585)
            ·
              refine ⟨706594820455071922915939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942126427273429230554585 706594820455071922915939)
              ·
                refine ⟨1059892230682607884373909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706594820455071922915939 1059892230682607884373909)
                ·
                  refine ⟨49682448313247244580027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1059892230682607884373909 49682448313247244580027)
                  ·
                    rfl

theorem cell23_870806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_870806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870806 prefixEnd_870806 := by exact prefixLift 870806
  have htrace : WordTrace (prefixWord ++ tailWord_870806) baseStart_870806 baseEnd_870806 := by
    simpa [prefixWord, tailWord_870806, baseEnd_870806] using wordTrace_append hprefix tailTrace_870806
  have hstable : (prefixWord ++ tailWord_870806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870806).length < 2 ^ (prefixWord ++ tailWord_870806).sum := by decide
  have hdescent : baseEnd_870806 < baseStart_870806 := by decide
  rcases family_descends (prefixWord ++ tailWord_870806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870821 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_870821 : Nat := 118140960795 + 870821 * 2 ^ 59
def prefixEnd_870821 : Nat := 4983230072969 + 3 ^ 40 * 870821 * 2
def baseEnd_870821 : Nat := 447149737029042642532673

theorem tailTrace_870821 : CollatzResearch.WordTrace tailWord_870821 prefixEnd_870821 447149737029042642532673 := by
  unfold tailWord_870821
  simp only [CollatzResearch.WordTrace]
  refine ⟨31761451178171716231356317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21174300785447810820904211 31761451178171716231356317)
  ·
    refine ⟨11910544191814393586758619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31761451178171716231356317 11910544191814393586758619)
    ·
      refine ⟨17865816287721590380137929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11910544191814393586758619 17865816287721590380137929)
      ·
        refine ⟨13399362215791192785103447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17865816287721590380137929 13399362215791192785103447)
        ·
          refine ⟨20099043323686789177655171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13399362215791192785103447 20099043323686789177655171)
          ·
            refine ⟨30148564985530183766482757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20099043323686789177655171 30148564985530183766482757)
            ·
              refine ⟨5652855934786909456215517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30148564985530183766482757 5652855934786909456215517)
              ·
                refine ⟨2119820975545091046080819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5652855934786909456215517 2119820975545091046080819)
                ·
                  refine ⟨3179731463317636569121229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119820975545091046080819 3179731463317636569121229)
                  ·
                    refine ⟨1192399298744113713420461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179731463317636569121229 1192399298744113713420461)
                    ·
                      refine ⟨447149737029042642532673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192399298744113713420461 447149737029042642532673)
                      ·
                        rfl

theorem cell23_870821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_870821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870821 prefixEnd_870821 := by exact prefixLift 870821
  have htrace : WordTrace (prefixWord ++ tailWord_870821) baseStart_870821 baseEnd_870821 := by
    simpa [prefixWord, tailWord_870821, baseEnd_870821] using wordTrace_append hprefix tailTrace_870821
  have hstable : (prefixWord ++ tailWord_870821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870821).length < 2 ^ (prefixWord ++ tailWord_870821).sum := by decide
  have hdescent : baseEnd_870821 < baseStart_870821 := by decide
  rcases family_descends (prefixWord ++ tailWord_870821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870849 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 2, 4]
def baseStart_870849 : Nat := 118140960795 + 870849 * 2 ^ 59
def prefixEnd_870849 : Nat := 4983230072969 + 3 ^ 40 * 870849 * 2
def baseEnd_870849 : Nat := 149054704829122844327515

theorem tailTrace_870849 : CollatzResearch.WordTrace tailWord_870849 prefixEnd_870849 149054704829122844327515 := by
  unfold tailWord_870849
  simp only [CollatzResearch.WordTrace]
  refine ⟨31762472422070277013375601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21174981614713518008917067 31762472422070277013375601)
  ·
    refine ⟨23821854316552707760031701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31762472422070277013375601 23821854316552707760031701)
    ·
      refine ⟨558324710544204088125743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23821854316552707760031701 558324710544204088125743)
      ·
        refine ⟨837487065816306132188615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558324710544204088125743 837487065816306132188615)
        ·
          refine ⟨1256230598724459198282923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837487065816306132188615 1256230598724459198282923)
          ·
            refine ⟨1884345898086688797424385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256230598724459198282923 1884345898086688797424385)
            ·
              refine ⟨1413259423565016598068289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884345898086688797424385 1413259423565016598068289)
              ·
                refine ⟨1059944567673762448551217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413259423565016598068289 1059944567673762448551217)
                ·
                  refine ⟨794958425755321836413413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059944567673762448551217 794958425755321836413413)
                  ·
                    refine ⟨149054704829122844327515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794958425755321836413413 149054704829122844327515)
                    ·
                      rfl

theorem cell23_870849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_870849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870849 prefixEnd_870849 := by exact prefixLift 870849
  have htrace : WordTrace (prefixWord ++ tailWord_870849) baseStart_870849 baseEnd_870849 := by
    simpa [prefixWord, tailWord_870849, baseEnd_870849] using wordTrace_append hprefix tailTrace_870849
  have hstable : (prefixWord ++ tailWord_870849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870849).length < 2 ^ (prefixWord ++ tailWord_870849).sum := by decide
  have hdescent : baseEnd_870849 < baseStart_870849 := by decide
  rcases family_descends (prefixWord ++ tailWord_870849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870855 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_870855 : Nat := 118140960795 + 870855 * 2 ^ 59
def prefixEnd_870855 : Nat := 4983230072969 + 3 ^ 40 * 870855 * 2
def baseEnd_870855 : Nat := 447167195371295509507517

theorem tailTrace_870855 : CollatzResearch.WordTrace tailWord_870855 prefixEnd_870855 447167195371295509507517 := by
  unfold tailWord_870855
  simp only [CollatzResearch.WordTrace]
  refine ⟨31762691260048540038094019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21175127506699026692062679 31762691260048540038094019)
  ·
    refine ⟨47644036890072810057141029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31762691260048540038094019 47644036890072810057141029)
    ·
      refine ⟨8933256916888651885713943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47644036890072810057141029 8933256916888651885713943)
      ·
        refine ⟨13399885375332977828570915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933256916888651885713943 13399885375332977828570915)
        ·
          refine ⟨20099828062999466742856373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13399885375332977828570915 20099828062999466742856373)
          ·
            refine ⟨1884358880906200007142785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20099828062999466742856373 1884358880906200007142785)
            ·
              refine ⟨1413269160679650005357089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884358880906200007142785 1413269160679650005357089)
              ·
                refine ⟨1059951870509737504017817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413269160679650005357089 1059951870509737504017817)
                ·
                  refine ⟨794963902882303128013363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059951870509737504017817 794963902882303128013363)
                  ·
                    refine ⟨1192445854323454692020045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 794963902882303128013363 1192445854323454692020045)
                    ·
                      refine ⟨447167195371295509507517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192445854323454692020045 447167195371295509507517)
                      ·
                        rfl

theorem cell23_870855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_870855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870855 prefixEnd_870855 := by exact prefixLift 870855
  have htrace : WordTrace (prefixWord ++ tailWord_870855) baseStart_870855 baseEnd_870855 := by
    simpa [prefixWord, tailWord_870855, baseEnd_870855] using wordTrace_append hprefix tailTrace_870855
  have hstable : (prefixWord ++ tailWord_870855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870855).length < 2 ^ (prefixWord ++ tailWord_870855).sum := by decide
  have hdescent : baseEnd_870855 < baseStart_870855 := by decide
  rcases family_descends (prefixWord ++ tailWord_870855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870881 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_870881 : Nat := 118140960795 + 870881 * 2 ^ 59
def prefixEnd_870881 : Nat := 4983230072969 + 3 ^ 40 * 870881 * 2
def baseEnd_870881 : Nat := 447180545868312407782397

theorem tailTrace_870881 : CollatzResearch.WordTrace tailWord_870881 prefixEnd_870881 447180545868312407782397 := by
  unfold tailWord_870881
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763639557954346478540497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21175759705302897652360331 31763639557954346478540497)
  ·
    refine ⟨23822729668465759858905373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31763639557954346478540497 23822729668465759858905373)
    ·
      refine ⟨8933523625674659947089515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23822729668465759858905373 8933523625674659947089515)
      ·
        refine ⟨13400285438511989920634273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933523625674659947089515 13400285438511989920634273)
        ·
          refine ⟨10050214078883992440475705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13400285438511989920634273 10050214078883992440475705)
          ·
            refine ⟨7537660559162994330356779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10050214078883992440475705 7537660559162994330356779)
            ·
              refine ⟨11306490838744491495535169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537660559162994330356779 11306490838744491495535169)
              ·
                refine ⟨8479868129058368621651377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11306490838744491495535169 8479868129058368621651377)
                ·
                  refine ⟨6359901096793776466238533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479868129058368621651377 6359901096793776466238533)
                  ·
                    refine ⟨1192481455648833087419725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359901096793776466238533 1192481455648833087419725)
                    ·
                      refine ⟨447180545868312407782397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192481455648833087419725 447180545868312407782397)
                      ·
                        rfl

theorem cell23_870881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_870881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870881 prefixEnd_870881 := by exact prefixLift 870881
  have htrace : WordTrace (prefixWord ++ tailWord_870881) baseStart_870881 baseEnd_870881 := by
    simpa [prefixWord, tailWord_870881, baseEnd_870881] using wordTrace_append hprefix tailTrace_870881
  have hstable : (prefixWord ++ tailWord_870881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870881).length < 2 ^ (prefixWord ++ tailWord_870881).sum := by decide
  have hdescent : baseEnd_870881 < baseStart_870881 := by decide
  rcases family_descends (prefixWord ++ tailWord_870881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870911 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 3]
def baseStart_870911 : Nat := 118140960795 + 870911 * 2 ^ 59
def prefixEnd_870911 : Nat := 4983230072969 + 3 ^ 40 * 870911 * 2
def baseEnd_870911 : Nat := 447195950287947290407259

theorem tailTrace_870911 : CollatzResearch.WordTrace tailWord_870911 prefixEnd_870911 447195950287947290407259 := by
  unfold tailWord_870911
  simp only [CollatzResearch.WordTrace]
  refine ⟨31764733747845661602132587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21176489165230441068088391 31764733747845661602132587)
  ·
    refine ⟨47647100621768492403198881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31764733747845661602132587 47647100621768492403198881)
    ·
      refine ⟨35735325466326369302399161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47647100621768492403198881 35735325466326369302399161)
      ·
        refine ⟨26801494099744776976799371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35735325466326369302399161 26801494099744776976799371)
        ·
          refine ⟨40202241149617165465199057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26801494099744776976799371 40202241149617165465199057)
          ·
            refine ⟨30151680862212874098899293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40202241149617165465199057 30151680862212874098899293)
            ·
              refine ⟨11306880323329827787087235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30151680862212874098899293 11306880323329827787087235)
              ·
                refine ⟨16960320484994741680630853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306880323329827787087235 16960320484994741680630853)
                ·
                  refine ⟨3180060090936514065118285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16960320484994741680630853 3180060090936514065118285)
                  ·
                    refine ⟨1192522534101192774419357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180060090936514065118285 1192522534101192774419357)
                    ·
                      refine ⟨447195950287947290407259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192522534101192774419357 447195950287947290407259)
                      ·
                        rfl

theorem cell23_870911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_870911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870911 prefixEnd_870911 := by exact prefixLift 870911
  have htrace : WordTrace (prefixWord ++ tailWord_870911) baseStart_870911 baseEnd_870911 := by
    simpa [prefixWord, tailWord_870911, baseEnd_870911] using wordTrace_append hprefix tailTrace_870911
  have hstable : (prefixWord ++ tailWord_870911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870911).length < 2 ^ (prefixWord ++ tailWord_870911).sum := by decide
  have hdescent : baseEnd_870911 < baseStart_870911 := by decide
  rcases family_descends (prefixWord ++ tailWord_870911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870938 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2]
def baseStart_870938 : Nat := 118140960795 + 870938 * 2 ^ 59
def prefixEnd_870938 : Nat := 4983230072969 + 3 ^ 40 * 870938 * 2
def baseEnd_870938 : Nat := 447209814265618684769635

theorem tailTrace_870938 : CollatzResearch.WordTrace tailWord_870938 prefixEnd_870938 447209814265618684769635 := by
  unfold tailWord_870938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941429629686961303341367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21177145679165230142243645 7941429629686961303341367)
  ·
    refine ⟨11912144444530441955012051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7941429629686961303341367 11912144444530441955012051)
    ·
      refine ⟨17868216666795662932518077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11912144444530441955012051 17868216666795662932518077)
      ·
        refine ⟨6700581250048373599694279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17868216666795662932518077 6700581250048373599694279)
        ·
          refine ⟨10050871875072560399541419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700581250048373599694279 10050871875072560399541419)
          ·
            refine ⟨15076307812608840599312129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10050871875072560399541419 15076307812608840599312129)
            ·
              refine ⟨11307230859456630449484097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15076307812608840599312129 11307230859456630449484097)
              ·
                refine ⟨8480423144592472837113073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11307230859456630449484097 8480423144592472837113073)
                ·
                  refine ⟨6360317358444354627834805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8480423144592472837113073 6360317358444354627834805)
                  ·
                    refine ⟨596279752354158246359513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6360317358444354627834805 596279752354158246359513)
                    ·
                      refine ⟨447209814265618684769635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 596279752354158246359513 447209814265618684769635)
                      ·
                        rfl

theorem cell23_870938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_870938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870938 prefixEnd_870938 := by exact prefixLift 870938
  have htrace : WordTrace (prefixWord ++ tailWord_870938) baseStart_870938 baseEnd_870938 := by
    simpa [prefixWord, tailWord_870938, baseEnd_870938] using wordTrace_append hprefix tailTrace_870938
  have hstable : (prefixWord ++ tailWord_870938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870938).length < 2 ^ (prefixWord ++ tailWord_870938).sum := by decide
  have hdescent : baseEnd_870938 < baseStart_870938 := by decide
  rcases family_descends (prefixWord ++ tailWord_870938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870952 : List Nat := [2, 1, 5, 2, 1, 3, 1, 3, 5]
def baseStart_870952 : Nat := 118140960795 + 870952 * 2 ^ 59
def prefixEnd_870952 : Nat := 4983230072969 + 3 ^ 40 * 870952 * 2
def baseEnd_870952 : Nat := 49690778110531292221619

theorem tailTrace_870952 : CollatzResearch.WordTrace tailWord_870952 prefixEnd_870952 49690778110531292221619 := by
  unfold tailWord_870952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883114570348562802187555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21177486093798083736250073 15883114570348562802187555)
  ·
    refine ⟨23824671855522844203281333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15883114570348562802187555 23824671855522844203281333)
    ·
      refine ⟨2233562986455266644057625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23824671855522844203281333 2233562986455266644057625)
      ·
        refine ⟨1675172239841449983043219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233562986455266644057625 1675172239841449983043219)
        ·
          refine ⟨2512758359762174974564829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675172239841449983043219 2512758359762174974564829)
          ·
            refine ⟨942284384910815615461811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2512758359762174974564829 942284384910815615461811)
            ·
              refine ⟨1413426577366223423192717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942284384910815615461811 1413426577366223423192717)
              ·
                refine ⟨530034966512333783697269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413426577366223423192717 530034966512333783697269)
                ·
                  refine ⟨49690778110531292221619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530034966512333783697269 49690778110531292221619)
                  ·
                    rfl

theorem cell23_870952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 5].length) (baseStart_870952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870952 prefixEnd_870952 := by exact prefixLift 870952
  have htrace : WordTrace (prefixWord ++ tailWord_870952) baseStart_870952 baseEnd_870952 := by
    simpa [prefixWord, tailWord_870952, baseEnd_870952] using wordTrace_append hprefix tailTrace_870952
  have hstable : (prefixWord ++ tailWord_870952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870952).length < 2 ^ (prefixWord ++ tailWord_870952).sum := by decide
  have hdescent : baseEnd_870952 < baseStart_870952 := by decide
  rcases family_descends (prefixWord ++ tailWord_870952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870968 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_870968 : Nat := 118140960795 + 870968 * 2 ^ 59
def prefixEnd_870968 : Nat := 4983230072969 + 3 ^ 40 * 870968 * 2
def baseEnd_870968 : Nat := 447225218685253567394497

theorem tailTrace_870968 : CollatzResearch.WordTrace tailWord_870968 prefixEnd_870968 447225218685253567394497 := by
  unfold tailWord_870968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883406354319580168478779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21177875139092773557971705 15883406354319580168478779)
  ·
    refine ⟨23825109531479370252718169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15883406354319580168478779 23825109531479370252718169)
    ·
      refine ⟨17868832148609527689538627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23825109531479370252718169 17868832148609527689538627)
      ·
        refine ⟨26803248222914291534307941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17868832148609527689538627 26803248222914291534307941)
        ·
          refine ⟨5025609041796429662682739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26803248222914291534307941 5025609041796429662682739)
          ·
            refine ⟨7538413562694644494024109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025609041796429662682739 7538413562694644494024109)
            ·
              refine ⟨2826905086010491685259041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7538413562694644494024109 2826905086010491685259041)
              ·
                refine ⟨2120178814507868763944281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2826905086010491685259041 2120178814507868763944281)
                ·
                  refine ⟨1590134110880901572958211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2120178814507868763944281 1590134110880901572958211)
                  ·
                    refine ⟨2385201166321352359437317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1590134110880901572958211 2385201166321352359437317)
                    ·
                      refine ⟨447225218685253567394497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2385201166321352359437317 447225218685253567394497)
                      ·
                        rfl

theorem cell23_870968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_870968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870968 prefixEnd_870968 := by exact prefixLift 870968
  have htrace : WordTrace (prefixWord ++ tailWord_870968) baseStart_870968 baseEnd_870968 := by
    simpa [prefixWord, tailWord_870968, baseEnd_870968] using wordTrace_append hprefix tailTrace_870968
  have hstable : (prefixWord ++ tailWord_870968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870968).length < 2 ^ (prefixWord ++ tailWord_870968).sum := by decide
  have hdescent : baseEnd_870968 < baseStart_870968 := by decide
  rcases family_descends (prefixWord ++ tailWord_870968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870980 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_870980 : Nat := 118140960795 + 870980 * 2 ^ 59
def prefixEnd_870980 : Nat := 4983230072969 + 3 ^ 40 * 870980 * 2
def baseEnd_870980 : Nat := 447231380453107520444443

theorem tailTrace_870980 : CollatzResearch.WordTrace tailWord_870980 prefixEnd_870980 447231380453107520444443 := by
  unfold tailWord_870980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883625192297843193197197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21178166923063790924262929 15883625192297843193197197)
  ·
    refine ⟨5956359447111691197448949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15883625192297843193197197 5956359447111691197448949)
    ·
      refine ⟨558408698166721049760839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5956359447111691197448949 558408698166721049760839)
      ·
        refine ⟨837613047250081574641259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558408698166721049760839 837613047250081574641259)
        ·
          refine ⟨1256419570875122361961889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837613047250081574641259 1256419570875122361961889)
          ·
            refine ⟨942314678156341771471417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1256419570875122361961889 942314678156341771471417)
            ·
              refine ⟨706736008617256328603563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942314678156341771471417 706736008617256328603563)
              ·
                refine ⟨1060104012925884492905345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706736008617256328603563 1060104012925884492905345)
                ·
                  refine ⟨795078009694413369679009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1060104012925884492905345 795078009694413369679009)
                  ·
                    refine ⟨596308507270810027259257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 795078009694413369679009 596308507270810027259257)
                    ·
                      refine ⟨447231380453107520444443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 596308507270810027259257 447231380453107520444443)
                      ·
                        rfl

theorem cell23_870980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_870980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870980 prefixEnd_870980 := by exact prefixLift 870980
  have htrace : WordTrace (prefixWord ++ tailWord_870980) baseStart_870980 baseEnd_870980 := by
    simpa [prefixWord, tailWord_870980, baseEnd_870980] using wordTrace_append hprefix tailTrace_870980
  have hstable : (prefixWord ++ tailWord_870980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870980).length < 2 ^ (prefixWord ++ tailWord_870980).sum := by decide
  have hdescent : baseEnd_870980 < baseStart_870980 := by decide
  rcases family_descends (prefixWord ++ tailWord_870980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870988 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_870988 : Nat := 118140960795 + 870988 * 2 ^ 59
def prefixEnd_870988 : Nat := 4983230072969 + 3 ^ 40 * 870988 * 2
def baseEnd_870988 : Nat := 447235488298343489144405

theorem tailTrace_870988 : CollatzResearch.WordTrace tailWord_870988 prefixEnd_870988 447235488298343489144405 := by
  unfold tailWord_870988
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883771084283351876342809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21178361445711135835123745 15883771084283351876342809)
  ·
    refine ⟨11912828313212513907257107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15883771084283351876342809 11912828313212513907257107)
    ·
      refine ⟨17869242469818770860885661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11912828313212513907257107 17869242469818770860885661)
      ·
        refine ⟨6700965926182039072832123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17869242469818770860885661 6700965926182039072832123)
        ·
          refine ⟨10051448889273058609248185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700965926182039072832123 10051448889273058609248185)
          ·
            refine ⟨7538586666954793956936139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10051448889273058609248185 7538586666954793956936139)
            ·
              refine ⟨11307880000432190935404209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538586666954793956936139 11307880000432190935404209)
              ·
                refine ⟨8480910000324143201553157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11307880000432190935404209 8480910000324143201553157)
                ·
                  refine ⟨1590170625060776850291217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8480910000324143201553157 1590170625060776850291217)
                  ·
                    refine ⟨1192627968795582637718413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590170625060776850291217 1192627968795582637718413)
                    ·
                      refine ⟨447235488298343489144405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192627968795582637718413 447235488298343489144405)
                      ·
                        rfl

theorem cell23_870988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_870988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_870988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_870988 prefixEnd_870988 := by exact prefixLift 870988
  have htrace : WordTrace (prefixWord ++ tailWord_870988) baseStart_870988 baseEnd_870988 := by
    simpa [prefixWord, tailWord_870988, baseEnd_870988] using wordTrace_append hprefix tailTrace_870988
  have hstable : (prefixWord ++ tailWord_870988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870988).length < 2 ^ (prefixWord ++ tailWord_870988).sum := by decide
  have hdescent : baseEnd_870988 < baseStart_870988 := by decide
  rcases family_descends (prefixWord ++ tailWord_870988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871029 : List Nat := [1, 3, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_871029 : Nat := 118140960795 + 871029 * 2 ^ 59
def prefixEnd_871029 : Nat := 4983230072969 + 3 ^ 40 * 871029 * 2
def baseEnd_871029 : Nat := 149085513668392609577239

theorem tailTrace_871029 : CollatzResearch.WordTrace tailWord_871029 prefixEnd_871029 149085513668392609577239 := by
  unfold tailWord_871029
  simp only [CollatzResearch.WordTrace]
  refine ⟨31769037561418167754928141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21179358374278778503285427 31769037561418167754928141)
  ·
    refine ⟨11913389085531812908098053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31769037561418167754928141 11913389085531812908098053)
    ·
      refine ⟨2233760453537214920268385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11913389085531812908098053 2233760453537214920268385)
      ·
        refine ⟨1675320340152911190201289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233760453537214920268385 1675320340152911190201289)
        ·
          refine ⟨1256490255114683392650967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1675320340152911190201289 1256490255114683392650967)
          ·
            refine ⟨1884735382672025088976451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256490255114683392650967 1884735382672025088976451)
            ·
              refine ⟨2827103074008037633464677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884735382672025088976451 2827103074008037633464677)
              ·
                refine ⟨530081826376507056274627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2827103074008037633464677 530081826376507056274627)
                ·
                  refine ⟨795122739564760584411941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530081826376507056274627 795122739564760584411941)
                  ·
                    refine ⟨149085513668392609577239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 795122739564760584411941 149085513668392609577239)
                    ·
                      rfl

theorem cell23_871029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_871029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871029 prefixEnd_871029 := by exact prefixLift 871029
  have htrace : WordTrace (prefixWord ++ tailWord_871029) baseStart_871029 baseEnd_871029 := by
    simpa [prefixWord, tailWord_871029, baseEnd_871029] using wordTrace_append hprefix tailTrace_871029
  have hstable : (prefixWord ++ tailWord_871029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871029).length < 2 ^ (prefixWord ++ tailWord_871029).sum := by decide
  have hdescent : baseEnd_871029 < baseStart_871029 := by decide
  rcases family_descends (prefixWord ++ tailWord_871029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871086 : List Nat := [4, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_871086 : Nat := 118140960795 + 871086 * 2 ^ 59
def prefixEnd_871086 : Nat := 4983230072969 + 3 ^ 40 * 871086 * 2
def baseEnd_871086 : Nat := 447285809402484105718955

theorem tailTrace_871086 : CollatzResearch.WordTrace tailWord_871086 prefixEnd_871086 447285809402484105718955 := by
  unfold tailWord_871086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3971389565276458311219139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21180744348141110993168741 3971389565276458311219139)
  ·
    refine ⟨5957084347914687466828709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3971389565276458311219139 5957084347914687466828709)
    ·
      refine ⟨1116953315234003900030383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5957084347914687466828709 1116953315234003900030383)
      ·
        refine ⟨1675429972851005850045575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1116953315234003900030383 1675429972851005850045575)
        ·
          refine ⟨2513144959276508775068363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675429972851005850045575 2513144959276508775068363)
          ·
            refine ⟨3769717438914763162602545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513144959276508775068363 3769717438914763162602545)
            ·
              refine ⟨2827288079186072371951909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769717438914763162602545 2827288079186072371951909)
              ·
                refine ⟨530116514847388569740983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2827288079186072371951909 530116514847388569740983)
                ·
                  refine ⟨795174772271082854611475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530116514847388569740983 795174772271082854611475)
                  ·
                    refine ⟨1192762158406624281917213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 795174772271082854611475 1192762158406624281917213)
                    ·
                      refine ⟨447285809402484105718955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192762158406624281917213 447285809402484105718955)
                      ·
                        rfl

theorem cell23_871086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_871086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871086 prefixEnd_871086 := by exact prefixLift 871086
  have htrace : WordTrace (prefixWord ++ tailWord_871086) baseStart_871086 baseEnd_871086 := by
    simpa [prefixWord, tailWord_871086, baseEnd_871086] using wordTrace_append hprefix tailTrace_871086
  have hstable : (prefixWord ++ tailWord_871086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871086).length < 2 ^ (prefixWord ++ tailWord_871086).sum := by decide
  have hdescent : baseEnd_871086 < baseStart_871086 := by decide
  rcases family_descends (prefixWord ++ tailWord_871086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871095 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_871095 : Nat := 118140960795 + 871095 * 2 ^ 59
def prefixEnd_871095 : Nat := 4983230072969 + 3 ^ 40 * 871095 * 2
def baseEnd_871095 : Nat := 447290430728374570506413

theorem tailTrace_871095 : CollatzResearch.WordTrace tailWord_871095 prefixEnd_871095 447290430728374570506413 := by
  unfold tailWord_871095
  simp only [CollatzResearch.WordTrace]
  refine ⟨31771444779179061026830739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21180963186119374017887159 31771444779179061026830739)
  ·
    refine ⟨47657167168768591540246109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31771444779179061026830739 47657167168768591540246109)
    ·
      refine ⟨17871437688288221827592291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47657167168768591540246109 17871437688288221827592291)
      ·
        refine ⟨26807156532432332741388437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17871437688288221827592291 26807156532432332741388437)
        ·
          refine ⟨1256585462457765597252583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26807156532432332741388437 1256585462457765597252583)
          ·
            refine ⟨1884878193686648395878875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256585462457765597252583 1884878193686648395878875)
            ·
              refine ⟨2827317290529972593818313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884878193686648395878875 2827317290529972593818313)
              ·
                refine ⟨2120487967897479445363735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827317290529972593818313 2120487967897479445363735)
                ·
                  refine ⟨3180731951846219168045603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120487967897479445363735 3180731951846219168045603)
                  ·
                    refine ⟨4771097927769328752068405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3180731951846219168045603 4771097927769328752068405)
                    ·
                      refine ⟨447290430728374570506413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4771097927769328752068405 447290430728374570506413)
                      ·
                        rfl

theorem cell23_871095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_871095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871095 prefixEnd_871095 := by exact prefixLift 871095
  have htrace : WordTrace (prefixWord ++ tailWord_871095) baseStart_871095 baseEnd_871095 := by
    simpa [prefixWord, tailWord_871095, baseEnd_871095] using wordTrace_append hprefix tailTrace_871095
  have hstable : (prefixWord ++ tailWord_871095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871095).length < 2 ^ (prefixWord ++ tailWord_871095).sum := by decide
  have hdescent : baseEnd_871095 < baseStart_871095 := by decide
  rcases family_descends (prefixWord ++ tailWord_871095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871112 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_871112 : Nat := 118140960795 + 871112 * 2 ^ 59
def prefixEnd_871112 : Nat := 4983230072969 + 3 ^ 40 * 871112 * 2
def baseEnd_871112 : Nat := 447299159899501003993835

theorem tailTrace_871112 : CollatzResearch.WordTrace tailWord_871112 prefixEnd_871112 447299159899501003993835 := by
  unfold tailWord_871112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886032410058736465099795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21181376546744981953466393 15886032410058736465099795)
  ·
    refine ⟨23829048615088104697649693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15886032410058736465099795 23829048615088104697649693)
    ·
      refine ⟨8935893230658039261618635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23829048615088104697649693 8935893230658039261618635)
      ·
        refine ⟨13403839845987058892427953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935893230658039261618635 13403839845987058892427953)
        ·
          refine ⟨10052879884490294169320965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13403839845987058892427953 10052879884490294169320965)
          ·
            refine ⟨1884914978341930156747681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10052879884490294169320965 1884914978341930156747681)
            ·
              refine ⟨1413686233756447617560761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884914978341930156747681 1413686233756447617560761)
              ·
                refine ⟨1060264675317335713170571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413686233756447617560761 1060264675317335713170571)
                ·
                  refine ⟨1590397012976003569755857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060264675317335713170571 1590397012976003569755857)
                  ·
                    refine ⟨1192797759732002677316893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590397012976003569755857 1192797759732002677316893)
                    ·
                      refine ⟨447299159899501003993835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1192797759732002677316893 447299159899501003993835)
                      ·
                        rfl

theorem cell23_871112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_871112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871112 prefixEnd_871112 := by exact prefixLift 871112
  have htrace : WordTrace (prefixWord ++ tailWord_871112) baseStart_871112 baseEnd_871112 := by
    simpa [prefixWord, tailWord_871112, baseEnd_871112] using wordTrace_append hprefix tailTrace_871112
  have hstable : (prefixWord ++ tailWord_871112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871112).length < 2 ^ (prefixWord ++ tailWord_871112).sum := by decide
  have hdescent : baseEnd_871112 < baseStart_871112 := by decide
  rcases family_descends (prefixWord ++ tailWord_871112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871148 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_871148 : Nat := 118140960795 + 871148 * 2 ^ 59
def prefixEnd_871148 : Nat := 4983230072969 + 3 ^ 40 * 871148 * 2
def baseEnd_871148 : Nat := 447317645203062863143669

theorem tailTrace_871148 : CollatzResearch.WordTrace tailWord_871148 prefixEnd_871148 447317645203062863143669 := by
  unfold tailWord_871148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886688923993525539255049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21182251898658034052340065 15886688923993525539255049)
  ·
    refine ⟨11915016692995144154441287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15886688923993525539255049 11915016692995144154441287)
    ·
      refine ⟨17872525039492716231661931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11915016692995144154441287 17872525039492716231661931)
      ·
        refine ⟨26808787559239074347492897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17872525039492716231661931 26808787559239074347492897)
        ·
          refine ⟨20106590669429305760619673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26808787559239074347492897 20106590669429305760619673)
          ·
            refine ⟨15079943002071979320464755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20106590669429305760619673 15079943002071979320464755)
            ·
              refine ⟨22619914503107968980697133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15079943002071979320464755 22619914503107968980697133)
              ·
                refine ⟨8482467938665488367761425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22619914503107968980697133 8482467938665488367761425)
                ·
                  refine ⟨6361850953999116275821069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8482467938665488367761425 6361850953999116275821069)
                  ·
                    refine ⟨2385694107749668603432901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6361850953999116275821069 2385694107749668603432901)
                    ·
                      refine ⟨447317645203062863143669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2385694107749668603432901 447317645203062863143669)
                      ·
                        rfl

theorem cell23_871148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_871148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871148 prefixEnd_871148 := by exact prefixLift 871148
  have htrace : WordTrace (prefixWord ++ tailWord_871148) baseStart_871148 baseEnd_871148 := by
    simpa [prefixWord, tailWord_871148, baseEnd_871148] using wordTrace_append hprefix tailTrace_871148
  have hstable : (prefixWord ++ tailWord_871148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871148).length < 2 ^ (prefixWord ++ tailWord_871148).sum := by decide
  have hdescent : baseEnd_871148 < baseStart_871148 := by decide
  rcases family_descends (prefixWord ++ tailWord_871148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871199 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 2, 2, 2]
def baseStart_871199 : Nat := 118140960795 + 871199 * 2 ^ 59
def prefixEnd_871199 : Nat := 4983230072969 + 3 ^ 40 * 871199 * 2
def baseEnd_871199 : Nat := 447343832716442163605935

theorem tailTrace_871199 : CollatzResearch.WordTrace tailWord_871199 prefixEnd_871199 447343832716442163605935 := by
  unfold tailWord_871199
  simp only [CollatzResearch.WordTrace]
  refine ⟨31775237970802286788616651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21183491980534857859077767 31775237970802286788616651)
  ·
    refine ⟨47662856956203430182924977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31775237970802286788616651 47662856956203430182924977)
    ·
      refine ⟨35747142717152572637193733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47662856956203430182924977 35747142717152572637193733)
      ·
        refine ⟨6702589259466107369473825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35747142717152572637193733 6702589259466107369473825)
        ·
          refine ⟨5026941944599580527105369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702589259466107369473825 5026941944599580527105369)
          ·
            refine ⟨3770206458449685395329027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026941944599580527105369 3770206458449685395329027)
            ·
              refine ⟨5655309687674528092993541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770206458449685395329027 5655309687674528092993541)
              ·
                refine ⟨1060370566438974017436289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5655309687674528092993541 1060370566438974017436289)
                ·
                  refine ⟨795277924829230513077217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1060370566438974017436289 795277924829230513077217)
                  ·
                    refine ⟨596458443621922884807913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 795277924829230513077217 596458443621922884807913)
                    ·
                      refine ⟨447343832716442163605935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 596458443621922884807913 447343832716442163605935)
                      ·
                        rfl

theorem cell23_871199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_871199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871199 prefixEnd_871199 := by exact prefixLift 871199
  have htrace : WordTrace (prefixWord ++ tailWord_871199) baseStart_871199 baseEnd_871199 := by
    simpa [prefixWord, tailWord_871199, baseEnd_871199] using wordTrace_append hprefix tailTrace_871199
  have hstable : (prefixWord ++ tailWord_871199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871199).length < 2 ^ (prefixWord ++ tailWord_871199).sum := by decide
  have hdescent : baseEnd_871199 < baseStart_871199 := by decide
  rcases family_descends (prefixWord ++ tailWord_871199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871275 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 3]
def baseStart_871275 : Nat := 118140960795 + 871275 * 2 ^ 59
def prefixEnd_871275 : Nat := 4983230072969 + 3 ^ 40 * 871275 * 2
def baseEnd_871275 : Nat := 447382857246183866255585

theorem tailTrace_871275 : CollatzResearch.WordTrace tailWord_871275 prefixEnd_871275 447382857246183866255585 := by
  unfold tailWord_871275
  simp only [CollatzResearch.WordTrace]
  refine ⟨31778009918526951768383279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21185339945684634512255519 31778009918526951768383279)
  ·
    refine ⟨47667014877790427652574919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31778009918526951768383279 47667014877790427652574919)
    ·
      refine ⟨71500522316685641478862379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47667014877790427652574919 71500522316685641478862379)
      ·
        refine ⟨107250783475028462218293569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71500522316685641478862379 107250783475028462218293569)
        ·
          refine ⟨80438087606271346663720177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107250783475028462218293569 80438087606271346663720177)
          ·
            refine ⟨60328565704703509997790133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80438087606271346663720177 60328565704703509997790133)
            ·
              refine ⟨5655803034815954062292825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60328565704703509997790133 5655803034815954062292825)
              ·
                refine ⟨4241852276111965546719619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5655803034815954062292825 4241852276111965546719619)
                ·
                  refine ⟨6362778414167948320079429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241852276111965546719619 6362778414167948320079429)
                  ·
                    refine ⟨1193020952656490310014893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6362778414167948320079429 1193020952656490310014893)
                    ·
                      refine ⟨447382857246183866255585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1193020952656490310014893 447382857246183866255585)
                      ·
                        rfl

theorem cell23_871275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 3].length) (baseStart_871275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871275 prefixEnd_871275 := by exact prefixLift 871275
  have htrace : WordTrace (prefixWord ++ tailWord_871275) baseStart_871275 baseEnd_871275 := by
    simpa [prefixWord, tailWord_871275, baseEnd_871275] using wordTrace_append hprefix tailTrace_871275
  have hstable : (prefixWord ++ tailWord_871275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871275).length < 2 ^ (prefixWord ++ tailWord_871275).sum := by decide
  have hdescent : baseEnd_871275 < baseStart_871275 := by decide
  rcases family_descends (prefixWord ++ tailWord_871275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871282 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_871282 : Nat := 118140960795 + 871282 * 2 ^ 59
def prefixEnd_871282 : Nat := 4983230072969 + 3 ^ 40 * 871282 * 2
def baseEnd_871282 : Nat := 149128817203588446289351

theorem tailTrace_871282 : CollatzResearch.WordTrace tailWord_871282 prefixEnd_871282 149128817203588446289351 := by
  unfold tailWord_871282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944566307375397990972025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21185510153001061309258733 7944566307375397990972025)
  ·
    refine ⟨5958424730531548493229019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7944566307375397990972025 5958424730531548493229019)
    ·
      refine ⟨8937637095797322739843529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958424730531548493229019 8937637095797322739843529)
      ·
        refine ⟨6703227821847992054882647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8937637095797322739843529 6703227821847992054882647)
        ·
          refine ⟨10054841732771988082323971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703227821847992054882647 10054841732771988082323971)
          ·
            refine ⟨15082262599157982123485957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054841732771988082323971 15082262599157982123485957)
            ·
              refine ⟨2827924237342121648153617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15082262599157982123485957 2827924237342121648153617)
              ·
                refine ⟨2120943178006591236115213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827924237342121648153617 2120943178006591236115213)
                ·
                  refine ⟨795353691752471713543205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2120943178006591236115213 795353691752471713543205)
                  ·
                    refine ⟨149128817203588446289351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 795353691752471713543205 149128817203588446289351)
                    ·
                      rfl

theorem cell23_871282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_871282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871282 prefixEnd_871282 := by exact prefixLift 871282
  have htrace : WordTrace (prefixWord ++ tailWord_871282) baseStart_871282 baseEnd_871282 := by
    simpa [prefixWord, tailWord_871282, baseEnd_871282] using wordTrace_append hprefix tailTrace_871282
  have hstable : (prefixWord ++ tailWord_871282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871282).length < 2 ^ (prefixWord ++ tailWord_871282).sum := by decide
  have hdescent : baseEnd_871282 < baseStart_871282 := by decide
  rcases family_descends (prefixWord ++ tailWord_871282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871329 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 6]
def baseStart_871329 : Nat := 118140960795 + 871329 * 2 ^ 59
def prefixEnd_871329 : Nat := 4983230072969 + 3 ^ 40 * 871329 * 2
def baseEnd_871329 : Nat := 49712287244614072775593

theorem tailTrace_871329 : CollatzResearch.WordTrace tailWord_871329 prefixEnd_871329 49712287244614072775593 := by
  unfold tailWord_871329
  simp only [CollatzResearch.WordTrace]
  refine ⟨31779979460331318990849041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21186652973554212660566027 31779979460331318990849041)
  ·
    refine ⟨23834984595248489243136781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31779979460331318990849041 23834984595248489243136781)
    ·
      refine ⟨8938119223218183466176293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23834984595248489243136781 8938119223218183466176293)
      ·
        refine ⟨1675897354353409399908055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8938119223218183466176293 1675897354353409399908055)
        ·
          refine ⟨2513846031530114099862083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675897354353409399908055 2513846031530114099862083)
          ·
            refine ⟨3770769047295171149793125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513846031530114099862083 3770769047295171149793125)
            ·
              refine ⟨707019196367844590586211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3770769047295171149793125 707019196367844590586211)
              ·
                refine ⟨1060528794551766885879317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707019196367844590586211 1060528794551766885879317)
                ·
                  refine ⟨49712287244614072775593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1060528794551766885879317 49712287244614072775593)
                  ·
                    rfl

theorem cell23_871329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 6].length) (baseStart_871329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871329 prefixEnd_871329 := by exact prefixLift 871329
  have htrace : WordTrace (prefixWord ++ tailWord_871329) baseStart_871329 baseEnd_871329 := by
    simpa [prefixWord, tailWord_871329, baseEnd_871329] using wordTrace_append hprefix tailTrace_871329
  have hstable : (prefixWord ++ tailWord_871329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871329).length < 2 ^ (prefixWord ++ tailWord_871329).sum := by decide
  have hdescent : baseEnd_871329 < baseStart_871329 := by decide
  rcases family_descends (prefixWord ++ tailWord_871329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871389 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_871389 : Nat := 118140960795 + 871389 * 2 ^ 59
def prefixEnd_871389 : Nat := 4983230072969 + 3 ^ 40 * 871389 * 2
def baseEnd_871389 : Nat := 149147131346932140076687

theorem tailTrace_871389 : CollatzResearch.WordTrace tailWord_871389 prefixEnd_871389 149147131346932140076687 := by
  unfold tailWord_871389
  simp only [CollatzResearch.WordTrace]
  refine ⟨31782167840113949238033221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21188111893409299492022147 31782167840113949238033221)
  ·
    refine ⟨5959156470021365482131229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31782167840113949238033221 5959156470021365482131229)
    ·
      refine ⟨2234683676258012055799211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5959156470021365482131229 2234683676258012055799211)
      ·
        refine ⟨3352025514387018083698817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234683676258012055799211 3352025514387018083698817)
        ·
          refine ⟨2514019135790263562774113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3352025514387018083698817 2514019135790263562774113)
          ·
            refine ⟨1885514351842697672080585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514019135790263562774113 1885514351842697672080585)
            ·
              refine ⟨1414135763882023254060439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885514351842697672080585 1414135763882023254060439)
              ·
                refine ⟨2121203645823034881090659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414135763882023254060439 2121203645823034881090659)
                ·
                  refine ⟨3181805468734552321635989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121203645823034881090659 3181805468734552321635989)
                  ·
                    refine ⟨149147131346932140076687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3181805468734552321635989 149147131346932140076687)
                    ·
                      rfl

theorem cell23_871389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_871389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871389 prefixEnd_871389 := by exact prefixLift 871389
  have htrace : WordTrace (prefixWord ++ tailWord_871389) baseStart_871389 baseEnd_871389 := by
    simpa [prefixWord, tailWord_871389, baseEnd_871389] using wordTrace_append hprefix tailTrace_871389
  have hstable : (prefixWord ++ tailWord_871389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871389).length < 2 ^ (prefixWord ++ tailWord_871389).sum := by decide
  have hdescent : baseEnd_871389 < baseStart_871389 := by decide
  rcases family_descends (prefixWord ++ tailWord_871389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871399 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_871399 : Nat := 118140960795 + 871399 * 2 ^ 59
def prefixEnd_871399 : Nat := 4983230072969 + 3 ^ 40 * 871399 * 2
def baseEnd_871399 : Nat := 447446528847341381105015

theorem tailTrace_871399 : CollatzResearch.WordTrace tailWord_871399 prefixEnd_871399 447446528847341381105015 := by
  unfold tailWord_871399
  simp only [CollatzResearch.WordTrace]
  refine ⟨31782532570077720945897251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21188355046718480630598167 31782532570077720945897251)
  ·
    refine ⟨47673798855116581418845877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31782532570077720945897251 47673798855116581418845877)
    ·
      refine ⟨4469418642667179508016801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47673798855116581418845877 4469418642667179508016801)
      ·
        refine ⟨3352063982000384631012601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4469418642667179508016801 3352063982000384631012601)
        ·
          refine ⟨2514047986500288473259451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3352063982000384631012601 2514047986500288473259451)
          ·
            refine ⟨3771071979750432709889177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514047986500288473259451 3771071979750432709889177)
            ·
              refine ⟨2828303984812824532416883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771071979750432709889177 2828303984812824532416883)
              ·
                refine ⟨4242455977219236798625325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828303984812824532416883 4242455977219236798625325)
                ·
                  refine ⟨1590920991457213799484497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4242455977219236798625325 1590920991457213799484497)
                  ·
                    refine ⟨1193190743592910349613373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590920991457213799484497 1193190743592910349613373)
                    ·
                      refine ⟨447446528847341381105015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1193190743592910349613373 447446528847341381105015)
                      ·
                        rfl

theorem cell23_871399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_871399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871399 prefixEnd_871399 := by exact prefixLift 871399
  have htrace : WordTrace (prefixWord ++ tailWord_871399) baseStart_871399 baseEnd_871399 := by
    simpa [prefixWord, tailWord_871399, baseEnd_871399] using wordTrace_append hprefix tailTrace_871399
  have hstable : (prefixWord ++ tailWord_871399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871399).length < 2 ^ (prefixWord ++ tailWord_871399).sum := by decide
  have hdescent : baseEnd_871399 < baseStart_871399 := by decide
  rcases family_descends (prefixWord ++ tailWord_871399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871410 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_871410 : Nat := 118140960795 + 871410 * 2 ^ 59
def prefixEnd_871410 : Nat := 4983230072969 + 3 ^ 40 * 871410 * 2
def baseEnd_871410 : Nat := 149150725711513612689155

theorem tailTrace_871410 : CollatzResearch.WordTrace tailWord_871410 prefixEnd_871410 149150725711513612689155 := by
  unfold tailWord_871410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7945733443259467456136921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21188622515358579883031789 7945733443259467456136921)
  ·
    refine ⟨5959300082444600592102691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7945733443259467456136921 5959300082444600592102691)
    ·
      refine ⟨8938950123666900888154037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5959300082444600592102691 8938950123666900888154037)
      ·
        refine ⟨838026574093771958264441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8938950123666900888154037 838026574093771958264441)
        ·
          refine ⟨628519930570328968698331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838026574093771958264441 628519930570328968698331)
          ·
            refine ⟨942779895855493453047497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628519930570328968698331 942779895855493453047497)
            ·
              refine ⟨707084921891620089785623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942779895855493453047497 707084921891620089785623)
              ·
                refine ⟨1060627382837430134678435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707084921891620089785623 1060627382837430134678435)
                ·
                  refine ⟨1590941074256145202017653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060627382837430134678435 1590941074256145202017653)
                  ·
                    refine ⟨149150725711513612689155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1590941074256145202017653 149150725711513612689155)
                    ·
                      rfl

theorem cell23_871410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_871410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871410 prefixEnd_871410 := by exact prefixLift 871410
  have htrace : WordTrace (prefixWord ++ tailWord_871410) baseStart_871410 baseEnd_871410 := by
    simpa [prefixWord, tailWord_871410, baseEnd_871410] using wordTrace_append hprefix tailTrace_871410
  have hstable : (prefixWord ++ tailWord_871410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871410).length < 2 ^ (prefixWord ++ tailWord_871410).sum := by decide
  have hdescent : baseEnd_871410 < baseStart_871410 := by decide
  rcases family_descends (prefixWord ++ tailWord_871410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871413 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_871413 : Nat := 118140960795 + 871413 * 2 ^ 59
def prefixEnd_871413 : Nat := 4983230072969 + 3 ^ 40 * 871413 * 2
def baseEnd_871413 : Nat := 447453717576504326329951

theorem tailTrace_871413 : CollatzResearch.WordTrace tailWord_871413 prefixEnd_871413 447453717576504326329951 := by
  unfold tailWord_871413
  simp only [CollatzResearch.WordTrace]
  refine ⟨31783043192027001336906893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21188695461351334224604595 31783043192027001336906893)
  ·
    refine ⟨11918641197010125501340085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31783043192027001336906893 11918641197010125501340085)
    ·
      refine ⟨1117372612219699265750633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11918641197010125501340085 1117372612219699265750633)
      ·
        refine ⟨838029459164774449312975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1117372612219699265750633 838029459164774449312975)
        ·
          refine ⟨1257044188747161673969463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838029459164774449312975 1257044188747161673969463)
          ·
            refine ⟨1885566283120742510954195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257044188747161673969463 1885566283120742510954195)
            ·
              refine ⟨2828349424681113766431293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885566283120742510954195 2828349424681113766431293)
              ·
                refine ⟨1060631034255417662411735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2828349424681113766431293 1060631034255417662411735)
                ·
                  refine ⟨1590946551383126493617603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060631034255417662411735 1590946551383126493617603)
                  ·
                    refine ⟨2386419827074689740426405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1590946551383126493617603 2386419827074689740426405)
                    ·
                      refine ⟨447453717576504326329951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2386419827074689740426405 447453717576504326329951)
                      ·
                        rfl

theorem cell23_871413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_871413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871413 prefixEnd_871413 := by exact prefixLift 871413
  have htrace : WordTrace (prefixWord ++ tailWord_871413) baseStart_871413 baseEnd_871413 := by
    simpa [prefixWord, tailWord_871413, baseEnd_871413] using wordTrace_append hprefix tailTrace_871413
  have hstable : (prefixWord ++ tailWord_871413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871413).length < 2 ^ (prefixWord ++ tailWord_871413).sum := by decide
  have hdescent : baseEnd_871413 < baseStart_871413 := by decide
  rcases family_descends (prefixWord ++ tailWord_871413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871429 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_871429 : Nat := 118140960795 + 871429 * 2 ^ 59
def prefixEnd_871429 : Nat := 4983230072969 + 3 ^ 40 * 871429 * 2
def baseEnd_871429 : Nat := 447461933266976263729877

theorem tailTrace_871429 : CollatzResearch.WordTrace tailWord_871429 prefixEnd_871429 447461933266976263729877 := by
  unfold tailWord_871429
  simp only [CollatzResearch.WordTrace]
  refine ⟨31783626759969036069489341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21189084506646024046326227 31783626759969036069489341)
  ·
    refine ⟨11918860034988388526058503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31783626759969036069489341 11918860034988388526058503)
    ·
      refine ⟨17878290052482582789087755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11918860034988388526058503 17878290052482582789087755)
      ·
        refine ⟨26817435078723874183631633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17878290052482582789087755 26817435078723874183631633)
        ·
          refine ⟨20113076309042905637723725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26817435078723874183631633 20113076309042905637723725)
          ·
            refine ⟨7542403615891089614146397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20113076309042905637723725 7542403615891089614146397)
            ·
              refine ⟨2828401355959158605304899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7542403615891089614146397 2828401355959158605304899)
              ·
                refine ⟨4242602033938737907957349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828401355959158605304899 4242602033938737907957349)
                ·
                  refine ⟨795487881363513357742003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4242602033938737907957349 795487881363513357742003)
                  ·
                    refine ⟨1193231822045270036613005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 795487881363513357742003 1193231822045270036613005)
                    ·
                      refine ⟨447461933266976263729877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1193231822045270036613005 447461933266976263729877)
                      ·
                        rfl

theorem cell23_871429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_871429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871429 prefixEnd_871429 := by exact prefixLift 871429
  have htrace : WordTrace (prefixWord ++ tailWord_871429) baseStart_871429 baseEnd_871429 := by
    simpa [prefixWord, tailWord_871429, baseEnd_871429] using wordTrace_append hprefix tailTrace_871429
  have hstable : (prefixWord ++ tailWord_871429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871429).length < 2 ^ (prefixWord ++ tailWord_871429).sum := by decide
  have hdescent : baseEnd_871429 < baseStart_871429 := by decide
  rcases family_descends (prefixWord ++ tailWord_871429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871472 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_871472 : Nat := 118140960795 + 871472 * 2 ^ 59
def prefixEnd_871472 : Nat := 4983230072969 + 3 ^ 40 * 871472 * 2
def baseEnd_871472 : Nat := 447484012935119595492179

theorem tailTrace_871472 : CollatzResearch.WordTrace tailWord_871472 prefixEnd_871472 447484012935119595492179 := by
  unfold tailWord_871472
  simp only [CollatzResearch.WordTrace]
  refine ⟨15892597549406627206652335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21190130065875502942203113 15892597549406627206652335)
  ·
    refine ⟨23838896324109940809978503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15892597549406627206652335 23838896324109940809978503)
    ·
      refine ⟨35758344486164911214967755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23838896324109940809978503 35758344486164911214967755)
      ·
        refine ⟨53637516729247366822451633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35758344486164911214967755 53637516729247366822451633)
        ·
          refine ⟨40228137546935525116838725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53637516729247366822451633 40228137546935525116838725)
          ·
            refine ⟨7542775790050410959407261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40228137546935525116838725 7542775790050410959407261)
            ·
              refine ⟨2828540921268904109777723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7542775790050410959407261 2828540921268904109777723)
              ·
                refine ⟨4242811381903356164666585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828540921268904109777723 4242811381903356164666585)
                ·
                  refine ⟨3182108536427517123499939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242811381903356164666585 3182108536427517123499939)
                  ·
                    refine ⟨4773162804641275685249909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3182108536427517123499939 4773162804641275685249909)
                    ·
                      refine ⟨447484012935119595492179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4773162804641275685249909 447484012935119595492179)
                      ·
                        rfl

theorem cell23_871472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_871472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871472 prefixEnd_871472 := by exact prefixLift 871472
  have htrace : WordTrace (prefixWord ++ tailWord_871472) baseStart_871472 baseEnd_871472 := by
    simpa [prefixWord, tailWord_871472, baseEnd_871472] using wordTrace_append hprefix tailTrace_871472
  have hstable : (prefixWord ++ tailWord_871472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871472).length < 2 ^ (prefixWord ++ tailWord_871472).sum := by decide
  have hdescent : baseEnd_871472 < baseStart_871472 := by decide
  rcases family_descends (prefixWord ++ tailWord_871472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871482 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_871482 : Nat := 118140960795 + 871482 * 2 ^ 59
def prefixEnd_871482 : Nat := 4983230072969 + 3 ^ 40 * 871482 * 2
def baseEnd_871482 : Nat := 447489147741664556367133

theorem tailTrace_871482 : CollatzResearch.WordTrace tailWord_871482 prefixEnd_871482 447489147741664556367133 := by
  unfold tailWord_871482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7946389957194256530292175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21190373219184684080779133 7946389957194256530292175)
  ·
    refine ⟨11919584935791384795438263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7946389957194256530292175 11919584935791384795438263)
    ·
      refine ⟨17879377403687077193157395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11919584935791384795438263 17879377403687077193157395)
      ·
        refine ⟨26819066105530615789736093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17879377403687077193157395 26819066105530615789736093)
        ·
          refine ⟨10057149789573980921151035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26819066105530615789736093 10057149789573980921151035)
          ·
            refine ⟨15085724684360971381726553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10057149789573980921151035 15085724684360971381726553)
            ·
              refine ⟨11314293513270728536294915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15085724684360971381726553 11314293513270728536294915)
              ·
                refine ⟨16971440269906092804442373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314293513270728536294915 16971440269906092804442373)
                ·
                  refine ⟨3182145050607392400832945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16971440269906092804442373 3182145050607392400832945)
                  ·
                    refine ⟨2386608787955544300624709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3182145050607392400832945 2386608787955544300624709)
                    ·
                      refine ⟨447489147741664556367133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2386608787955544300624709 447489147741664556367133)
                      ·
                        rfl

theorem cell23_871482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_871482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871482 prefixEnd_871482 := by exact prefixLift 871482
  have htrace : WordTrace (prefixWord ++ tailWord_871482) baseStart_871482 baseEnd_871482 := by
    simpa [prefixWord, tailWord_871482, baseEnd_871482] using wordTrace_append hprefix tailTrace_871482
  have hstable : (prefixWord ++ tailWord_871482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871482).length < 2 ^ (prefixWord ++ tailWord_871482).sum := by decide
  have hdescent : baseEnd_871482 < baseStart_871482 := by decide
  rcases family_descends (prefixWord ++ tailWord_871482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871532 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_871532 : Nat := 118140960795 + 871532 * 2 ^ 59
def prefixEnd_871532 : Nat := 4983230072969 + 3 ^ 40 * 871532 * 2
def baseEnd_871532 : Nat := 447514821774389360741903

theorem tailTrace_871532 : CollatzResearch.WordTrace tailWord_871532 prefixEnd_871532 447514821774389360741903 := by
  unfold tailWord_871532
  simp only [CollatzResearch.WordTrace]
  refine ⟨15893691739297942330244425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21191588985730589773659233 15893691739297942330244425)
  ·
    refine ⟨11920268804473456747683319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15893691739297942330244425 11920268804473456747683319)
    ·
      refine ⟨17880403206710185121524979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11920268804473456747683319 17880403206710185121524979)
      ·
        refine ⟨26820604810065277682287469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17880403206710185121524979 26820604810065277682287469)
        ·
          refine ⟨10057726803774479130857801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26820604810065277682287469 10057726803774479130857801)
          ·
            refine ⟨7543295102830859348143351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10057726803774479130857801 7543295102830859348143351)
            ·
              refine ⟨11314942654246289022215027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7543295102830859348143351 11314942654246289022215027)
              ·
                refine ⟨16972413981369433533322541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314942654246289022215027 16972413981369433533322541)
                ·
                  refine ⟨6364655243013537574995953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16972413981369433533322541 6364655243013537574995953)
                  ·
                    refine ⟨4773491432260153181246965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6364655243013537574995953 4773491432260153181246965)
                    ·
                      refine ⟨447514821774389360741903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4773491432260153181246965 447514821774389360741903)
                      ·
                        rfl

theorem cell23_871532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_871532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871532 prefixEnd_871532 := by exact prefixLift 871532
  have htrace : WordTrace (prefixWord ++ tailWord_871532) baseStart_871532 baseEnd_871532 := by
    simpa [prefixWord, tailWord_871532, baseEnd_871532] using wordTrace_append hprefix tailTrace_871532
  have hstable : (prefixWord ++ tailWord_871532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871532).length < 2 ^ (prefixWord ++ tailWord_871532).sum := by decide
  have hdescent : baseEnd_871532 < baseStart_871532 := by decide
  rcases family_descends (prefixWord ++ tailWord_871532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871550 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_871550 : Nat := 118140960795 + 871550 * 2 ^ 59
def prefixEnd_871550 : Nat := 4983230072969 + 3 ^ 40 * 871550 * 2
def baseEnd_871550 : Nat := 447524064426170290316821

theorem tailTrace_871550 : CollatzResearch.WordTrace tailWord_871550 prefixEnd_871550 447524064426170290316821 := by
  unfold tailWord_871550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973504999066334216830513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21192026661687115823096069 3973504999066334216830513)
  ·
    refine ⟨2980128749299750662622885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3973504999066334216830513 2980128749299750662622885)
    ·
      refine ⟨558774140493703249241791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2980128749299750662622885 558774140493703249241791)
      ·
        refine ⟨838161210740554873862687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558774140493703249241791 838161210740554873862687)
        ·
          refine ⟨1257241816110832310794031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838161210740554873862687 1257241816110832310794031)
          ·
            refine ⟨1885862724166248466191047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257241816110832310794031 1885862724166248466191047)
            ·
              refine ⟨2828794086249372699286571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885862724166248466191047 2828794086249372699286571)
              ·
                refine ⟨4243191129374059048929857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828794086249372699286571 4243191129374059048929857)
                ·
                  refine ⟨3182393347030544286697393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4243191129374059048929857 3182393347030544286697393)
                  ·
                    refine ⟨2386795010272908215023045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3182393347030544286697393 2386795010272908215023045)
                    ·
                      refine ⟨447524064426170290316821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2386795010272908215023045 447524064426170290316821)
                      ·
                        rfl

theorem cell23_871550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_871550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871550 prefixEnd_871550 := by exact prefixLift 871550
  have htrace : WordTrace (prefixWord ++ tailWord_871550) baseStart_871550 baseEnd_871550 := by
    simpa [prefixWord, tailWord_871550, baseEnd_871550] using wordTrace_append hprefix tailTrace_871550
  have hstable : (prefixWord ++ tailWord_871550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871550).length < 2 ^ (prefixWord ++ tailWord_871550).sum := by decide
  have hdescent : baseEnd_871550 < baseStart_871550 := by decide
  rcases family_descends (prefixWord ++ tailWord_871550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871576 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_871576 : Nat := 118140960795 + 871576 * 2 ^ 59
def prefixEnd_871576 : Nat := 4983230072969 + 3 ^ 40 * 871576 * 2
def baseEnd_871576 : Nat := 447537414923187188591701

theorem tailTrace_871576 : CollatzResearch.WordTrace tailWord_871576 prefixEnd_871576 447537414923187188591701 := by
  unfold tailWord_871576
  simp only [CollatzResearch.WordTrace]
  refine ⟨15894494145218240087545291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21192658860290986783393721 15894494145218240087545291)
  ·
    refine ⟨23841741217827360131317937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15894494145218240087545291 23841741217827360131317937)
    ·
      refine ⟨17881305913370520098488453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23841741217827360131317937 17881305913370520098488453)
      ·
        refine ⟨3352744858756972518466585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17881305913370520098488453 3352744858756972518466585)
        ·
          refine ⟨2514558644067729388849939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3352744858756972518466585 2514558644067729388849939)
          ·
            refine ⟨3771837966101594083274909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514558644067729388849939 3771837966101594083274909)
            ·
              refine ⟨1414439237288097781228091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3771837966101594083274909 1414439237288097781228091)
              ·
                refine ⟨2121658855932146671842137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414439237288097781228091 2121658855932146671842137)
                ·
                  refine ⟨1591244141949110003881603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2121658855932146671842137 1591244141949110003881603)
                  ·
                    refine ⟨2386866212923665005822405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591244141949110003881603 2386866212923665005822405)
                    ·
                      refine ⟨447537414923187188591701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2386866212923665005822405 447537414923187188591701)
                      ·
                        rfl

theorem cell23_871576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_871576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871576 prefixEnd_871576 := by exact prefixLift 871576
  have htrace : WordTrace (prefixWord ++ tailWord_871576) baseStart_871576 baseEnd_871576 := by
    simpa [prefixWord, tailWord_871576, baseEnd_871576] using wordTrace_append hprefix tailTrace_871576
  have hstable : (prefixWord ++ tailWord_871576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871576).length < 2 ^ (prefixWord ++ tailWord_871576).sum := by decide
  have hdescent : baseEnd_871576 < baseStart_871576 := by decide
  rcases family_descends (prefixWord ++ tailWord_871576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871599 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 6]
def baseStart_871599 : Nat := 118140960795 + 871599 * 2 ^ 59
def prefixEnd_871599 : Nat := 4983230072969 + 3 ^ 40 * 871599 * 2
def baseEnd_871599 : Nat := 49727691664248955400455

theorem tailTrace_871599 : CollatzResearch.WordTrace tailWord_871599 prefixEnd_871599 49727691664248955400455 := by
  unfold tailWord_871599
  simp only [CollatzResearch.WordTrace]
  refine ⟨31789827169353155103177851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21193218112902103402118567 31789827169353155103177851)
  ·
    refine ⟨47684740754029732654766777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31789827169353155103177851 47684740754029732654766777)
    ·
      refine ⟨35763555565522299491075083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47684740754029732654766777 35763555565522299491075083)
      ·
        refine ⟨53645333348283449236612625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35763555565522299491075083 53645333348283449236612625)
        ·
          refine ⟨40234000011212586927459469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53645333348283449236612625 40234000011212586927459469)
          ·
            refine ⟨15087750004204720097797301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40234000011212586927459469 15087750004204720097797301)
            ·
              refine ⟨1414476562894192509168497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15087750004204720097797301 1414476562894192509168497)
              ·
                refine ⟨1060857422170644381876373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414476562894192509168497 1060857422170644381876373)
                ·
                  refine ⟨49727691664248955400455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1060857422170644381876373 49727691664248955400455)
                  ·
                    rfl

theorem cell23_871599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 6].length) (baseStart_871599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871599 prefixEnd_871599 := by exact prefixLift 871599
  have htrace : WordTrace (prefixWord ++ tailWord_871599) baseStart_871599 baseEnd_871599 := by
    simpa [prefixWord, tailWord_871599, baseEnd_871599] using wordTrace_append hprefix tailTrace_871599
  have hstable : (prefixWord ++ tailWord_871599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871599).length < 2 ^ (prefixWord ++ tailWord_871599).sum := by decide
  have hdescent : baseEnd_871599 < baseStart_871599 := by decide
  rcases family_descends (prefixWord ++ tailWord_871599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871679 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_871679 : Nat := 118140960795 + 871679 * 2 ^ 59
def prefixEnd_871679 : Nat := 4983230072969 + 3 ^ 40 * 871679 * 2
def baseEnd_871679 : Nat := 447590303430600285603727

theorem tailTrace_871679 : CollatzResearch.WordTrace tailWord_871679 prefixEnd_871679 447590303430600285603727 := by
  unfold tailWord_871679
  simp only [CollatzResearch.WordTrace]
  refine ⟨31792745009063328766090091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21195163339375552510726727 31792745009063328766090091)
  ·
    refine ⟨47689117513594993149135137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31792745009063328766090091 47689117513594993149135137)
    ·
      refine ⟨35766838135196244861851353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47689117513594993149135137 35766838135196244861851353)
      ·
        refine ⟨26825128601397183646388515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35766838135196244861851353 26825128601397183646388515)
        ·
          refine ⟨40237692902095775469582773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26825128601397183646388515 40237692902095775469582773)
          ·
            refine ⟨3772283709571478950273385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40237692902095775469582773 3772283709571478950273385)
            ·
              refine ⟨2829212782178609212705039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3772283709571478950273385 2829212782178609212705039)
              ·
                refine ⟨4243819173267913819057559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829212782178609212705039 4243819173267913819057559)
                ·
                  refine ⟨6365728759901870728586339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243819173267913819057559 6365728759901870728586339)
                  ·
                    refine ⟨9548593139852806092879509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6365728759901870728586339 9548593139852806092879509)
                    ·
                      refine ⟨447590303430600285603727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9548593139852806092879509 447590303430600285603727)
                      ·
                        rfl

theorem cell23_871679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_871679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871679 prefixEnd_871679 := by exact prefixLift 871679
  have htrace : WordTrace (prefixWord ++ tailWord_871679) baseStart_871679 baseEnd_871679 := by
    simpa [prefixWord, tailWord_871679, baseEnd_871679] using wordTrace_append hprefix tailTrace_871679
  have hstable : (prefixWord ++ tailWord_871679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871679).length < 2 ^ (prefixWord ++ tailWord_871679).sum := by decide
  have hdescent : baseEnd_871679 < baseStart_871679 := by decide
  rcases family_descends (prefixWord ++ tailWord_871679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871683 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 4]
def baseStart_871683 : Nat := 118140960795 + 871683 * 2 ^ 59
def prefixEnd_871683 : Nat := 4983230072969 + 3 ^ 40 * 871683 * 2
def baseEnd_871683 : Nat := 447592357353218269953709

theorem tailTrace_871683 : CollatzResearch.WordTrace tailWord_871683 prefixEnd_871683 447592357353218269953709 := by
  unfold tailWord_871683
  simp only [CollatzResearch.WordTrace]
  refine ⟨31792890901048837449235703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21195260600699224966157135 31792890901048837449235703)
  ·
    refine ⟨47689336351573256173853555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31792890901048837449235703 47689336351573256173853555)
    ·
      refine ⟨71534004527359884260780333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47689336351573256173853555 71534004527359884260780333)
      ·
        refine ⟨26825251697759956597792625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71534004527359884260780333 26825251697759956597792625)
        ·
          refine ⟨20118938773319967448344469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26825251697759956597792625 20118938773319967448344469)
          ·
            refine ⟨943075254999373474141147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20118938773319967448344469 943075254999373474141147)
            ·
              refine ⟨1414612882499060211211721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943075254999373474141147 1414612882499060211211721)
              ·
                refine ⟨1060959661874295158408791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414612882499060211211721 1060959661874295158408791)
                ·
                  refine ⟨1591439492811442737613187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060959661874295158408791 1591439492811442737613187)
                  ·
                    refine ⟨2387159239217164106419781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591439492811442737613187 2387159239217164106419781)
                    ·
                      refine ⟨447592357353218269953709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2387159239217164106419781 447592357353218269953709)
                      ·
                        rfl

theorem cell23_871683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_871683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871683 prefixEnd_871683 := by exact prefixLift 871683
  have htrace : WordTrace (prefixWord ++ tailWord_871683) baseStart_871683 baseEnd_871683 := by
    simpa [prefixWord, tailWord_871683, baseEnd_871683] using wordTrace_append hprefix tailTrace_871683
  have hstable : (prefixWord ++ tailWord_871683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871683).length < 2 ^ (prefixWord ++ tailWord_871683).sum := by decide
  have hdescent : baseEnd_871683 < baseStart_871683 := by decide
  rcases family_descends (prefixWord ++ tailWord_871683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871716 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_871716 : Nat := 118140960795 + 871716 * 2 ^ 59
def prefixEnd_871716 : Nat := 4983230072969 + 3 ^ 40 * 871716 * 2
def baseEnd_871716 : Nat := 447609302214816640841057

theorem tailTrace_871716 : CollatzResearch.WordTrace tailWord_871716 prefixEnd_871716 447609302214816640841057 := by
  unfold tailWord_871716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15897047254964642042593501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21196063006619522723458001 15897047254964642042593501)
  ·
    refine ⟨5961392720611740765972563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15897047254964642042593501 5961392720611740765972563)
    ·
      refine ⟨8942089080917611148958845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5961392720611740765972563 8942089080917611148958845)
      ·
        refine ⟨3353283405344104180859567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8942089080917611148958845 3353283405344104180859567)
        ·
          refine ⟨5029925108016156271289351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353283405344104180859567 5029925108016156271289351)
          ·
            refine ⟨7544887662024234406934027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029925108016156271289351 7544887662024234406934027)
            ·
              refine ⟨11317331493036351610401041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544887662024234406934027 11317331493036351610401041)
              ·
                refine ⟨8487998619777263707800781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11317331493036351610401041 8487998619777263707800781)
                ·
                  refine ⟨3182999482416473890425293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8487998619777263707800781 3182999482416473890425293)
                  ·
                    refine ⟨1193624805906177708909485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182999482416473890425293 1193624805906177708909485)
                    ·
                      refine ⟨447609302214816640841057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1193624805906177708909485 447609302214816640841057)
                      ·
                        rfl

theorem cell23_871716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_871716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871716 prefixEnd_871716 := by exact prefixLift 871716
  have htrace : WordTrace (prefixWord ++ tailWord_871716) baseStart_871716 baseEnd_871716 := by
    simpa [prefixWord, tailWord_871716, baseEnd_871716] using wordTrace_append hprefix tailTrace_871716
  have hstable : (prefixWord ++ tailWord_871716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871716).length < 2 ^ (prefixWord ++ tailWord_871716).sum := by decide
  have hdescent : baseEnd_871716 < baseStart_871716 := by decide
  rcases family_descends (prefixWord ++ tailWord_871716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871717 : List Nat := [1, 3, 1, 2, 4, 2, 1, 4, 1, 2, 2]
def baseStart_871717 : Nat := 118140960795 + 871717 * 2 ^ 59
def prefixEnd_871717 : Nat := 4983230072969 + 3 ^ 40 * 871717 * 2
def baseEnd_871717 : Nat := 447609815695471136928553

theorem tailTrace_871717 : CollatzResearch.WordTrace tailWord_871717 prefixEnd_871717 447609815695471136928553 := by
  unfold tailWord_871717
  simp only [CollatzResearch.WordTrace]
  refine ⟨31794130982925661255973405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21196087321950440837315603 31794130982925661255973405)
  ·
    refine ⟨11922799118597122970990027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31794130982925661255973405 11922799118597122970990027)
    ·
      refine ⟨17884198677895684456485041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11922799118597122970990027 17884198677895684456485041)
      ·
        refine ⟨13413149008421763342363781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17884198677895684456485041 13413149008421763342363781)
        ·
          refine ⟨2514965439079080626693209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13413149008421763342363781 2514965439079080626693209)
          ·
            refine ⟨1886224079309310470019907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514965439079080626693209 1886224079309310470019907)
            ·
              refine ⟨2829336118963965705029861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886224079309310470019907 2829336118963965705029861)
              ·
                refine ⟨530500522305743569693099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2829336118963965705029861 530500522305743569693099)
                ·
                  refine ⟨795750783458615354539649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530500522305743569693099 795750783458615354539649)
                  ·
                    refine ⟨596813087593961515904737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 795750783458615354539649 596813087593961515904737)
                    ·
                      refine ⟨447609815695471136928553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 596813087593961515904737 447609815695471136928553)
                      ·
                        rfl

theorem cell23_871717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_871717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871717 prefixEnd_871717 := by exact prefixLift 871717
  have htrace : WordTrace (prefixWord ++ tailWord_871717) baseStart_871717 baseEnd_871717 := by
    simpa [prefixWord, tailWord_871717, baseEnd_871717] using wordTrace_append hprefix tailTrace_871717
  have hstable : (prefixWord ++ tailWord_871717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871717).length < 2 ^ (prefixWord ++ tailWord_871717).sum := by decide
  have hdescent : baseEnd_871717 < baseStart_871717 := by decide
  rcases family_descends (prefixWord ++ tailWord_871717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871733 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_871733 : Nat := 118140960795 + 871733 * 2 ^ 59
def prefixEnd_871733 : Nat := 4983230072969 + 3 ^ 40 * 871733 * 2
def baseEnd_871733 : Nat := 447618031385943074328479

theorem tailTrace_871733 : CollatzResearch.WordTrace tailWord_871733 prefixEnd_871733 447618031385943074328479 := by
  unfold tailWord_871733
  simp only [CollatzResearch.WordTrace]
  refine ⟨31794714550867695988555853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21196476367245130659037235 31794714550867695988555853)
  ·
    refine ⟨11923017956575385995708445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31794714550867695988555853 11923017956575385995708445)
    ·
      refine ⟨4471131733715769748390667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11923017956575385995708445 4471131733715769748390667)
      ·
        refine ⟨6706697600573654622586001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471131733715769748390667 6706697600573654622586001)
        ·
          refine ⟨5030023200430240966939501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6706697600573654622586001 5030023200430240966939501)
          ·
            refine ⟨1886258700161340362602313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5030023200430240966939501 1886258700161340362602313)
            ·
              refine ⟨1414694025121005271951735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1886258700161340362602313 1414694025121005271951735)
              ·
                refine ⟨2122041037681507907927603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414694025121005271951735 2122041037681507907927603)
                ·
                  refine ⟨3183061556522261861891405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122041037681507907927603 3183061556522261861891405)
                  ·
                    refine ⟨1193648083695848198209277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183061556522261861891405 1193648083695848198209277)
                    ·
                      refine ⟨447618031385943074328479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1193648083695848198209277 447618031385943074328479)
                      ·
                        rfl

theorem cell23_871733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_871733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871733 prefixEnd_871733 := by exact prefixLift 871733
  have htrace : WordTrace (prefixWord ++ tailWord_871733) baseStart_871733 baseEnd_871733 := by
    simpa [prefixWord, tailWord_871733, baseEnd_871733] using wordTrace_append hprefix tailTrace_871733
  have hstable : (prefixWord ++ tailWord_871733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871733).length < 2 ^ (prefixWord ++ tailWord_871733).sum := by decide
  have hdescent : baseEnd_871733 < baseStart_871733 := by decide
  rcases family_descends (prefixWord ++ tailWord_871733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871734 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_871734 : Nat := 118140960795 + 871734 * 2 ^ 59
def prefixEnd_871734 : Nat := 4983230072969 + 3 ^ 40 * 871734 * 2
def baseEnd_871734 : Nat := 447618544866597570415975

theorem tailTrace_871734 : CollatzResearch.WordTrace tailWord_871734 prefixEnd_871734 447618544866597570415975 := by
  unfold tailWord_871734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987171938991504572458891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21196500682576048772894837 1987171938991504572458891)
  ·
    refine ⟨2980757908487256858688337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1987171938991504572458891 2980757908487256858688337)
    ·
      refine ⟨2235568431365442644016253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2980757908487256858688337 2235568431365442644016253)
      ·
        refine ⟨838338161762040991506095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2235568431365442644016253 838338161762040991506095)
        ·
          refine ⟨1257507242643061487259143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838338161762040991506095 1257507242643061487259143)
          ·
            refine ⟨1886260863964592230888715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257507242643061487259143 1886260863964592230888715)
            ·
              refine ⟨2829391295946888346333073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886260863964592230888715 2829391295946888346333073)
              ·
                refine ⟨2122043471960166259749805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829391295946888346333073 2122043471960166259749805)
                ·
                  refine ⟨795766301985062347406177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2122043471960166259749805 795766301985062347406177)
                  ·
                    refine ⟨596824726488796760554633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 795766301985062347406177 596824726488796760554633)
                    ·
                      refine ⟨447618544866597570415975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 596824726488796760554633 447618544866597570415975)
                      ·
                        rfl

theorem cell23_871734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_871734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871734 prefixEnd_871734 := by exact prefixLift 871734
  have htrace : WordTrace (prefixWord ++ tailWord_871734) baseStart_871734 baseEnd_871734 := by
    simpa [prefixWord, tailWord_871734, baseEnd_871734] using wordTrace_append hprefix tailTrace_871734
  have hstable : (prefixWord ++ tailWord_871734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871734).length < 2 ^ (prefixWord ++ tailWord_871734).sum := by decide
  have hdescent : baseEnd_871734 < baseStart_871734 := by decide
  rcases family_descends (prefixWord ++ tailWord_871734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871743 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 3, 3, 2]
def baseStart_871743 : Nat := 118140960795 + 871743 * 2 ^ 59
def prefixEnd_871743 : Nat := 4983230072969 + 3 ^ 40 * 871743 * 2
def baseEnd_871743 : Nat := 447623166192488035203433

theorem tailTrace_871743 : CollatzResearch.WordTrace tailWord_871743 prefixEnd_871743 447623166192488035203433 := by
  unfold tailWord_871743
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795079280831467696419883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21196719520554311797613255 31795079280831467696419883)
  ·
    refine ⟨47692618921247201544629825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31795079280831467696419883 47692618921247201544629825)
    ·
      refine ⟨35769464190935401158472369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47692618921247201544629825 35769464190935401158472369)
      ·
        refine ⟨26827098143201550868854277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35769464190935401158472369 26827098143201550868854277)
        ·
          refine ⟨5030080901850290787910177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26827098143201550868854277 5030080901850290787910177)
          ·
            refine ⟨3772560676387718090932633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030080901850290787910177 3772560676387718090932633)
            ·
              refine ⟨2829420507290788568199475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3772560676387718090932633 2829420507290788568199475)
              ·
                refine ⟨4244130760936182852299213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829420507290788568199475 4244130760936182852299213)
                ·
                  refine ⟨1591549035351068569612205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4244130760936182852299213 1591549035351068569612205)
                  ·
                    refine ⟨596830888256650713604577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1591549035351068569612205 596830888256650713604577)
                    ·
                      refine ⟨447623166192488035203433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 596830888256650713604577 447623166192488035203433)
                      ·
                        rfl

theorem cell23_871743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_871743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871743 prefixEnd_871743 := by exact prefixLift 871743
  have htrace : WordTrace (prefixWord ++ tailWord_871743) baseStart_871743 baseEnd_871743 := by
    simpa [prefixWord, tailWord_871743, baseEnd_871743] using wordTrace_append hprefix tailTrace_871743
  have hstable : (prefixWord ++ tailWord_871743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871743).length < 2 ^ (prefixWord ++ tailWord_871743).sum := by decide
  have hdescent : baseEnd_871743 < baseStart_871743 := by decide
  rcases family_descends (prefixWord ++ tailWord_871743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871759 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_871759 : Nat := 118140960795 + 871759 * 2 ^ 59
def prefixEnd_871759 : Nat := 4983230072969 + 3 ^ 40 * 871759 * 2
def baseEnd_871759 : Nat := 447631381882959972603359

theorem tailTrace_871759 : CollatzResearch.WordTrace tailWord_871759 prefixEnd_871759 447631381882959972603359 := by
  unfold tailWord_871759
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795662848773502429002331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21197108565849001619334887 31795662848773502429002331)
  ·
    refine ⟨47693494273160253643503497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31795662848773502429002331 47693494273160253643503497)
    ·
      refine ⟨35770120704870190232627623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47693494273160253643503497 35770120704870190232627623)
      ·
        refine ⟨53655181057305285348941435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35770120704870190232627623 53655181057305285348941435)
        ·
          refine ⟨80482771585957928023412153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53655181057305285348941435 80482771585957928023412153)
          ·
            refine ⟨60362078689468446017559115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80482771585957928023412153 60362078689468446017559115)
            ·
              refine ⟨90543118034202669026338673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60362078689468446017559115 90543118034202669026338673)
              ·
                refine ⟨67907338525652001769754005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90543118034202669026338673 67907338525652001769754005)
                ·
                  refine ⟨3183156493389937582957219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67907338525652001769754005 3183156493389937582957219)
                  ·
                    refine ⟨4774734740084906374435829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183156493389937582957219 4774734740084906374435829)
                    ·
                      refine ⟨447631381882959972603359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4774734740084906374435829 447631381882959972603359)
                      ·
                        rfl

theorem cell23_871759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_871759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871759 prefixEnd_871759 := by exact prefixLift 871759
  have htrace : WordTrace (prefixWord ++ tailWord_871759) baseStart_871759 baseEnd_871759 := by
    simpa [prefixWord, tailWord_871759, baseEnd_871759] using wordTrace_append hprefix tailTrace_871759
  have hstable : (prefixWord ++ tailWord_871759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871759).length < 2 ^ (prefixWord ++ tailWord_871759).sum := by decide
  have hdescent : baseEnd_871759 < baseStart_871759 := by decide
  rcases family_descends (prefixWord ++ tailWord_871759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871810 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_871810 : Nat := 118140960795 + 871810 * 2 ^ 59
def prefixEnd_871810 : Nat := 4983230072969 + 3 ^ 40 * 871810 * 2
def baseEnd_871810 : Nat := 447657569396339273065625

theorem tailTrace_871810 : CollatzResearch.WordTrace tailWord_871810 prefixEnd_871810 447657569396339273065625 := by
  unfold tailWord_871810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949380742897184534777221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21198348647725825426072589 7949380742897184534777221)
  ·
    refine ⟨1490508889293222100270729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7949380742897184534777221 1490508889293222100270729)
    ·
      refine ⟨1117881666969916575203047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1490508889293222100270729 1117881666969916575203047)
      ·
        refine ⟨1676822500454874862804571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117881666969916575203047 1676822500454874862804571)
        ·
          refine ⟨2515233750682312294206857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676822500454874862804571 2515233750682312294206857)
          ·
            refine ⟨1886425313011734220655143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515233750682312294206857 1886425313011734220655143)
            ·
              refine ⟨2829637969517601330982715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886425313011734220655143 2829637969517601330982715)
              ·
                refine ⟨4244456954276401996474073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829637969517601330982715 4244456954276401996474073)
                ·
                  refine ⟨3183342715707301497355555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4244456954276401996474073 3183342715707301497355555)
                  ·
                    refine ⟨4775014073560952246033333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183342715707301497355555 4775014073560952246033333)
                    ·
                      refine ⟨447657569396339273065625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4775014073560952246033333 447657569396339273065625)
                      ·
                        rfl

theorem cell23_871810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_871810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871810 prefixEnd_871810 := by exact prefixLift 871810
  have htrace : WordTrace (prefixWord ++ tailWord_871810) baseStart_871810 baseEnd_871810 := by
    simpa [prefixWord, tailWord_871810, baseEnd_871810] using wordTrace_append hprefix tailTrace_871810
  have hstable : (prefixWord ++ tailWord_871810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871810).length < 2 ^ (prefixWord ++ tailWord_871810).sum := by decide
  have hdescent : baseEnd_871810 < baseStart_871810 := by decide
  rcases family_descends (prefixWord ++ tailWord_871810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871813 : List Nat := [1, 3, 1, 1, 3, 1, 5, 3, 5]
def baseStart_871813 : Nat := 118140960795 + 871813 * 2 ^ 59
def prefixEnd_871813 : Nat := 4983230072969 + 3 ^ 40 * 871813 * 2
def baseEnd_871813 : Nat := 49739901093144751258679

theorem tailTrace_871813 : CollatzResearch.WordTrace tailWord_871813 prefixEnd_871813 49739901093144751258679 := by
  unfold tailWord_871813
  simp only [CollatzResearch.WordTrace]
  refine ⟨31797632390577869651468093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21198421593718579767645395 31797632390577869651468093)
  ·
    refine ⟨11924112146466701119300535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31797632390577869651468093 11924112146466701119300535)
    ·
      refine ⟨17886168219700051678950803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11924112146466701119300535 17886168219700051678950803)
      ·
        refine ⟨26829252329550077518426205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17886168219700051678950803 26829252329550077518426205)
        ·
          refine ⟨10060969623581279069409827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26829252329550077518426205 10060969623581279069409827)
          ·
            refine ⟨15091454435371918604114741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060969623581279069409827 15091454435371918604114741)
            ·
              refine ⟨1414823853316117369135757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15091454435371918604114741 1414823853316117369135757)
              ·
                refine ⟨530558944993544013425909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1414823853316117369135757 530558944993544013425909)
                ·
                  refine ⟨49739901093144751258679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530558944993544013425909 49739901093144751258679)
                  ·
                    rfl

theorem cell23_871813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_871813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871813 prefixEnd_871813 := by exact prefixLift 871813
  have htrace : WordTrace (prefixWord ++ tailWord_871813) baseStart_871813 baseEnd_871813 := by
    simpa [prefixWord, tailWord_871813, baseEnd_871813] using wordTrace_append hprefix tailTrace_871813
  have hstable : (prefixWord ++ tailWord_871813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871813).length < 2 ^ (prefixWord ++ tailWord_871813).sum := by decide
  have hdescent : baseEnd_871813 < baseStart_871813 := by decide
  rcases family_descends (prefixWord ++ tailWord_871813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871863 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_871863 : Nat := 118140960795 + 871863 * 2 ^ 59
def prefixEnd_871863 : Nat := 4983230072969 + 3 ^ 40 * 871863 * 2
def baseEnd_871863 : Nat := 447684783871027565702881

theorem tailTrace_871863 : CollatzResearch.WordTrace tailWord_871863 prefixEnd_871863 447684783871027565702881 := by
  unfold tailWord_871863
  simp only [CollatzResearch.WordTrace]
  refine ⟨31799456040396728190788243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21199637360264485460525495 31799456040396728190788243)
  ·
    refine ⟨47699184060595092286182365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31799456040396728190788243 47699184060595092286182365)
    ·
      refine ⟨17887194022723159607318387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47699184060595092286182365 17887194022723159607318387)
      ·
        refine ⟨26830791034084739410977581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17887194022723159607318387 26830791034084739410977581)
        ·
          refine ⟨10061546637781777279116593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26830791034084739410977581 10061546637781777279116593)
          ·
            refine ⟨7546159978336332959337445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10061546637781777279116593 7546159978336332959337445)
            ·
              refine ⟨1414904995938062429875771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7546159978336332959337445 1414904995938062429875771)
              ·
                refine ⟨2122357493907093644813657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414904995938062429875771 2122357493907093644813657)
                ·
                  refine ⟨1591768120430320233610243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2122357493907093644813657 1591768120430320233610243)
                  ·
                    refine ⟨2387652180645480350415365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591768120430320233610243 2387652180645480350415365)
                    ·
                      refine ⟨447684783871027565702881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2387652180645480350415365 447684783871027565702881)
                      ·
                        rfl

theorem cell23_871863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_871863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871863 prefixEnd_871863 := by exact prefixLift 871863
  have htrace : WordTrace (prefixWord ++ tailWord_871863) baseStart_871863 baseEnd_871863 := by
    simpa [prefixWord, tailWord_871863, baseEnd_871863] using wordTrace_append hprefix tailTrace_871863
  have hstable : (prefixWord ++ tailWord_871863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871863).length < 2 ^ (prefixWord ++ tailWord_871863).sum := by decide
  have hdescent : baseEnd_871863 < baseStart_871863 := by decide
  rcases family_descends (prefixWord ++ tailWord_871863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871883 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 3]
def baseStart_871883 : Nat := 118140960795 + 871883 * 2 ^ 59
def prefixEnd_871883 : Nat := 4983230072969 + 3 ^ 40 * 871883 * 2
def baseEnd_871883 : Nat := 447695053484117487452789

theorem tailTrace_871883 : CollatzResearch.WordTrace tailWord_871883 prefixEnd_871883 447695053484117487452789 := by
  unfold tailWord_871883
  simp only [CollatzResearch.WordTrace]
  refine ⟨31800185500324271606516303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21200123666882847737677535 31800185500324271606516303)
  ·
    refine ⟨47700278250486407409774455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31800185500324271606516303 47700278250486407409774455)
    ·
      refine ⟨71550417375729611114661683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47700278250486407409774455 71550417375729611114661683)
      ·
        refine ⟨107325626063594416671992525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71550417375729611114661683 107325626063594416671992525)
        ·
          refine ⟨40247109773847906251997197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107325626063594416671992525 40247109773847906251997197)
          ·
            refine ⟨15092666165192964844498949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40247109773847906251997197 15092666165192964844498949)
            ·
              refine ⟨2829874905973680908343553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15092666165192964844498949 2829874905973680908343553)
              ·
                refine ⟨2122406179480260681257665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829874905973680908343553 2122406179480260681257665)
                ·
                  refine ⟨1591804634610195510943249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2122406179480260681257665 1591804634610195510943249)
                  ·
                    refine ⟨1193853475957646633207437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1591804634610195510943249 1193853475957646633207437)
                    ·
                      refine ⟨447695053484117487452789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1193853475957646633207437 447695053484117487452789)
                      ·
                        rfl

theorem cell23_871883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 3].length) (baseStart_871883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871883 prefixEnd_871883 := by exact prefixLift 871883
  have htrace : WordTrace (prefixWord ++ tailWord_871883) baseStart_871883 baseEnd_871883 := by
    simpa [prefixWord, tailWord_871883, baseEnd_871883] using wordTrace_append hprefix tailTrace_871883
  have hstable : (prefixWord ++ tailWord_871883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871883).length < 2 ^ (prefixWord ++ tailWord_871883).sum := by decide
  have hdescent : baseEnd_871883 < baseStart_871883 := by decide
  rcases family_descends (prefixWord ++ tailWord_871883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871886 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_871886 : Nat := 118140960795 + 871886 * 2 ^ 59
def prefixEnd_871886 : Nat := 4983230072969 + 3 ^ 40 * 871886 * 2
def baseEnd_871886 : Nat := 49744065991786775079475

theorem tailTrace_871886 : CollatzResearch.WordTrace tailWord_871886 prefixEnd_871886 49744065991786775079475 := by
  unfold tailWord_871886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975036864914175389859439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21200196612875602079250341 3975036864914175389859439)
  ·
    refine ⟨5962555297371263084789159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3975036864914175389859439 5962555297371263084789159)
    ·
      refine ⟨8943832946056894627183739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5962555297371263084789159 8943832946056894627183739)
      ·
        refine ⟨13415749419085341940775609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8943832946056894627183739 13415749419085341940775609)
        ·
          refine ⟨10061812064314006455581707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13415749419085341940775609 10061812064314006455581707)
          ·
            refine ⟨15092718096471009683372561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10061812064314006455581707 15092718096471009683372561)
            ·
              refine ⟨11319538572353257262529421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15092718096471009683372561 11319538572353257262529421)
              ·
                refine ⟨4244826964632471473448533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11319538572353257262529421 4244826964632471473448533)
                ·
                  refine ⟨49744065991786775079475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4244826964632471473448533 49744065991786775079475)
                  ·
                    rfl

theorem cell23_871886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_871886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871886 prefixEnd_871886 := by exact prefixLift 871886
  have htrace : WordTrace (prefixWord ++ tailWord_871886) baseStart_871886 baseEnd_871886 := by
    simpa [prefixWord, tailWord_871886, baseEnd_871886] using wordTrace_append hprefix tailTrace_871886
  have hstable : (prefixWord ++ tailWord_871886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871886).length < 2 ^ (prefixWord ++ tailWord_871886).sum := by decide
  have hdescent : baseEnd_871886 < baseStart_871886 := by decide
  rcases family_descends (prefixWord ++ tailWord_871886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871937 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 6]
def baseStart_871937 : Nat := 118140960795 + 871937 * 2 ^ 59
def prefixEnd_871937 : Nat := 4983230072969 + 3 ^ 40 * 871937 * 2
def baseEnd_871937 : Nat := 49746975715495586241949

theorem tailTrace_871937 : CollatzResearch.WordTrace tailWord_871937 prefixEnd_871937 49746975715495586241949 := by
  unfold tailWord_871937
  simp only [CollatzResearch.WordTrace]
  refine ⟨31802155042128638828982065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21201436694752425885988043 31802155042128638828982065)
  ·
    refine ⟨23851616281596479121736549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31802155042128638828982065 23851616281596479121736549)
    ·
      refine ⟨4472178052799339835325603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23851616281596479121736549 4472178052799339835325603)
      ·
        refine ⟨6708267079199009752988405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472178052799339835325603 6708267079199009752988405)
        ·
          refine ⟨628900038674907164342663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6708267079199009752988405 628900038674907164342663)
          ·
            refine ⟨943350058012360746513995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628900038674907164342663 943350058012360746513995)
            ·
              refine ⟨1415025087018541119770993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943350058012360746513995 1415025087018541119770993)
              ·
                refine ⟨1061268815263905839828245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415025087018541119770993 1061268815263905839828245)
                ·
                  refine ⟨49746975715495586241949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1061268815263905839828245 49746975715495586241949)
                  ·
                    rfl

theorem cell23_871937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 6].length) (baseStart_871937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871937 prefixEnd_871937 := by exact prefixLift 871937
  have htrace : WordTrace (prefixWord ++ tailWord_871937) baseStart_871937 baseEnd_871937 := by
    simpa [prefixWord, tailWord_871937, baseEnd_871937] using wordTrace_append hprefix tailTrace_871937
  have hstable : (prefixWord ++ tailWord_871937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871937).length < 2 ^ (prefixWord ++ tailWord_871937).sum := by decide
  have hdescent : baseEnd_871937 < baseStart_871937 := by decide
  rcases family_descends (prefixWord ++ tailWord_871937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871947 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 3]
def baseStart_871947 : Nat := 118140960795 + 871947 * 2 ^ 59
def prefixEnd_871947 : Nat := 4983230072969 + 3 ^ 40 * 871947 * 2
def baseEnd_871947 : Nat := 447727916246005237052495

theorem tailTrace_871947 : CollatzResearch.WordTrace tailWord_871947 prefixEnd_871947 447727916246005237052495 := by
  unfold tailWord_871947
  simp only [CollatzResearch.WordTrace]
  refine ⟨31802519772092410536846095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21201679848061607024564063 31802519772092410536846095)
  ·
    refine ⟨47703779658138615805269143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31802519772092410536846095 47703779658138615805269143)
    ·
      refine ⟨71555669487207923707903715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47703779658138615805269143 71555669487207923707903715)
      ·
        refine ⟨107333504230811885561855573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71555669487207923707903715 107333504230811885561855573)
        ·
          refine ⟨1257814502704826783927995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 107333504230811885561855573 1257814502704826783927995)
          ·
            refine ⟨1886721754057240175891993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257814502704826783927995 1886721754057240175891993)
            ·
              refine ⟨1415041315542930131918995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1886721754057240175891993 1415041315542930131918995)
              ·
                refine ⟨2122561973314395197878493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415041315542930131918995 2122561973314395197878493)
                ·
                  refine ⟨795960739992898199204435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2122561973314395197878493 795960739992898199204435)
                  ·
                    refine ⟨1193941109989347298806653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 795960739992898199204435 1193941109989347298806653)
                    ·
                      refine ⟨447727916246005237052495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1193941109989347298806653 447727916246005237052495)
                      ·
                        rfl

theorem cell23_871947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 3].length) (baseStart_871947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871947 prefixEnd_871947 := by exact prefixLift 871947
  have htrace : WordTrace (prefixWord ++ tailWord_871947) baseStart_871947 baseEnd_871947 := by
    simpa [prefixWord, tailWord_871947, baseEnd_871947] using wordTrace_append hprefix tailTrace_871947
  have hstable : (prefixWord ++ tailWord_871947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871947).length < 2 ^ (prefixWord ++ tailWord_871947).sum := by decide
  have hdescent : baseEnd_871947 < baseStart_871947 := by decide
  rcases family_descends (prefixWord ++ tailWord_871947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871970 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_871970 : Nat := 118140960795 + 871970 * 2 ^ 59
def prefixEnd_871970 : Nat := 4983230072969 + 3 ^ 40 * 871970 * 2
def baseEnd_871970 : Nat := 447739726301058647064889

theorem tailTrace_871970 : CollatzResearch.WordTrace tailWord_871970 prefixEnd_871970 447739726301058647064889 := by
  unfold tailWord_871970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950839662752271366233341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21202239100672723643288909 7950839662752271366233341)
  ·
    refine ⟨2981564873532101762337503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7950839662752271366233341 2981564873532101762337503)
    ·
      refine ⟨4472347310298152643506255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981564873532101762337503 4472347310298152643506255)
      ·
        refine ⟨6708520965447228965259383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472347310298152643506255 6708520965447228965259383)
        ·
          refine ⟨10062781448170843447889075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708520965447228965259383 10062781448170843447889075)
          ·
            refine ⟨15094172172256265171833613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10062781448170843447889075 15094172172256265171833613)
            ·
              refine ⟨5660314564596099439437605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15094172172256265171833613 5660314564596099439437605)
              ·
                refine ⟨1061308980861768644894551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5660314564596099439437605 1061308980861768644894551)
                ·
                  refine ⟨1591963471292652967341827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1061308980861768644894551 1591963471292652967341827)
                  ·
                    refine ⟨2387945206938979451012741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591963471292652967341827 2387945206938979451012741)
                    ·
                      refine ⟨447739726301058647064889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2387945206938979451012741 447739726301058647064889)
                      ·
                        rfl

theorem cell23_871970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_871970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871970 prefixEnd_871970 := by exact prefixLift 871970
  have htrace : WordTrace (prefixWord ++ tailWord_871970) baseStart_871970 baseEnd_871970 := by
    simpa [prefixWord, tailWord_871970, baseEnd_871970] using wordTrace_append hprefix tailTrace_871970
  have hstable : (prefixWord ++ tailWord_871970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871970).length < 2 ^ (prefixWord ++ tailWord_871970).sum := by decide
  have hdescent : baseEnd_871970 < baseStart_871970 := by decide
  rcases family_descends (prefixWord ++ tailWord_871970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871993 : List Nat := [1, 2, 1, 5, 1, 4, 9]
def baseStart_871993 : Nat := 118140960795 + 871993 * 2 ^ 59
def prefixEnd_871993 : Nat := 4983230072969 + 3 ^ 40 * 871993 * 2
def baseEnd_871993 : Nat := 5527796745137185889843

theorem tailTrace_871993 : CollatzResearch.WordTrace tailWord_871993 prefixEnd_871993 5527796745137185889843 := by
  unfold tailWord_871993
  simp only [CollatzResearch.WordTrace]
  refine ⟨31804197529925760393020633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21202798353283840262013755 31804197529925760393020633)
  ·
    refine ⟨23853148147444320294765475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31804197529925760393020633 23853148147444320294765475)
    ·
      refine ⟨35779722221166480442148213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23853148147444320294765475 35779722221166480442148213)
      ·
        refine ⟨3354348958234357541451395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35779722221166480442148213 3354348958234357541451395)
        ·
          refine ⟨5031523437351536312177093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354348958234357541451395 5031523437351536312177093)
          ·
            refine ⟨943410644503413058533205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5031523437351536312177093 943410644503413058533205)
            ·
              refine ⟨5527796745137185889843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 943410644503413058533205 5527796745137185889843)
              ·
                rfl

theorem cell23_871993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 9].length) (baseStart_871993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_871993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_871993 prefixEnd_871993 := by exact prefixLift 871993
  have htrace : WordTrace (prefixWord ++ tailWord_871993) baseStart_871993 baseEnd_871993 := by
    simpa [prefixWord, tailWord_871993, baseEnd_871993] using wordTrace_append hprefix tailTrace_871993
  have hstable : (prefixWord ++ tailWord_871993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871993).length < 2 ^ (prefixWord ++ tailWord_871993).sum := by decide
  have hdescent : baseEnd_871993 < baseStart_871993 := by decide
  rcases family_descends (prefixWord ++ tailWord_871993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872020 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_872020 : Nat := 118140960795 + 872020 * 2 ^ 59
def prefixEnd_872020 : Nat := 4983230072969 + 3 ^ 40 * 872020 * 2
def baseEnd_872020 : Nat := 447765400333783451439659

theorem tailTrace_872020 : CollatzResearch.WordTrace tailWord_872020 prefixEnd_872020 447765400333783451439659 := by
  unfold tailWord_872020
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902591150413972002126757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21203454867218629336169009 15902591150413972002126757)
  ·
    refine ⟨2981735840702619750398767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15902591150413972002126757 2981735840702619750398767)
    ·
      refine ⟨4472603761053929625598151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981735840702619750398767 4472603761053929625598151)
      ·
        refine ⟨6708905641580894438397227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472603761053929625598151 6708905641580894438397227)
        ·
          refine ⟨10063358462371341657595841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708905641580894438397227 10063358462371341657595841)
          ·
            refine ⟨7547518846778506243196881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10063358462371341657595841 7547518846778506243196881)
            ·
              refine ⟨5660639135083879682397661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7547518846778506243196881 5660639135083879682397661)
              ·
                refine ⟨2122739675656454880899123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5660639135083879682397661 2122739675656454880899123)
                ·
                  refine ⟨3184109513484682321348685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122739675656454880899123 3184109513484682321348685)
                  ·
                    refine ⟨1194041067556755870505757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184109513484682321348685 1194041067556755870505757)
                    ·
                      refine ⟨447765400333783451439659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194041067556755870505757 447765400333783451439659)
                      ·
                        rfl

theorem cell23_872020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_872020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872020 prefixEnd_872020 := by exact prefixLift 872020
  have htrace : WordTrace (prefixWord ++ tailWord_872020) baseStart_872020 baseEnd_872020 := by
    simpa [prefixWord, tailWord_872020, baseEnd_872020] using wordTrace_append hprefix tailTrace_872020
  have hstable : (prefixWord ++ tailWord_872020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872020).length < 2 ^ (prefixWord ++ tailWord_872020).sum := by decide
  have hdescent : baseEnd_872020 < baseStart_872020 := by decide
  rcases family_descends (prefixWord ++ tailWord_872020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872054 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_872054 : Nat := 118140960795 + 872054 * 2 ^ 59
def prefixEnd_872054 : Nat := 4983230072969 + 3 ^ 40 * 872054 * 2
def baseEnd_872054 : Nat := 447782858676036318414503

theorem tailTrace_872054 : CollatzResearch.WordTrace tailWord_872054 prefixEnd_872054 447782858676036318414503 := by
  unfold tailWord_872054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987901398919047988186951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21204281588469845207327477 1987901398919047988186951)
  ·
    refine ⟨2981852098378571982280427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1987901398919047988186951 2981852098378571982280427)
    ·
      refine ⟨4472778147567857973420641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981852098378571982280427 4472778147567857973420641)
      ·
        refine ⟨3354583610675893480065481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4472778147567857973420641 3354583610675893480065481)
        ·
          refine ⟨2515937708006920110049111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354583610675893480065481 2515937708006920110049111)
          ·
            refine ⟨3773906562010380165073667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515937708006920110049111 3773906562010380165073667)
            ·
              refine ⟨5660859843015570247610501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773906562010380165073667 5660859843015570247610501)
              ·
                refine ⟨1061411220565419421426969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5660859843015570247610501 1061411220565419421426969)
                ·
                  refine ⟨796058415424064566070227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1061411220565419421426969 796058415424064566070227)
                  ·
                    refine ⟨1194087623136096849105341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 796058415424064566070227 1194087623136096849105341)
                    ·
                      refine ⟨447782858676036318414503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194087623136096849105341 447782858676036318414503)
                      ·
                        rfl

theorem cell23_872054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_872054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872054 prefixEnd_872054 := by exact prefixLift 872054
  have htrace : WordTrace (prefixWord ++ tailWord_872054) baseStart_872054 baseEnd_872054 := by
    simpa [prefixWord, tailWord_872054, baseEnd_872054] using wordTrace_append hprefix tailTrace_872054
  have hstable : (prefixWord ++ tailWord_872054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872054).length < 2 ^ (prefixWord ++ tailWord_872054).sum := by decide
  have hdescent : baseEnd_872054 < baseStart_872054 := by decide
  rcases family_descends (prefixWord ++ tailWord_872054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872060 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_872060 : Nat := 118140960795 + 872060 * 2 ^ 59
def prefixEnd_872060 : Nat := 4983230072969 + 3 ^ 40 * 872060 * 2
def baseEnd_872060 : Nat := 447785939559963294939475

theorem tailTrace_872060 : CollatzResearch.WordTrace tailWord_872060 prefixEnd_872060 447785939559963294939475 := by
  unfold tailWord_872060
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903320610341515417854817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21204427480455353890473089 15903320610341515417854817)
  ·
    refine ⟨11927490457756136563391113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15903320610341515417854817 11927490457756136563391113)
    ·
      refine ⟨8945617843317102422543335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11927490457756136563391113 8945617843317102422543335)
      ·
        refine ⟨13418426764975653633815003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945617843317102422543335 13418426764975653633815003)
        ·
          refine ⟨20127640147463480450722505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13418426764975653633815003 20127640147463480450722505)
          ·
            refine ⟨15095730110597610338041879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20127640147463480450722505 15095730110597610338041879)
            ·
              refine ⟨22643595165896415507062819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15095730110597610338041879 22643595165896415507062819)
              ·
                refine ⟨33965392748844623260594229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22643595165896415507062819 33965392748844623260594229)
                ·
                  refine ⟨3184255570204183430680709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33965392748844623260594229 3184255570204183430680709)
                  ·
                    refine ⟨597047919413284393252633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184255570204183430680709 597047919413284393252633)
                    ·
                      refine ⟨447785939559963294939475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597047919413284393252633 447785939559963294939475)
                      ·
                        rfl

theorem cell23_872060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_872060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872060 prefixEnd_872060 := by exact prefixLift 872060
  have htrace : WordTrace (prefixWord ++ tailWord_872060) baseStart_872060 baseEnd_872060 := by
    simpa [prefixWord, tailWord_872060, baseEnd_872060] using wordTrace_append hprefix tailTrace_872060
  have hstable : (prefixWord ++ tailWord_872060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872060).length < 2 ^ (prefixWord ++ tailWord_872060).sum := by decide
  have hdescent : baseEnd_872060 < baseStart_872060 := by decide
  rcases family_descends (prefixWord ++ tailWord_872060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872073 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_872073 : Nat := 118140960795 + 872073 * 2 ^ 59
def prefixEnd_872073 : Nat := 4983230072969 + 3 ^ 40 * 872073 * 2
def baseEnd_872073 : Nat := 447792614808471744076915

theorem tailTrace_872073 : CollatzResearch.WordTrace tailWord_872073 prefixEnd_872073 447792614808471744076915 := by
  unfold tailWord_872073
  simp only [CollatzResearch.WordTrace]
  refine ⟨31807115369635934055932873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21204743579757289370621915 31807115369635934055932873)
  ·
    refine ⟨23855336527226950541949655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31807115369635934055932873 23855336527226950541949655)
    ·
      refine ⟨35783004790840425812924483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23855336527226950541949655 35783004790840425812924483)
      ·
        refine ⟨53674507186260638719386725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35783004790840425812924483 53674507186260638719386725)
        ·
          refine ⟨10063970097423869759885011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53674507186260638719386725 10063970097423869759885011)
          ·
            refine ⟨15095955146135804639827517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10063970097423869759885011 15095955146135804639827517)
            ·
              refine ⟨5660983179800926739935319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15095955146135804639827517 5660983179800926739935319)
              ·
                refine ⟨8491474769701390109902979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5660983179800926739935319 8491474769701390109902979)
                ·
                  refine ⟨12737212154552085164854469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8491474769701390109902979 12737212154552085164854469)
                  ·
                    refine ⟨2388227278978515968410213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12737212154552085164854469 2388227278978515968410213)
                    ·
                      refine ⟨447792614808471744076915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2388227278978515968410213 447792614808471744076915)
                      ·
                        rfl

theorem cell23_872073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_872073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872073 prefixEnd_872073 := by exact prefixLift 872073
  have htrace : WordTrace (prefixWord ++ tailWord_872073) baseStart_872073 baseEnd_872073 := by
    simpa [prefixWord, tailWord_872073, baseEnd_872073] using wordTrace_append hprefix tailTrace_872073
  have hstable : (prefixWord ++ tailWord_872073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872073).length < 2 ^ (prefixWord ++ tailWord_872073).sum := by decide
  have hdescent : baseEnd_872073 < baseStart_872073 := by decide
  rcases family_descends (prefixWord ++ tailWord_872073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872093 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_872093 : Nat := 118140960795 + 872093 * 2 ^ 59
def prefixEnd_872093 : Nat := 4983230072969 + 3 ^ 40 * 872093 * 2
def baseEnd_872093 : Nat := 447802884421561665826823

theorem tailTrace_872093 : CollatzResearch.WordTrace tailWord_872093 prefixEnd_872093 447802884421561665826823 := by
  unfold tailWord_872093
  simp only [CollatzResearch.WordTrace]
  refine ⟨31807844829563477471660933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21205229886375651647773955 31807844829563477471660933)
  ·
    refine ⟨5963970905543152025936425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31807844829563477471660933 5963970905543152025936425)
    ·
      refine ⟨4472978179157364019452319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5963970905543152025936425 4472978179157364019452319)
      ·
        refine ⟨6709467268736046029178479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472978179157364019452319 6709467268736046029178479)
        ·
          refine ⟨10064200903104069043767719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709467268736046029178479 10064200903104069043767719)
          ·
            refine ⟨15096301354656103565651579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10064200903104069043767719 15096301354656103565651579)
            ·
              refine ⟨22644452031984155348477369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15096301354656103565651579 22644452031984155348477369)
              ·
                refine ⟨16983339023988116511358027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22644452031984155348477369 16983339023988116511358027)
                ·
                  refine ⟨25475008535982174767037041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16983339023988116511358027 25475008535982174767037041)
                  ·
                    refine ⟨19106256401986631075277781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25475008535982174767037041 19106256401986631075277781)
                    ·
                      refine ⟨447802884421561665826823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19106256401986631075277781 447802884421561665826823)
                      ·
                        rfl

theorem cell23_872093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_872093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872093 prefixEnd_872093 := by exact prefixLift 872093
  have htrace : WordTrace (prefixWord ++ tailWord_872093) baseStart_872093 baseEnd_872093 := by
    simpa [prefixWord, tailWord_872093, baseEnd_872093] using wordTrace_append hprefix tailTrace_872093
  have hstable : (prefixWord ++ tailWord_872093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872093).length < 2 ^ (prefixWord ++ tailWord_872093).sum := by decide
  have hdescent : baseEnd_872093 < baseStart_872093 := by decide
  rcases family_descends (prefixWord ++ tailWord_872093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872094 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_872094 : Nat := 118140960795 + 872094 * 2 ^ 59
def prefixEnd_872094 : Nat := 4983230072969 + 3 ^ 40 * 872094 * 2
def baseEnd_872094 : Nat := 447803397902216161914319

theorem tailTrace_872094 : CollatzResearch.WordTrace tailWord_872094 prefixEnd_872094 447803397902216161914319 := by
  unfold tailWord_872094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975985162819981830305917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21205254201706569761631557 3975985162819981830305917)
  ·
    refine ⟨1490994436057493186364719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3975985162819981830305917 1490994436057493186364719)
    ·
      refine ⟨2236491654086239779547079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1490994436057493186364719 2236491654086239779547079)
      ·
        refine ⟨3354737481129359669320619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236491654086239779547079 3354737481129359669320619)
        ·
          refine ⟨5032106221694039503980929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354737481129359669320619 5032106221694039503980929)
          ·
            refine ⟨3774079666270529627985697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5032106221694039503980929 3774079666270529627985697)
            ·
              refine ⟨2830559749702897220989273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774079666270529627985697 2830559749702897220989273)
              ·
                refine ⟨2122919812277172915741955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830559749702897220989273 2122919812277172915741955)
                ·
                  refine ⟨3184379718415759373612933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122919812277172915741955 3184379718415759373612933)
                  ·
                    refine ⟨597071197202954882552425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184379718415759373612933 597071197202954882552425)
                    ·
                      refine ⟨447803397902216161914319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597071197202954882552425 447803397902216161914319)
                      ·
                        rfl

theorem cell23_872094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_872094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872094 prefixEnd_872094 := by exact prefixLift 872094
  have htrace : WordTrace (prefixWord ++ tailWord_872094) baseStart_872094 baseEnd_872094 := by
    simpa [prefixWord, tailWord_872094, baseEnd_872094] using wordTrace_append hprefix tailTrace_872094
  have hstable : (prefixWord ++ tailWord_872094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872094).length < 2 ^ (prefixWord ++ tailWord_872094).sum := by decide
  have hdescent : baseEnd_872094 < baseStart_872094 := by decide
  rcases family_descends (prefixWord ++ tailWord_872094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872117 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 7]
def baseStart_872117 : Nat := 118140960795 + 872117 * 2 ^ 59
def prefixEnd_872117 : Nat := 4983230072969 + 3 ^ 40 * 872117 * 2
def baseEnd_872117 : Nat := 49757245328585507991857

theorem tailTrace_872117 : CollatzResearch.WordTrace tailWord_872117 prefixEnd_872117 49757245328585507991857 := by
  unfold tailWord_872117
  simp only [CollatzResearch.WordTrace]
  refine ⟨31808720181476529570534605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21205813454317686380356403 31808720181476529570534605)
  ·
    refine ⟨11928270068053698588950477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31808720181476529570534605 11928270068053698588950477)
    ·
      refine ⟨4473101275520136970856429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11928270068053698588950477 4473101275520136970856429)
      ·
        refine ⟨1677412978320051364071161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4473101275520136970856429 1677412978320051364071161)
        ·
          refine ⟨1258059733740038523053371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677412978320051364071161 1258059733740038523053371)
          ·
            refine ⟨1887089600610057784580057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258059733740038523053371 1887089600610057784580057)
            ·
              refine ⟨1415317200457543338435043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887089600610057784580057 1415317200457543338435043)
              ·
                refine ⟨2122975800686315007652565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415317200457543338435043 2122975800686315007652565)
                ·
                  refine ⟨49757245328585507991857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2122975800686315007652565 49757245328585507991857)
                  ·
                    rfl

theorem cell23_872117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_872117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872117 prefixEnd_872117 := by exact prefixLift 872117
  have htrace : WordTrace (prefixWord ++ tailWord_872117) baseStart_872117 baseEnd_872117 := by
    simpa [prefixWord, tailWord_872117, baseEnd_872117] using wordTrace_append hprefix tailTrace_872117
  have hstable : (prefixWord ++ tailWord_872117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872117).length < 2 ^ (prefixWord ++ tailWord_872117).sum := by decide
  have hdescent : baseEnd_872117 < baseStart_872117 := by decide
  rcases family_descends (prefixWord ++ tailWord_872117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872120 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 7, 2]
def baseStart_872120 : Nat := 118140960795 + 872120 * 2 ^ 59
def prefixEnd_872120 : Nat := 4983230072969 + 3 ^ 40 * 872120 * 2
def baseEnd_872120 : Nat := 447816748399233060189199

theorem tailTrace_872120 : CollatzResearch.WordTrace tailWord_872120 prefixEnd_872120 447816748399233060189199 := by
  unfold tailWord_872120
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904414800232830541446907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21205886400310440721929209 15904414800232830541446907)
  ·
    refine ⟨23856622200349245812170361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15904414800232830541446907 23856622200349245812170361)
    ·
      refine ⟨17892466650261934359127771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23856622200349245812170361 17892466650261934359127771)
      ·
        refine ⟨26838699975392901538691657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17892466650261934359127771 26838699975392901538691657)
        ·
          refine ⟨20129024981544676154018743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26838699975392901538691657 20129024981544676154018743)
          ·
            refine ⟨30193537472317014231028115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20129024981544676154018743 30193537472317014231028115)
            ·
              refine ⟨45290306208475521346542173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30193537472317014231028115 45290306208475521346542173)
              ·
                refine ⟨16983864828178320504953315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45290306208475521346542173 16983864828178320504953315)
                ·
                  refine ⟨25475797242267480757429973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16983864828178320504953315 25475797242267480757429973)
                  ·
                    refine ⟨597088997865644080252265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25475797242267480757429973 597088997865644080252265)
                    ·
                      refine ⟨447816748399233060189199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597088997865644080252265 447816748399233060189199)
                      ·
                        rfl

theorem cell23_872120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_872120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872120 prefixEnd_872120 := by exact prefixLift 872120
  have htrace : WordTrace (prefixWord ++ tailWord_872120) baseStart_872120 baseEnd_872120 := by
    simpa [prefixWord, tailWord_872120, baseEnd_872120] using wordTrace_append hprefix tailTrace_872120
  have hstable : (prefixWord ++ tailWord_872120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872120).length < 2 ^ (prefixWord ++ tailWord_872120).sum := by decide
  have hdescent : baseEnd_872120 < baseStart_872120 := by decide
  rcases family_descends (prefixWord ++ tailWord_872120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872123 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5]
def baseStart_872123 : Nat := 118140960795 + 872123 * 2 ^ 59
def prefixEnd_872123 : Nat := 4983230072969 + 3 ^ 40 * 872123 * 2
def baseEnd_872123 : Nat := 447818288841196548451685

theorem tailTrace_872123 : CollatzResearch.WordTrace tailWord_872123 prefixEnd_872123 447818288841196548451685 := by
  unfold tailWord_872123
  simp only [CollatzResearch.WordTrace]
  refine ⟨31808939019454792595253023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21205959346303195063502015 31808939019454792595253023)
  ·
    refine ⟨47713408529182188892879535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31808939019454792595253023 47713408529182188892879535)
    ·
      refine ⟨71570112793773283339319303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47713408529182188892879535 71570112793773283339319303)
      ·
        refine ⟨107355169190659925008978955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71570112793773283339319303 107355169190659925008978955)
        ·
          refine ⟨161032753785989887513468433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107355169190659925008978955 161032753785989887513468433)
          ·
            refine ⟨120774565339492415635101325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161032753785989887513468433 120774565339492415635101325)
            ·
              refine ⟨45290462002309655863162997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120774565339492415635101325 45290462002309655863162997)
              ·
                refine ⟨4245980812716530237171531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45290462002309655863162997 4245980812716530237171531)
                ·
                  refine ⟨6368971219074795355757297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245980812716530237171531 6368971219074795355757297)
                  ·
                    refine ⟨4776728414306096516817973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6368971219074795355757297 4776728414306096516817973)
                    ·
                      refine ⟨447818288841196548451685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4776728414306096516817973 447818288841196548451685)
                      ·
                        rfl

theorem cell23_872123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_872123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872123 prefixEnd_872123 := by exact prefixLift 872123
  have htrace : WordTrace (prefixWord ++ tailWord_872123) baseStart_872123 baseEnd_872123 := by
    simpa [prefixWord, tailWord_872123, baseEnd_872123] using wordTrace_append hprefix tailTrace_872123
  have hstable : (prefixWord ++ tailWord_872123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872123).length < 2 ^ (prefixWord ++ tailWord_872123).sum := by decide
  have hdescent : baseEnd_872123 < baseStart_872123 := by decide
  rcases family_descends (prefixWord ++ tailWord_872123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872134 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_872134 : Nat := 118140960795 + 872134 * 2 ^ 59
def prefixEnd_872134 : Nat := 4983230072969 + 3 ^ 40 * 872134 * 2
def baseEnd_872134 : Nat := 49758215236488445046015

theorem tailTrace_872134 : CollatzResearch.WordTrace tailWord_872134 prefixEnd_872134 49758215236488445046015 := by
  unfold tailWord_872134
  simp only [CollatzResearch.WordTrace]
  refine ⟨994041881950466921059483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21206226814943294315935637 994041881950466921059483)
  ·
    refine ⟨1491062822925700381589225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 994041881950466921059483 1491062822925700381589225)
    ·
      refine ⟨1118297117194275286191919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1491062822925700381589225 1118297117194275286191919)
      ·
        refine ⟨1677445675791412929287879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118297117194275286191919 1677445675791412929287879)
        ·
          refine ⟨2516168513687119393931819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677445675791412929287879 2516168513687119393931819)
          ·
            refine ⟨3774252770530679090897729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516168513687119393931819 3774252770530679090897729)
            ·
              refine ⟨2830689577898009318173297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774252770530679090897729 2830689577898009318173297)
              ·
                refine ⟨2123017183423506988629973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830689577898009318173297 2123017183423506988629973)
                ·
                  refine ⟨49758215236488445046015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2123017183423506988629973 49758215236488445046015)
                  ·
                    rfl

theorem cell23_872134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_872134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872134 prefixEnd_872134 := by exact prefixLift 872134
  have htrace : WordTrace (prefixWord ++ tailWord_872134) baseStart_872134 baseEnd_872134 := by
    simpa [prefixWord, tailWord_872134, baseEnd_872134] using wordTrace_append hprefix tailTrace_872134
  have hstable : (prefixWord ++ tailWord_872134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872134).length < 2 ^ (prefixWord ++ tailWord_872134).sum := by decide
  have hdescent : baseEnd_872134 < baseStart_872134 := by decide
  rcases family_descends (prefixWord ++ tailWord_872134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872160 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 5, 4]
def baseStart_872160 : Nat := 118140960795 + 872160 * 2 ^ 59
def prefixEnd_872160 : Nat := 4983230072969 + 3 ^ 40 * 872160 * 2
def baseEnd_872160 : Nat := 149279095875137634563005

theorem tailTrace_872160 : CollatzResearch.WordTrace tailWord_872160 prefixEnd_872160 149279095875137634563005 := by
  unfold tailWord_872160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15905144260160373957174967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21206859013547165276233289 15905144260160373957174967)
  ·
    refine ⟨23857716390240560935762451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15905144260160373957174967 23857716390240560935762451)
    ·
      refine ⟨35786574585360841403643677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23857716390240560935762451 35786574585360841403643677)
      ·
        refine ⟨13419965469510315526366379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35786574585360841403643677 13419965469510315526366379)
        ·
          refine ⟨20129948204265473289549569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13419965469510315526366379 20129948204265473289549569)
          ·
            refine ⟨15097461153199104967162177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20129948204265473289549569 15097461153199104967162177)
            ·
              refine ⟨11323095864899328725371633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15097461153199104967162177 11323095864899328725371633)
              ·
                refine ⟨8492321898674496544028725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11323095864899328725371633 8492321898674496544028725)
                ·
                  refine ⟨796155178000734051002693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8492321898674496544028725 796155178000734051002693)
                  ·
                    refine ⟨149279095875137634563005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796155178000734051002693 149279095875137634563005)
                    ·
                      rfl

theorem cell23_872160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_872160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872160 prefixEnd_872160 := by exact prefixLift 872160
  have htrace : WordTrace (prefixWord ++ tailWord_872160) baseStart_872160 baseEnd_872160 := by
    simpa [prefixWord, tailWord_872160, baseEnd_872160] using wordTrace_append hprefix tailTrace_872160
  have hstable : (prefixWord ++ tailWord_872160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872160).length < 2 ^ (prefixWord ++ tailWord_872160).sum := by decide
  have hdescent : baseEnd_872160 < baseStart_872160 := by decide
  rcases family_descends (prefixWord ++ tailWord_872160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872177 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 3, 4]
def baseStart_872177 : Nat := 118140960795 + 872177 * 2 ^ 59
def prefixEnd_872177 : Nat := 4983230072969 + 3 ^ 40 * 872177 * 2
def baseEnd_872177 : Nat := 149282005598846445725479

theorem tailTrace_872177 : CollatzResearch.WordTrace tailWord_872177 prefixEnd_872177 149282005598846445725479 := by
  unfold tailWord_872177
  simp only [CollatzResearch.WordTrace]
  refine ⟨31810908561259159817718785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21207272374172773211812523 31810908561259159817718785)
  ·
    refine ⟨23858181420944369863289089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31810908561259159817718785 23858181420944369863289089)
    ·
      refine ⟨17893636065708277397466817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23858181420944369863289089 17893636065708277397466817)
      ·
        refine ⟨13420227049281208048100113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17893636065708277397466817 13420227049281208048100113)
        ·
          refine ⟨10065170286960906036075085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13420227049281208048100113 10065170286960906036075085)
          ·
            refine ⟨3774438857610339763528157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10065170286960906036075085 3774438857610339763528157)
            ·
              refine ⟨1415414571603877411323059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3774438857610339763528157 1415414571603877411323059)
              ·
                refine ⟨2123121857405816116984589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415414571603877411323059 2123121857405816116984589)
                ·
                  refine ⟨796170696527181043869221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2123121857405816116984589 796170696527181043869221)
                  ·
                    refine ⟨149282005598846445725479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796170696527181043869221 149282005598846445725479)
                    ·
                      rfl

theorem cell23_872177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_872177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872177 prefixEnd_872177 := by exact prefixLift 872177
  have htrace : WordTrace (prefixWord ++ tailWord_872177) baseStart_872177 baseEnd_872177 := by
    simpa [prefixWord, tailWord_872177, baseEnd_872177] using wordTrace_append hprefix tailTrace_872177
  have hstable : (prefixWord ++ tailWord_872177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872177).length < 2 ^ (prefixWord ++ tailWord_872177).sum := by decide
  have hdescent : baseEnd_872177 < baseStart_872177 := by decide
  rcases family_descends (prefixWord ++ tailWord_872177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872228 : List Nat := [2, 3, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_872228 : Nat := 118140960795 + 872228 * 2 ^ 59
def prefixEnd_872228 : Nat := 4983230072969 + 3 ^ 40 * 872228 * 2
def baseEnd_872228 : Nat := 149290734769972879212901

theorem tailTrace_872228 : CollatzResearch.WordTrace tailWord_872228 prefixEnd_872228 149290734769972879212901 := by
  unfold tailWord_872228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15906384342037197763912669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21208512456049597018550225 15906384342037197763912669)
  ·
    refine ⟨5964894128263949161467251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15906384342037197763912669 5964894128263949161467251)
    ·
      refine ⟨8947341192395923742200877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5964894128263949161467251 8947341192395923742200877)
      ·
        refine ⟨3355252947148471403325329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8947341192395923742200877 3355252947148471403325329)
        ·
          refine ⟨2516439710361353552493997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3355252947148471403325329 2516439710361353552493997)
          ·
            refine ⟨943664891385507582185249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2516439710361353552493997 943664891385507582185249)
            ·
              refine ⟨707748668539130686638937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943664891385507582185249 707748668539130686638937)
              ·
                refine ⟨530811501404348014979203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707748668539130686638937 530811501404348014979203)
                ·
                  refine ⟨796217252106522022468805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530811501404348014979203 796217252106522022468805)
                  ·
                    refine ⟨149290734769972879212901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796217252106522022468805 149290734769972879212901)
                    ·
                      rfl

theorem cell23_872228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_872228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872228 prefixEnd_872228 := by exact prefixLift 872228
  have htrace : WordTrace (prefixWord ++ tailWord_872228) baseStart_872228 baseEnd_872228 := by
    simpa [prefixWord, tailWord_872228, baseEnd_872228] using wordTrace_append hprefix tailTrace_872228
  have hstable : (prefixWord ++ tailWord_872228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872228).length < 2 ^ (prefixWord ++ tailWord_872228).sum := by decide
  have hdescent : baseEnd_872228 < baseStart_872228 := by decide
  rcases family_descends (prefixWord ++ tailWord_872228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872268 : List Nat := [2, 2, 1, 3, 4, 1, 2, 3, 1, 1, 3]
def baseStart_872268 : Nat := 118140960795 + 872268 * 2 ^ 59
def prefixEnd_872268 : Nat := 4983230072969 + 3 ^ 40 * 872268 * 2
def baseEnd_872268 : Nat := 447892743536098481138519

theorem tailTrace_872268 : CollatzResearch.WordTrace tailWord_872268 prefixEnd_872268 447892743536098481138519 := by
  unfold tailWord_872268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15907113801964741179640729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21209485069286321572854305 15907113801964741179640729)
  ·
    refine ⟨11930335351473555884730547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15907113801964741179640729 11930335351473555884730547)
    ·
      refine ⟨17895503027210333827095821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11930335351473555884730547 17895503027210333827095821)
      ·
        refine ⟨6710813635203875185160933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17895503027210333827095821 6710813635203875185160933)
        ·
          refine ⟨1258277556600726597217675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6710813635203875185160933 1258277556600726597217675)
          ·
            refine ⟨1887416334901089895826513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258277556600726597217675 1887416334901089895826513)
            ·
              refine ⟨1415562251175817421869885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887416334901089895826513 1415562251175817421869885)
              ·
                refine ⟨530835844190931533201207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1415562251175817421869885 530835844190931533201207)
                ·
                  refine ⟨796253766286397299801811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530835844190931533201207 796253766286397299801811)
                  ·
                    refine ⟨1194380649429595949702717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 796253766286397299801811 1194380649429595949702717)
                    ·
                      refine ⟨447892743536098481138519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194380649429595949702717 447892743536098481138519)
                      ·
                        rfl

theorem cell23_872268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_872268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872268 prefixEnd_872268 := by exact prefixLift 872268
  have htrace : WordTrace (prefixWord ++ tailWord_872268) baseStart_872268 baseEnd_872268 := by
    simpa [prefixWord, tailWord_872268, baseEnd_872268] using wordTrace_append hprefix tailTrace_872268
  have hstable : (prefixWord ++ tailWord_872268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872268).length < 2 ^ (prefixWord ++ tailWord_872268).sum := by decide
  have hdescent : baseEnd_872268 < baseStart_872268 := by decide
  rcases family_descends (prefixWord ++ tailWord_872268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872270 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_872270 : Nat := 118140960795 + 872270 * 2 ^ 59
def prefixEnd_872270 : Nat := 4983230072969 + 3 ^ 40 * 872270 * 2
def baseEnd_872270 : Nat := 447893770497407473313509

theorem tailTrace_872270 : CollatzResearch.WordTrace tailWord_872270 prefixEnd_872270 447893770497407473313509 := by
  unfold tailWord_872270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976787568740279587606783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21209533699948157800569509 3976787568740279587606783)
  ·
    refine ⟨5965181353110419381410175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976787568740279587606783 5965181353110419381410175)
    ·
      refine ⟨8947772029665629072115263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5965181353110419381410175 8947772029665629072115263)
      ·
        refine ⟨13421658044498443608172895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8947772029665629072115263 13421658044498443608172895)
        ·
          refine ⟨20132487066747665412259343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13421658044498443608172895 20132487066747665412259343)
          ·
            refine ⟨30198730600121498118389015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20132487066747665412259343 30198730600121498118389015)
            ·
              refine ⟨45298095900182247177583523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30198730600121498118389015 45298095900182247177583523)
              ·
                refine ⟨67947143850273370766375285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45298095900182247177583523 67947143850273370766375285)
                ·
                  refine ⟨6370044735963128509347683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67947143850273370766375285 6370044735963128509347683)
                  ·
                    refine ⟨9555067103944692764021525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370044735963128509347683 9555067103944692764021525)
                    ·
                      refine ⟨447893770497407473313509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9555067103944692764021525 447893770497407473313509)
                      ·
                        rfl

theorem cell23_872270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_872270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872270 prefixEnd_872270 := by exact prefixLift 872270
  have htrace : WordTrace (prefixWord ++ tailWord_872270) baseStart_872270 baseEnd_872270 := by
    simpa [prefixWord, tailWord_872270, baseEnd_872270] using wordTrace_append hprefix tailTrace_872270
  have hstable : (prefixWord ++ tailWord_872270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872270).length < 2 ^ (prefixWord ++ tailWord_872270).sum := by decide
  have hdescent : baseEnd_872270 < baseStart_872270 := by decide
  rcases family_descends (prefixWord ++ tailWord_872270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872274 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_872274 : Nat := 118140960795 + 872274 * 2 ^ 59
def prefixEnd_872274 : Nat := 4983230072969 + 3 ^ 40 * 872274 * 2
def baseEnd_872274 : Nat := 447895824420025457663491

theorem tailTrace_872274 : CollatzResearch.WordTrace tailWord_872274 prefixEnd_872274 447895824420025457663491 := by
  unfold tailWord_872274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953611610476936345999969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21209630961271830255999917 7953611610476936345999969)
  ·
    refine ⟨5965208707857702259499977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7953611610476936345999969 5965208707857702259499977)
    ·
      refine ⟨4473906530893276694624983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5965208707857702259499977 4473906530893276694624983)
      ·
        refine ⟨6710859796339915041937475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473906530893276694624983 6710859796339915041937475)
        ·
          refine ⟨10066289694509872562906213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710859796339915041937475 10066289694509872562906213)
          ·
            refine ⟨1887429317720601105544915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10066289694509872562906213 1887429317720601105544915)
            ·
              refine ⟨2831143976580901658317373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887429317720601105544915 2831143976580901658317373)
              ·
                refine ⟨1061678991217838121869015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2831143976580901658317373 1061678991217838121869015)
                ·
                  refine ⟨1592518486826757182803523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1061678991217838121869015 1592518486826757182803523)
                  ·
                    refine ⟨2388777730240135774205285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1592518486826757182803523 2388777730240135774205285)
                    ·
                      refine ⟨447895824420025457663491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2388777730240135774205285 447895824420025457663491)
                      ·
                        rfl

theorem cell23_872274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_872274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872274 prefixEnd_872274 := by exact prefixLift 872274
  have htrace : WordTrace (prefixWord ++ tailWord_872274) baseStart_872274 baseEnd_872274 := by
    simpa [prefixWord, tailWord_872274, baseEnd_872274] using wordTrace_append hprefix tailTrace_872274
  have hstable : (prefixWord ++ tailWord_872274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872274).length < 2 ^ (prefixWord ++ tailWord_872274).sum := by decide
  have hdescent : baseEnd_872274 < baseStart_872274 := by decide
  rcases family_descends (prefixWord ++ tailWord_872274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872320 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_872320 : Nat := 118140960795 + 872320 * 2 ^ 59
def prefixEnd_872320 : Nat := 4983230072969 + 3 ^ 40 * 872320 * 2
def baseEnd_872320 : Nat := 447919444530132277688279

theorem tailTrace_872320 : CollatzResearch.WordTrace tailWord_872320 prefixEnd_872320 447919444530132277688279 := by
  unfold tailWord_872320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908062099870547620087207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21210749466494063493449609 15908062099870547620087207)
  ·
    refine ⟨23862093149805821430130811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15908062099870547620087207 23862093149805821430130811)
    ·
      refine ⟨35793139724708732145196217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23862093149805821430130811 35793139724708732145196217)
      ·
        refine ⟨26844854793531549108897163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35793139724708732145196217 26844854793531549108897163)
        ·
          refine ⟨40267282190297323663345745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26844854793531549108897163 40267282190297323663345745)
          ·
            refine ⟨30200461642722992747509309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40267282190297323663345745 30200461642722992747509309)
            ·
              refine ⟨11325173116021122280315991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30200461642722992747509309 11325173116021122280315991)
              ·
                refine ⟨16987759674031683420473987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11325173116021122280315991 16987759674031683420473987)
                ·
                  refine ⟨25481639511047525130710981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16987759674031683420473987 25481639511047525130710981)
                  ·
                    refine ⟨4777807408321410962008309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25481639511047525130710981 4777807408321410962008309)
                    ·
                      refine ⟨447919444530132277688279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4777807408321410962008309 447919444530132277688279)
                      ·
                        rfl

theorem cell23_872320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_872320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872320 prefixEnd_872320 := by exact prefixLift 872320
  have htrace : WordTrace (prefixWord ++ tailWord_872320) baseStart_872320 baseEnd_872320 := by
    simpa [prefixWord, tailWord_872320, baseEnd_872320] using wordTrace_append hprefix tailTrace_872320
  have hstable : (prefixWord ++ tailWord_872320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872320).length < 2 ^ (prefixWord ++ tailWord_872320).sum := by decide
  have hdescent : baseEnd_872320 < baseStart_872320 := by decide
  rcases family_descends (prefixWord ++ tailWord_872320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872324 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_872324 : Nat := 118140960795 + 872324 * 2 ^ 59
def prefixEnd_872324 : Nat := 4983230072969 + 3 ^ 40 * 872324 * 2
def baseEnd_872324 : Nat := 447921498452750262038261

theorem tailTrace_872324 : CollatzResearch.WordTrace tailWord_872324 prefixEnd_872324 447921498452750262038261 := by
  unfold tailWord_872324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908135045863301961660013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21210846727817735948880017 15908135045863301961660013)
  ·
    refine ⟨5965550642198738235622505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15908135045863301961660013 5965550642198738235622505)
    ·
      refine ⟨4474162981649053676716879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5965550642198738235622505 4474162981649053676716879)
      ·
        refine ⟨6711244472473580515075319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474162981649053676716879 6711244472473580515075319)
        ·
          refine ⟨10066866708710370772612979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711244472473580515075319 10066866708710370772612979)
          ·
            refine ⟨15100300063065556158919469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066866708710370772612979 15100300063065556158919469)
            ·
              refine ⟨5662612523649583559594801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15100300063065556158919469 5662612523649583559594801)
              ·
                refine ⟨4246959392737187669696101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662612523649583559594801 4246959392737187669696101)
                ·
                  refine ⟨796304886138222688068019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4246959392737187669696101 796304886138222688068019)
                  ·
                    refine ⟨1194457329207334032102029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 796304886138222688068019 1194457329207334032102029)
                    ·
                      refine ⟨447921498452750262038261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194457329207334032102029 447921498452750262038261)
                      ·
                        rfl

theorem cell23_872324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_872324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872324 prefixEnd_872324 := by exact prefixLift 872324
  have htrace : WordTrace (prefixWord ++ tailWord_872324) baseStart_872324 baseEnd_872324 := by
    simpa [prefixWord, tailWord_872324, baseEnd_872324] using wordTrace_append hprefix tailTrace_872324
  have hstable : (prefixWord ++ tailWord_872324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872324).length < 2 ^ (prefixWord ++ tailWord_872324).sum := by decide
  have hdescent : baseEnd_872324 < baseStart_872324 := by decide
  rcases family_descends (prefixWord ++ tailWord_872324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872381 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_872381 : Nat := 118140960795 + 872381 * 2 ^ 59
def prefixEnd_872381 : Nat := 4983230072969 + 3 ^ 40 * 872381 * 2
def baseEnd_872381 : Nat := 447950766850056539025499

theorem tailTrace_872381 : CollatzResearch.WordTrace tailWord_872381 prefixEnd_872381 447950766850056539025499 := by
  unfold tailWord_872381
  simp only [CollatzResearch.WordTrace]
  refine ⟨31818349052520102658144997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21212232701680068438763331 31818349052520102658144997)
  ·
    refine ⟨5965940447347519248402187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31818349052520102658144997 5965940447347519248402187)
    ·
      refine ⟨8948910671021278872603281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5965940447347519248402187 8948910671021278872603281)
      ·
        refine ⟨6711683003265959154452461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8948910671021278872603281 6711683003265959154452461)
        ·
          refine ⟨2516881126224734682919673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6711683003265959154452461 2516881126224734682919673)
          ·
            refine ⟨1887660844668551012189755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2516881126224734682919673 1887660844668551012189755)
            ·
              refine ⟨2831491267002826518284633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887660844668551012189755 2831491267002826518284633)
              ·
                refine ⟨2123618450252119888713475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831491267002826518284633 2123618450252119888713475)
                ·
                  refine ⟨3185427675378179833070213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123618450252119888713475 3185427675378179833070213)
                  ·
                    refine ⟨597267689133408718700665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3185427675378179833070213 597267689133408718700665)
                    ·
                      refine ⟨447950766850056539025499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597267689133408718700665 447950766850056539025499)
                      ·
                        rfl

theorem cell23_872381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_872381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872381 prefixEnd_872381 := by exact prefixLift 872381
  have htrace : WordTrace (prefixWord ++ tailWord_872381) baseStart_872381 baseEnd_872381 := by
    simpa [prefixWord, tailWord_872381, baseEnd_872381] using wordTrace_append hprefix tailTrace_872381
  have hstable : (prefixWord ++ tailWord_872381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872381).length < 2 ^ (prefixWord ++ tailWord_872381).sum := by decide
  have hdescent : baseEnd_872381 < baseStart_872381 := by decide
  rcases family_descends (prefixWord ++ tailWord_872381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872398 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_872398 : Nat := 118140960795 + 872398 * 2 ^ 59
def prefixEnd_872398 : Nat := 4983230072969 + 3 ^ 40 * 872398 * 2
def baseEnd_872398 : Nat := 447959496021182972512921

theorem tailTrace_872398 : CollatzResearch.WordTrace tailWord_872398 prefixEnd_872398 447959496021182972512921 := by
  unfold tailWord_872398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977371136682314320189231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21212646062305676374342565 3977371136682314320189231)
  ·
    refine ⟨5966056705023471480283847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3977371136682314320189231 5966056705023471480283847)
    ·
      refine ⟨8949085057535207220425771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5966056705023471480283847 8949085057535207220425771)
      ·
        refine ⟨13423627586302810830638657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8949085057535207220425771 13423627586302810830638657)
        ·
          refine ⟨10067720689727108122978993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13423627586302810830638657 10067720689727108122978993)
          ·
            refine ⟨7550790517295331092234245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10067720689727108122978993 7550790517295331092234245)
            ·
              refine ⟨1415773221992874579793921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7550790517295331092234245 1415773221992874579793921)
              ·
                refine ⟨1061829916494655934845441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415773221992874579793921 1061829916494655934845441)
                ·
                  refine ⟨796372437370991951134081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1061829916494655934845441 796372437370991951134081)
                  ·
                    refine ⟨597279328028243963350561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796372437370991951134081 597279328028243963350561)
                    ·
                      refine ⟨447959496021182972512921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597279328028243963350561 447959496021182972512921)
                      ·
                        rfl

theorem cell23_872398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_872398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872398 prefixEnd_872398 := by exact prefixLift 872398
  have htrace : WordTrace (prefixWord ++ tailWord_872398) baseStart_872398 baseEnd_872398 := by
    simpa [prefixWord, tailWord_872398, baseEnd_872398] using wordTrace_append hprefix tailTrace_872398
  have hstable : (prefixWord ++ tailWord_872398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872398).length < 2 ^ (prefixWord ++ tailWord_872398).sum := by decide
  have hdescent : baseEnd_872398 < baseStart_872398 := by decide
  rcases family_descends (prefixWord ++ tailWord_872398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872417 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 4, 5]
def baseStart_872417 : Nat := 118140960795 + 872417 * 2 ^ 59
def prefixEnd_872417 : Nat := 4983230072969 + 3 ^ 40 * 872417 * 2
def baseEnd_872417 : Nat := 149323084051206132725111

theorem tailTrace_872417 : CollatzResearch.WordTrace tailWord_872417 prefixEnd_872417 149323084051206132725111 := by
  unfold tailWord_872417
  simp only [CollatzResearch.WordTrace]
  refine ⟨31819662080389680806455505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21213108053593120537637003 31819662080389680806455505)
  ·
    refine ⟨23864746560292260604841629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31819662080389680806455505 23864746560292260604841629)
    ·
      refine ⟨8949279960109597726815611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23864746560292260604841629 8949279960109597726815611)
      ·
        refine ⟨13423919940164396590223417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8949279960109597726815611 13423919940164396590223417)
        ·
          refine ⟨10067939955123297442667563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13423919940164396590223417 10067939955123297442667563)
          ·
            refine ⟨15101909932684946164001345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067939955123297442667563 15101909932684946164001345)
            ·
              refine ⟨11326432449513709623001009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15101909932684946164001345 11326432449513709623001009)
              ·
                refine ⟨8494824337135282217250757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11326432449513709623001009 8494824337135282217250757)
                ·
                  refine ⟨1592779563212865415734517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8494824337135282217250757 1592779563212865415734517)
                  ·
                    refine ⟨149323084051206132725111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1592779563212865415734517 149323084051206132725111)
                    ·
                      rfl

theorem cell23_872417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_872417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872417 prefixEnd_872417 := by exact prefixLift 872417
  have htrace : WordTrace (prefixWord ++ tailWord_872417) baseStart_872417 baseEnd_872417 := by
    simpa [prefixWord, tailWord_872417, baseEnd_872417] using wordTrace_append hprefix tailTrace_872417
  have hstable : (prefixWord ++ tailWord_872417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872417).length < 2 ^ (prefixWord ++ tailWord_872417).sum := by decide
  have hdescent : baseEnd_872417 < baseStart_872417 := by decide
  rcases family_descends (prefixWord ++ tailWord_872417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872424 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_872424 : Nat := 118140960795 + 872424 * 2 ^ 59
def prefixEnd_872424 : Nat := 4983230072969 + 3 ^ 40 * 872424 * 2
def baseEnd_872424 : Nat := 447972846518199870787801

theorem tailTrace_872424 : CollatzResearch.WordTrace tailWord_872424 prefixEnd_872424 447972846518199870787801 := by
  unfold tailWord_872424
  simp only [CollatzResearch.WordTrace]
  refine ⟨15909958695682160500980163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21213278260909547334640217 15909958695682160500980163)
  ·
    refine ⟨23864938043523240751470245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15909958695682160500980163 23864938043523240751470245)
    ·
      refine ⟨4474675883160607640900671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23864938043523240751470245 4474675883160607640900671)
      ·
        refine ⟨6712013824740911461351007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474675883160607640900671 6712013824740911461351007)
        ·
          refine ⟨10068020737111367192026511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712013824740911461351007 10068020737111367192026511)
          ·
            refine ⟨15102031105667050788039767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068020737111367192026511 15102031105667050788039767)
            ·
              refine ⟨22653046658500576182059651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15102031105667050788039767 22653046658500576182059651)
              ·
                refine ⟨33979569987750864273089477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22653046658500576182059651 33979569987750864273089477)
                ·
                  refine ⟨6371169372703287051204277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33979569987750864273089477 6371169372703287051204277)
                  ·
                    refine ⟨597297128690933161050401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6371169372703287051204277 597297128690933161050401)
                    ·
                      refine ⟨447972846518199870787801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597297128690933161050401 447972846518199870787801)
                      ·
                        rfl

theorem cell23_872424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_872424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872424 prefixEnd_872424 := by exact prefixLift 872424
  have htrace : WordTrace (prefixWord ++ tailWord_872424) baseStart_872424 baseEnd_872424 := by
    simpa [prefixWord, tailWord_872424, baseEnd_872424] using wordTrace_append hprefix tailTrace_872424
  have hstable : (prefixWord ++ tailWord_872424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872424).length < 2 ^ (prefixWord ++ tailWord_872424).sum := by decide
  have hdescent : baseEnd_872424 < baseStart_872424 := by decide
  rcases family_descends (prefixWord ++ tailWord_872424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872438 : List Nat := [5, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_872438 : Nat := 118140960795 + 872438 * 2 ^ 59
def prefixEnd_872438 : Nat := 4983230072969 + 3 ^ 40 * 872438 * 2
def baseEnd_872438 : Nat := 49775559471929201779193

theorem tailTrace_872438 : CollatzResearch.WordTrace tailWord_872438 prefixEnd_872438 49775559471929201779193 := by
  unfold tailWord_872438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1988776750832100087060623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21213618675542400928646645 1988776750832100087060623)
  ·
    refine ⟨2983165126248150130590935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1988776750832100087060623 2983165126248150130590935)
    ·
      refine ⟨4474747689372225195886403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983165126248150130590935 4474747689372225195886403)
      ·
        refine ⟨6712121534058337793829605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474747689372225195886403 6712121534058337793829605)
        ·
          refine ⟨1258522787635938336343051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6712121534058337793829605 1258522787635938336343051)
          ·
            refine ⟨1887784181453907504514577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258522787635938336343051 1887784181453907504514577)
            ·
              refine ⟨1415838136090430628385933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887784181453907504514577 1415838136090430628385933)
              ·
                refine ⟨530939301033911485644725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1415838136090430628385933 530939301033911485644725)
                ·
                  refine ⟨49775559471929201779193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530939301033911485644725 49775559471929201779193)
                  ·
                    rfl

theorem cell23_872438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_872438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872438 prefixEnd_872438 := by exact prefixLift 872438
  have htrace : WordTrace (prefixWord ++ tailWord_872438) baseStart_872438 baseEnd_872438 := by
    simpa [prefixWord, tailWord_872438, baseEnd_872438] using wordTrace_append hprefix tailTrace_872438
  have hstable : (prefixWord ++ tailWord_872438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872438).length < 2 ^ (prefixWord ++ tailWord_872438).sum := by decide
  have hdescent : baseEnd_872438 < baseStart_872438 := by decide
  rcases family_descends (prefixWord ++ tailWord_872438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872474 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_872474 : Nat := 118140960795 + 872474 * 2 ^ 59
def prefixEnd_872474 : Nat := 4983230072969 + 3 ^ 40 * 872474 * 2
def baseEnd_872474 : Nat := 447998520550924675162571

theorem tailTrace_872474 : CollatzResearch.WordTrace tailWord_872474 prefixEnd_872474 447998520550924675162571 := by
  unfold tailWord_872474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955435260295794885320119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21214494027455453027520317 7955435260295794885320119)
  ·
    refine ⟨11933152890443692327980179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7955435260295794885320119 11933152890443692327980179)
    ·
      refine ⟨17899729335665538491970269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11933152890443692327980179 17899729335665538491970269)
      ·
        refine ⟨6712398500874576934488851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17899729335665538491970269 6712398500874576934488851)
        ·
          refine ⟨10068597751311865401733277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712398500874576934488851 10068597751311865401733277)
          ·
            refine ⟨3775724156741949525649979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10068597751311865401733277 3775724156741949525649979)
            ·
              refine ⟨5663586235112924288474969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775724156741949525649979 5663586235112924288474969)
              ·
                refine ⟨4247689676334693216356227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663586235112924288474969 4247689676334693216356227)
                ·
                  refine ⟨6371534514502039824534341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247689676334693216356227 6371534514502039824534341)
                  ·
                    refine ⟨1194662721469132467100189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371534514502039824534341 1194662721469132467100189)
                    ·
                      refine ⟨447998520550924675162571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194662721469132467100189 447998520550924675162571)
                      ·
                        rfl

theorem cell23_872474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_872474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872474 prefixEnd_872474 := by exact prefixLift 872474
  have htrace : WordTrace (prefixWord ++ tailWord_872474) baseStart_872474 baseEnd_872474 := by
    simpa [prefixWord, tailWord_872474, baseEnd_872474] using wordTrace_append hprefix tailTrace_872474
  have hstable : (prefixWord ++ tailWord_872474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872474).length < 2 ^ (prefixWord ++ tailWord_872474).sum := by decide
  have hdescent : baseEnd_872474 < baseStart_872474 := by decide
  rcases family_descends (prefixWord ++ tailWord_872474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872494 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_872494 : Nat := 118140960795 + 872494 * 2 ^ 59
def prefixEnd_872494 : Nat := 4983230072969 + 3 ^ 40 * 872494 * 2
def baseEnd_872494 : Nat := 49778754462668288545831

theorem tailTrace_872494 : CollatzResearch.WordTrace tailWord_872494 prefixEnd_872494 49778754462668288545831 := by
  unfold tailWord_872494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977808812638840369626067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21214980334073815304672357 3977808812638840369626067)
  ·
    refine ⟨5966713218958260554439101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3977808812638840369626067 5966713218958260554439101)
    ·
      refine ⟨2237517457109347707914663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5966713218958260554439101 2237517457109347707914663)
      ·
        refine ⟨3356276185664021561871995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237517457109347707914663 3356276185664021561871995)
        ·
          refine ⟨5034414278496032342807993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356276185664021561871995 5034414278496032342807993)
          ·
            refine ⟨3775810708872024257105995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5034414278496032342807993 3775810708872024257105995)
            ·
              refine ⟨5663716063308036385658993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775810708872024257105995 5663716063308036385658993)
              ·
                refine ⟨4247787047481027289244245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663716063308036385658993 4247787047481027289244245)
                ·
                  refine ⟨49778754462668288545831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4247787047481027289244245 49778754462668288545831)
                  ·
                    rfl

theorem cell23_872494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_872494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872494 prefixEnd_872494 := by exact prefixLift 872494
  have htrace : WordTrace (prefixWord ++ tailWord_872494) baseStart_872494 baseEnd_872494 := by
    simpa [prefixWord, tailWord_872494, baseEnd_872494] using wordTrace_append hprefix tailTrace_872494
  have hstable : (prefixWord ++ tailWord_872494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872494).length < 2 ^ (prefixWord ++ tailWord_872494).sum := by decide
  have hdescent : baseEnd_872494 < baseStart_872494 := by decide
  rcases family_descends (prefixWord ++ tailWord_872494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872498 : List Nat := [3, 2, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_872498 : Nat := 118140960795 + 872498 * 2 ^ 59
def prefixEnd_872498 : Nat := 4983230072969 + 3 ^ 40 * 872498 * 2
def baseEnd_872498 : Nat := 149336948028877527087487

theorem tailTrace_872498 : CollatzResearch.WordTrace tailWord_872498 prefixEnd_872498 149336948028877527087487 := by
  unfold tailWord_872498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955654098274057910038537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21215077595397487760102765 7955654098274057910038537)
  ·
    refine ⟨5966740573705543432528903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7955654098274057910038537 5966740573705543432528903)
    ·
      refine ⟨8950110860558315148793355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5966740573705543432528903 8950110860558315148793355)
      ·
        refine ⟨13425166290837472723190033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8950110860558315148793355 13425166290837472723190033)
        ·
          refine ⟨10068874718128104542392525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13425166290837472723190033 10068874718128104542392525)
          ·
            refine ⟨3775828019298039203397197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10068874718128104542392525 3775828019298039203397197)
            ·
              refine ⟨1415935507236764701273949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3775828019298039203397197 1415935507236764701273949)
              ·
                refine ⟨530975815213786762977731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1415935507236764701273949 530975815213786762977731)
                ·
                  refine ⟨796463722820680144466597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530975815213786762977731 796463722820680144466597)
                  ·
                    refine ⟨149336948028877527087487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796463722820680144466597 149336948028877527087487)
                    ·
                      rfl

theorem cell23_872498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_872498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872498 prefixEnd_872498 := by exact prefixLift 872498
  have htrace : WordTrace (prefixWord ++ tailWord_872498) baseStart_872498 baseEnd_872498 := by
    simpa [prefixWord, tailWord_872498, baseEnd_872498] using wordTrace_append hprefix tailTrace_872498
  have hstable : (prefixWord ++ tailWord_872498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872498).length < 2 ^ (prefixWord ++ tailWord_872498).sum := by decide
  have hdescent : baseEnd_872498 < baseStart_872498 := by decide
  rcases family_descends (prefixWord ++ tailWord_872498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872517 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_872517 : Nat := 118140960795 + 872517 * 2 ^ 59
def prefixEnd_872517 : Nat := 4983230072969 + 3 ^ 40 * 872517 * 2
def baseEnd_872517 : Nat := 448020600219068006924873

theorem tailTrace_872517 : CollatzResearch.WordTrace tailWord_872517 prefixEnd_872517 448020600219068006924873 := by
  unfold tailWord_872517
  simp only [CollatzResearch.WordTrace]
  refine ⟨31823309380027397885095805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21215539586684931923397203 31823309380027397885095805)
  ·
    refine ⟨11933741017510274206910927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31823309380027397885095805 11933741017510274206910927)
    ·
      refine ⟨17900611526265411310366391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11933741017510274206910927 17900611526265411310366391)
      ·
        refine ⟨26850917289398116965549587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17900611526265411310366391 26850917289398116965549587)
        ·
          refine ⟨40276375934097175448324381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26850917289398116965549587 40276375934097175448324381)
          ·
            refine ⟨15103640975286440793121643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40276375934097175448324381 15103640975286440793121643)
            ·
              refine ⟨22655461462929661189682465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15103640975286440793121643 22655461462929661189682465)
              ·
                refine ⟨16991596097197245892261849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22655461462929661189682465 16991596097197245892261849)
                ·
                  refine ⟨12743697072897934419196387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16991596097197245892261849 12743697072897934419196387)
                  ·
                    refine ⟨19115545609346901628794581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12743697072897934419196387 19115545609346901628794581)
                    ·
                      refine ⟨448020600219068006924873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19115545609346901628794581 448020600219068006924873)
                      ·
                        rfl

theorem cell23_872517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_872517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872517 prefixEnd_872517 := by exact prefixLift 872517
  have htrace : WordTrace (prefixWord ++ tailWord_872517) baseStart_872517 baseEnd_872517 := by
    simpa [prefixWord, tailWord_872517, baseEnd_872517] using wordTrace_append hprefix tailTrace_872517
  have hstable : (prefixWord ++ tailWord_872517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872517).length < 2 ^ (prefixWord ++ tailWord_872517).sum := by decide
  have hdescent : baseEnd_872517 < baseStart_872517 := by decide
  rcases family_descends (prefixWord ++ tailWord_872517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872542 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_872542 : Nat := 118140960795 + 872542 * 2 ^ 59
def prefixEnd_872542 : Nat := 4983230072969 + 3 ^ 40 * 872542 * 2
def baseEnd_872542 : Nat := 448033437235430409112259

theorem tailTrace_872542 : CollatzResearch.WordTrace tailWord_872542 prefixEnd_872542 448033437235430409112259 := by
  unfold tailWord_872542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978027650617103394344485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21216147469957884769837253 3978027650617103394344485)
  ·
    refine ⟨745880184490706886439591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3978027650617103394344485 745880184490706886439591)
    ·
      refine ⟨1118820276736060329659387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 745880184490706886439591 1118820276736060329659387)
      ·
        refine ⟨1678230415104090494489081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118820276736060329659387 1678230415104090494489081)
        ·
          refine ⟨1258672811328067870866811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678230415104090494489081 1258672811328067870866811)
          ·
            refine ⟨1888009216992101806300217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258672811328067870866811 1888009216992101806300217)
            ·
              refine ⟨1416006912744076354725163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888009216992101806300217 1416006912744076354725163)
              ·
                refine ⟨2124010369116114532087745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416006912744076354725163 2124010369116114532087745)
                ·
                  refine ⟨1593007776837085899065809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2124010369116114532087745 1593007776837085899065809)
                  ·
                    refine ⟨1194755832627814424299357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1593007776837085899065809 1194755832627814424299357)
                    ·
                      refine ⟨448033437235430409112259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194755832627814424299357 448033437235430409112259)
                      ·
                        rfl

theorem cell23_872542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_872542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872542 prefixEnd_872542 := by exact prefixLift 872542
  have htrace : WordTrace (prefixWord ++ tailWord_872542) baseStart_872542 baseEnd_872542 := by
    simpa [prefixWord, tailWord_872542, baseEnd_872542] using wordTrace_append hprefix tailTrace_872542
  have hstable : (prefixWord ++ tailWord_872542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872542).length < 2 ^ (prefixWord ++ tailWord_872542).sum := by decide
  have hdescent : baseEnd_872542 < baseStart_872542 := by decide
  rcases family_descends (prefixWord ++ tailWord_872542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872558 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_872558 : Nat := 118140960795 + 872558 * 2 ^ 59
def prefixEnd_872558 : Nat := 4983230072969 + 3 ^ 40 * 872558 * 2
def baseEnd_872558 : Nat := 149347217641967448837395

theorem tailTrace_872558 : CollatzResearch.WordTrace tailWord_872558 prefixEnd_872558 149347217641967448837395 := by
  unfold tailWord_872558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978100596609857735917291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21216536515252574591558885 3978100596609857735917291)
  ·
    refine ⟨5967150894914786603875937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3978100596609857735917291 5967150894914786603875937)
    ·
      refine ⟨4475363171186089952906953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5967150894914786603875937 4475363171186089952906953)
      ·
        refine ⟨3356522378389567464680215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4475363171186089952906953 3356522378389567464680215)
        ·
          refine ⟨5034783567584351197020323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356522378389567464680215 5034783567584351197020323)
          ·
            refine ⟨7552175351376526795530485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034783567584351197020323 7552175351376526795530485)
            ·
              refine ⟨708016439191549387080983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7552175351376526795530485 708016439191549387080983)
              ·
                refine ⟨1062024658787324080621475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708016439191549387080983 1062024658787324080621475)
                ·
                  refine ⟨1593036988180986120932213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062024658787324080621475 1593036988180986120932213)
                  ·
                    refine ⟨149347217641967448837395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1593036988180986120932213 149347217641967448837395)
                    ·
                      rfl

theorem cell23_872558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_872558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872558 prefixEnd_872558 := by exact prefixLift 872558
  have htrace : WordTrace (prefixWord ++ tailWord_872558) baseStart_872558 baseEnd_872558 := by
    simpa [prefixWord, tailWord_872558, baseEnd_872558] using wordTrace_append hprefix tailTrace_872558
  have hstable : (prefixWord ++ tailWord_872558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872558).length < 2 ^ (prefixWord ++ tailWord_872558).sum := by decide
  have hdescent : baseEnd_872558 < baseStart_872558 := by decide
  rcases family_descends (prefixWord ++ tailWord_872558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872567 : List Nat := [1, 1, 3, 1, 1, 16]
def baseStart_872567 : Nat := 118140960795 + 872567 * 2 ^ 59
def prefixEnd_872567 : Nat := 4983230072969 + 3 ^ 40 * 872567 * 2
def baseEnd_872567 : Nat := 1843811828196678235801

theorem tailTrace_872567 : CollatzResearch.WordTrace tailWord_872567 prefixEnd_872567 1843811828196678235801 := by
  unfold tailWord_872567
  simp only [CollatzResearch.WordTrace]
  refine ⟨31825133029846256424415955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21216755353230837616277303 31825133029846256424415955)
  ·
    refine ⟨47737699544769384636623933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31825133029846256424415955 47737699544769384636623933)
    ·
      refine ⟨17901637329288519238733975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47737699544769384636623933 17901637329288519238733975)
      ·
        refine ⟨26852455993932778858100963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17901637329288519238733975 26852455993932778858100963)
        ·
          refine ⟨40278683990899168287151445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26852455993932778858100963 40278683990899168287151445)
          ·
            refine ⟨1843811828196678235801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 40278683990899168287151445 1843811828196678235801)
            ·
              rfl

theorem cell23_872567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 16].length) (baseStart_872567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872567 prefixEnd_872567 := by exact prefixLift 872567
  have htrace : WordTrace (prefixWord ++ tailWord_872567) baseStart_872567 baseEnd_872567 := by
    simpa [prefixWord, tailWord_872567, baseEnd_872567] using wordTrace_append hprefix tailTrace_872567
  have hstable : (prefixWord ++ tailWord_872567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872567).length < 2 ^ (prefixWord ++ tailWord_872567).sum := by decide
  have hdescent : baseEnd_872567 < baseStart_872567 := by decide
  rcases family_descends (prefixWord ++ tailWord_872567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872572 : List Nat := [2, 2, 2, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_872572 : Nat := 118140960795 + 872572 * 2 ^ 59
def prefixEnd_872572 : Nat := 4983230072969 + 3 ^ 40 * 872572 * 2
def baseEnd_872572 : Nat := 448048841655065291737121

theorem tailTrace_872572 : CollatzResearch.WordTrace tailWord_872572 prefixEnd_872572 448048841655065291737121 := by
  unfold tailWord_872572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15912657697414071139173985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21216876929885428185565313 15912657697414071139173985)
  ·
    refine ⟨11934493273060553354380489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15912657697414071139173985 11934493273060553354380489)
    ·
      refine ⟨8950869954795415015785367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11934493273060553354380489 8950869954795415015785367)
      ·
        refine ⟨13426304932193122523678051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8950869954795415015785367 13426304932193122523678051)
        ·
          refine ⟨20139457398289683785517077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426304932193122523678051 20139457398289683785517077)
          ·
            refine ⟨944037065544828927446113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20139457398289683785517077 944037065544828927446113)
            ·
              refine ⟨708027799158621695584585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944037065544828927446113 708027799158621695584585)
              ·
                refine ⟨531020849368966271688439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708027799158621695584585 531020849368966271688439)
                ·
                  refine ⟨796531274053449407532659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531020849368966271688439 796531274053449407532659)
                  ·
                    refine ⟨1194796911080174111298989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 796531274053449407532659 1194796911080174111298989)
                    ·
                      refine ⟨448048841655065291737121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194796911080174111298989 448048841655065291737121)
                      ·
                        rfl

theorem cell23_872572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_872572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872572 prefixEnd_872572 := by exact prefixLift 872572
  have htrace : WordTrace (prefixWord ++ tailWord_872572) baseStart_872572 baseEnd_872572 := by
    simpa [prefixWord, tailWord_872572, baseEnd_872572] using wordTrace_append hprefix tailTrace_872572
  have hstable : (prefixWord ++ tailWord_872572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872572).length < 2 ^ (prefixWord ++ tailWord_872572).sum := by decide
  have hdescent : baseEnd_872572 < baseStart_872572 := by decide
  rcases family_descends (prefixWord ++ tailWord_872572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872581 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_872581 : Nat := 118140960795 + 872581 * 2 ^ 59
def prefixEnd_872581 : Nat := 4983230072969 + 3 ^ 40 * 872581 * 2
def baseEnd_872581 : Nat := 448053462980955756524579

theorem tailTrace_872581 : CollatzResearch.WordTrace tailWord_872581 prefixEnd_872581 448053462980955756524579 := by
  unfold tailWord_872581
  simp only [CollatzResearch.WordTrace]
  refine ⟨31825643651795536815425597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21217095767863691210283731 31825643651795536815425597)
  ·
    refine ⟨11934616369423326305784599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31825643651795536815425597 11934616369423326305784599)
    ·
      refine ⟨17901924554134989458676899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11934616369423326305784599 17901924554134989458676899)
      ·
        refine ⟨26852886831202484188015349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17901924554134989458676899 26852886831202484188015349)
        ·
          refine ⟨2517458140425232892626439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26852886831202484188015349 2517458140425232892626439)
          ·
            refine ⟨3776187210637849338939659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517458140425232892626439 3776187210637849338939659)
            ·
              refine ⟨5664280815956774008409489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776187210637849338939659 5664280815956774008409489)
              ·
                refine ⟨4248210611967580506307117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5664280815956774008409489 4248210611967580506307117)
                ·
                  refine ⟨1593078979487842689865169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4248210611967580506307117 1593078979487842689865169)
                  ·
                    refine ⟨1194809234615882017398877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1593078979487842689865169 1194809234615882017398877)
                    ·
                      refine ⟨448053462980955756524579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194809234615882017398877 448053462980955756524579)
                      ·
                        rfl

theorem cell23_872581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_872581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872581 prefixEnd_872581 := by exact prefixLift 872581
  have htrace : WordTrace (prefixWord ++ tailWord_872581) baseStart_872581 baseEnd_872581 := by
    simpa [prefixWord, tailWord_872581, baseEnd_872581] using wordTrace_append hprefix tailTrace_872581
  have hstable : (prefixWord ++ tailWord_872581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872581).length < 2 ^ (prefixWord ++ tailWord_872581).sum := by decide
  have hdescent : baseEnd_872581 < baseStart_872581 := by decide
  rcases family_descends (prefixWord ++ tailWord_872581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872612 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_872612 : Nat := 118140960795 + 872612 * 2 ^ 59
def prefixEnd_872612 : Nat := 4983230072969 + 3 ^ 40 * 872612 * 2
def baseEnd_872612 : Nat := 448069380881245135236937

theorem tailTrace_872612 : CollatzResearch.WordTrace tailWord_872612 prefixEnd_872612 448069380881245135236937 := by
  unfold tailWord_872612
  simp only [CollatzResearch.WordTrace]
  refine ⟨15913387157341614554902045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21217849543122152739869393 15913387157341614554902045)
  ·
    refine ⟨5967520184003105458088267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15913387157341614554902045 5967520184003105458088267)
    ·
      refine ⟨8951280276004658187132401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5967520184003105458088267 8951280276004658187132401)
      ·
        refine ⟨6713460207003493640349301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8951280276004658187132401 6713460207003493640349301)
        ·
          refine ⟨629386894406577528782747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6713460207003493640349301 629386894406577528782747)
          ·
            refine ⟨944080341609866293174121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629386894406577528782747 944080341609866293174121)
            ·
              refine ⟨708060256207399719880591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944080341609866293174121 708060256207399719880591)
              ·
                refine ⟨1062090384311099579820887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708060256207399719880591 1062090384311099579820887)
                ·
                  refine ⟨1593135576466649369731331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062090384311099579820887 1593135576466649369731331)
                  ·
                    refine ⟨2389703364699974054596997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1593135576466649369731331 2389703364699974054596997)
                    ·
                      refine ⟨448069380881245135236937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2389703364699974054596997 448069380881245135236937)
                      ·
                        rfl

theorem cell23_872612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_872612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872612 prefixEnd_872612 := by exact prefixLift 872612
  have htrace : WordTrace (prefixWord ++ tailWord_872612) baseStart_872612 baseEnd_872612 := by
    simpa [prefixWord, tailWord_872612, baseEnd_872612] using wordTrace_append hprefix tailTrace_872612
  have hstable : (prefixWord ++ tailWord_872612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872612).length < 2 ^ (prefixWord ++ tailWord_872612).sum := by decide
  have hdescent : baseEnd_872612 < baseStart_872612 := by decide
  rcases family_descends (prefixWord ++ tailWord_872612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872615 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_872615 : Nat := 118140960795 + 872615 * 2 ^ 59
def prefixEnd_872615 : Nat := 4983230072969 + 3 ^ 40 * 872615 * 2
def baseEnd_872615 : Nat := 448070921323208623499423

theorem tailTrace_872615 : CollatzResearch.WordTrace tailWord_872615 prefixEnd_872615 448070921323208623499423 := by
  unfold tailWord_872615
  simp only [CollatzResearch.WordTrace]
  refine ⟨31826883733672360622163299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21217922489114907081442199 31826883733672360622163299)
  ·
    refine ⟨47740325600508540933244949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31826883733672360622163299 47740325600508540933244949)
    ·
      refine ⟨2237827762523837856245857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47740325600508540933244949 2237827762523837856245857)
      ·
        refine ⟨1678370821892878392184393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2237827762523837856245857 1678370821892878392184393)
        ·
          refine ⟨1258778116419658794138295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678370821892878392184393 1258778116419658794138295)
          ·
            refine ⟨1888167174629488191207443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258778116419658794138295 1888167174629488191207443)
            ·
              refine ⟨2832250761944232286811165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888167174629488191207443 2832250761944232286811165)
              ·
                refine ⟨1062094035729087107554187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832250761944232286811165 1062094035729087107554187)
                ·
                  refine ⟨1593141053593630661331281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062094035729087107554187 1593141053593630661331281)
                  ·
                    refine ⟨1194855790195222995998461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1593141053593630661331281 1194855790195222995998461)
                    ·
                      refine ⟨448070921323208623499423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194855790195222995998461 448070921323208623499423)
                      ·
                        rfl

theorem cell23_872615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_872615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872615 prefixEnd_872615 := by exact prefixLift 872615
  have htrace : WordTrace (prefixWord ++ tailWord_872615) baseStart_872615 baseEnd_872615 := by
    simpa [prefixWord, tailWord_872615, baseEnd_872615] using wordTrace_append hprefix tailTrace_872615
  have hstable : (prefixWord ++ tailWord_872615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872615).length < 2 ^ (prefixWord ++ tailWord_872615).sum := by decide
  have hdescent : baseEnd_872615 < baseStart_872615 := by decide
  rcases family_descends (prefixWord ++ tailWord_872615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872634 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_872634 : Nat := 118140960795 + 872634 * 2 ^ 59
def prefixEnd_872634 : Nat := 4983230072969 + 3 ^ 40 * 872634 * 2
def baseEnd_872634 : Nat := 448080677455644049161835

theorem tailTrace_872634 : CollatzResearch.WordTrace tailWord_872634 prefixEnd_872634 448080677455644049161835 := by
  unfold tailWord_872634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956894180150881716776239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21218384480402351244736637 7956894180150881716776239)
  ·
    refine ⟨11935341270226322575164359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7956894180150881716776239 11935341270226322575164359)
    ·
      refine ⟨17903011905339483862746539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11935341270226322575164359 17903011905339483862746539)
      ·
        refine ⟨26854517858009225794119809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17903011905339483862746539 26854517858009225794119809)
        ·
          refine ⟨20140888393506919345589857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26854517858009225794119809 20140888393506919345589857)
          ·
            refine ⟨15105666295130189509192393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20140888393506919345589857 15105666295130189509192393)
            ·
              refine ⟨11329249721347642131894295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15105666295130189509192393 11329249721347642131894295)
              ·
                refine ⟨16993874582021463197841443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11329249721347642131894295 16993874582021463197841443)
                ·
                  refine ⟨25490811873032194796762165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16993874582021463197841443 25490811873032194796762165)
                  ·
                    refine ⟨2389763613096768262196453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25490811873032194796762165 2389763613096768262196453)
                    ·
                      refine ⟨448080677455644049161835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2389763613096768262196453 448080677455644049161835)
                      ·
                        rfl

theorem cell23_872634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_872634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872634 prefixEnd_872634 := by exact prefixLift 872634
  have htrace : WordTrace (prefixWord ++ tailWord_872634) baseStart_872634 baseEnd_872634 := by
    simpa [prefixWord, tailWord_872634, baseEnd_872634] using wordTrace_append hprefix tailTrace_872634
  have hstable : (prefixWord ++ tailWord_872634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872634).length < 2 ^ (prefixWord ++ tailWord_872634).sum := by decide
  have hdescent : baseEnd_872634 < baseStart_872634 := by decide
  rcases family_descends (prefixWord ++ tailWord_872634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872642 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_872642 : Nat := 118140960795 + 872642 * 2 ^ 59
def prefixEnd_872642 : Nat := 4983230072969 + 3 ^ 40 * 872642 * 2
def baseEnd_872642 : Nat := 448084785300880017861799

theorem tailTrace_872642 : CollatzResearch.WordTrace tailWord_872642 prefixEnd_872642 448084785300880017861799 := by
  unfold tailWord_872642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956967126143636058349045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21218579003049696155597453 7956967126143636058349045)
  ·
    refine ⟨745965668075965880470223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7956967126143636058349045 745965668075965880470223)
    ·
      refine ⟨1118948502113948820705335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 745965668075965880470223 1118948502113948820705335)
      ·
        refine ⟨1678422753170923231058003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118948502113948820705335 1678422753170923231058003)
        ·
          refine ⟨2517634129756384846587005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678422753170923231058003 2517634129756384846587005)
          ·
            refine ⟨944112798658644317470127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2517634129756384846587005 944112798658644317470127)
            ·
              refine ⟨1416169197987966476205191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944112798658644317470127 1416169197987966476205191)
              ·
                refine ⟨2124253796981949714307787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416169197987966476205191 2124253796981949714307787)
                ·
                  refine ⟨3186380695472924571461681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124253796981949714307787 3186380695472924571461681)
                  ·
                    refine ⟨2389785521604693428596261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3186380695472924571461681 2389785521604693428596261)
                    ·
                      refine ⟨448084785300880017861799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2389785521604693428596261 448084785300880017861799)
                      ·
                        rfl

theorem cell23_872642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_872642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872642 prefixEnd_872642 := by exact prefixLift 872642
  have htrace : WordTrace (prefixWord ++ tailWord_872642) baseStart_872642 baseEnd_872642 := by
    simpa [prefixWord, tailWord_872642, baseEnd_872642] using wordTrace_append hprefix tailTrace_872642
  have hstable : (prefixWord ++ tailWord_872642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872642).length < 2 ^ (prefixWord ++ tailWord_872642).sum := by decide
  have hdescent : baseEnd_872642 < baseStart_872642 := by decide
  rcases family_descends (prefixWord ++ tailWord_872642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872684 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_872684 : Nat := 118140960795 + 872684 * 2 ^ 59
def prefixEnd_872684 : Nat := 4983230072969 + 3 ^ 40 * 872684 * 2
def baseEnd_872684 : Nat := 448106351488368853536605

theorem tailTrace_872684 : CollatzResearch.WordTrace tailWord_872684 prefixEnd_872684 448106351488368853536605 := by
  unfold tailWord_872684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914700185211192703212553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21219600246948256937616737 15914700185211192703212553)
  ·
    refine ⟨11936025138908394527409415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15914700185211192703212553 11936025138908394527409415)
    ·
      refine ⟨17904037708362591791114123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936025138908394527409415 17904037708362591791114123)
      ·
        refine ⟨26856056562543887686671185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17904037708362591791114123 26856056562543887686671185)
        ·
          refine ⟨20142042421907915765003389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26856056562543887686671185 20142042421907915765003389)
          ·
            refine ⟨7553265908215468411876271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20142042421907915765003389 7553265908215468411876271)
            ·
              refine ⟨11329898862323202617814407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7553265908215468411876271 11329898862323202617814407)
              ·
                refine ⟨16994848293484803926721611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11329898862323202617814407 16994848293484803926721611)
                ·
                  refine ⟨25492272440227205890082417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16994848293484803926721611 25492272440227205890082417)
                  ·
                    refine ⟨19119204330170404417561813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25492272440227205890082417 19119204330170404417561813)
                    ·
                      refine ⟨448106351488368853536605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19119204330170404417561813 448106351488368853536605)
                      ·
                        rfl

theorem cell23_872684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_872684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872684 prefixEnd_872684 := by exact prefixLift 872684
  have htrace : WordTrace (prefixWord ++ tailWord_872684) baseStart_872684 baseEnd_872684 := by
    simpa [prefixWord, tailWord_872684, baseEnd_872684] using wordTrace_append hprefix tailTrace_872684
  have hstable : (prefixWord ++ tailWord_872684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872684).length < 2 ^ (prefixWord ++ tailWord_872684).sum := by decide
  have hdescent : baseEnd_872684 < baseStart_872684 := by decide
  rcases family_descends (prefixWord ++ tailWord_872684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872701 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_872701 : Nat := 118140960795 + 872701 * 2 ^ 59
def prefixEnd_872701 : Nat := 4983230072969 + 3 ^ 40 * 872701 * 2
def baseEnd_872701 : Nat := 448115080659495287024027

theorem tailTrace_872701 : CollatzResearch.WordTrace tailWord_872701 prefixEnd_872701 448115080659495287024027 := by
  unfold tailWord_872701
  simp only [CollatzResearch.WordTrace]
  refine ⟨31830020411360797309793957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21220013607573864873195971 31830020411360797309793957)
  ·
    refine ⟨5968128827130149495586367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31830020411360797309793957 5968128827130149495586367)
    ·
      refine ⟨8952193240695224243379551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5968128827130149495586367 8952193240695224243379551)
      ·
        refine ⟨13428289861042836365069327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8952193240695224243379551 13428289861042836365069327)
        ·
          refine ⟨20142434791564254547603991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13428289861042836365069327 20142434791564254547603991)
          ·
            refine ⟨30213652187346381821405987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20142434791564254547603991 30213652187346381821405987)
            ·
              refine ⟨45320478281019572732108981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30213652187346381821405987 45320478281019572732108981)
              ·
                refine ⟨4248794838845584943635217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45320478281019572732108981 4248794838845584943635217)
                ·
                  refine ⟨3186596129134188707726413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248794838845584943635217 3186596129134188707726413)
                  ·
                    refine ⟨1194973548425320765397405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3186596129134188707726413 1194973548425320765397405)
                    ·
                      refine ⟨448115080659495287024027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1194973548425320765397405 448115080659495287024027)
                      ·
                        rfl

theorem cell23_872701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_872701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872701 prefixEnd_872701 := by exact prefixLift 872701
  have htrace : WordTrace (prefixWord ++ tailWord_872701) baseStart_872701 baseEnd_872701 := by
    simpa [prefixWord, tailWord_872701, baseEnd_872701] using wordTrace_append hprefix tailTrace_872701
  have hstable : (prefixWord ++ tailWord_872701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872701).length < 2 ^ (prefixWord ++ tailWord_872701).sum := by decide
  have hdescent : baseEnd_872701 < baseStart_872701 := by decide
  rcases family_descends (prefixWord ++ tailWord_872701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872702 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_872702 : Nat := 118140960795 + 872702 * 2 ^ 59
def prefixEnd_872702 : Nat := 4983230072969 + 3 ^ 40 * 872702 * 2
def baseEnd_872702 : Nat := 448115594140149783111523

theorem tailTrace_872702 : CollatzResearch.WordTrace tailWord_872702 prefixEnd_872702 448115594140149783111523 := by
  unfold tailWord_872702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978757110544646810072545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21220037922904782987053573 3978757110544646810072545)
  ·
    refine ⟨2984067832908485107554409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3978757110544646810072545 2984067832908485107554409)
    ·
      refine ⟨2238050874681363830665807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2984067832908485107554409 2238050874681363830665807)
      ·
        refine ⟨3357076312022045745998711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238050874681363830665807 3357076312022045745998711)
        ·
          refine ⟨5035614468033068618998067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357076312022045745998711 5035614468033068618998067)
          ·
            refine ⟨7553421702049602928497101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035614468033068618998067 7553421702049602928497101)
            ·
              refine ⟨2832533138268601098186413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7553421702049602928497101 2832533138268601098186413)
              ·
                refine ⟨1062199926850725411819905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832533138268601098186413 1062199926850725411819905)
                ·
                  refine ⟨796649945138044058864929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062199926850725411819905 796649945138044058864929)
                  ·
                    refine ⟨597487458853533044148697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796649945138044058864929 597487458853533044148697)
                    ·
                      refine ⟨448115594140149783111523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597487458853533044148697 448115594140149783111523)
                      ·
                        rfl

theorem cell23_872702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_872702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872702 prefixEnd_872702 := by exact prefixLift 872702
  have htrace : WordTrace (prefixWord ++ tailWord_872702) baseStart_872702 baseEnd_872702 := by
    simpa [prefixWord, tailWord_872702, baseEnd_872702] using wordTrace_append hprefix tailTrace_872702
  have hstable : (prefixWord ++ tailWord_872702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872702).length < 2 ^ (prefixWord ++ tailWord_872702).sum := by decide
  have hdescent : baseEnd_872702 < baseStart_872702 := by decide
  rcases family_descends (prefixWord ++ tailWord_872702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872704 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 3, 7]
def baseStart_872704 : Nat := 118140960795 + 872704 * 2 ^ 59
def prefixEnd_872704 : Nat := 4983230072969 + 3 ^ 40 * 872704 * 2
def baseEnd_872704 : Nat := 149372207033819591762171

theorem tailTrace_872704 : CollatzResearch.WordTrace tailWord_872704 prefixEnd_872704 149372207033819591762171 := by
  unfold tailWord_872704
  simp only [CollatzResearch.WordTrace]
  refine ⟨15915064915174964411076583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21220086553566619214768777 15915064915174964411076583)
  ·
    refine ⟨23872597372762446616614875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15915064915174964411076583 23872597372762446616614875)
    ·
      refine ⟨35808896059143669924922313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23872597372762446616614875 35808896059143669924922313)
      ·
        refine ⟨26856672044357752443691735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35808896059143669924922313 26856672044357752443691735)
        ·
          refine ⟨40285008066536628665537603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26856672044357752443691735 40285008066536628665537603)
          ·
            refine ⟨60427512099804942998306405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40285008066536628665537603 60427512099804942998306405)
            ·
              refine ⟨11330158518713426812182451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60427512099804942998306405 11330158518713426812182451)
              ·
                refine ⟨16995237778070140218273677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11330158518713426812182451 16995237778070140218273677)
                ·
                  refine ⟨6373214166776302581852629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16995237778070140218273677 6373214166776302581852629)
                  ·
                    refine ⟨149372207033819591762171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6373214166776302581852629 149372207033819591762171)
                    ·
                      rfl

theorem cell23_872704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_872704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872704 prefixEnd_872704 := by exact prefixLift 872704
  have htrace : WordTrace (prefixWord ++ tailWord_872704) baseStart_872704 baseEnd_872704 := by
    simpa [prefixWord, tailWord_872704, baseEnd_872704] using wordTrace_append hprefix tailTrace_872704
  have hstable : (prefixWord ++ tailWord_872704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872704).length < 2 ^ (prefixWord ++ tailWord_872704).sum := by decide
  have hdescent : baseEnd_872704 < baseStart_872704 := by decide
  rcases family_descends (prefixWord ++ tailWord_872704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872721 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 2, 5]
def baseStart_872721 : Nat := 118140960795 + 872721 * 2 ^ 59
def prefixEnd_872721 : Nat := 4983230072969 + 3 ^ 40 * 872721 * 2
def baseEnd_872721 : Nat := 149375116757528402924645

theorem tailTrace_872721 : CollatzResearch.WordTrace tailWord_872721 prefixEnd_872721 149375116757528402924645 := by
  unfold tailWord_872721
  simp only [CollatzResearch.WordTrace]
  refine ⟨31830749871288340725522017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21220499914192227150348011 31830749871288340725522017)
  ·
    refine ⟨23873062403466255544141513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31830749871288340725522017 23873062403466255544141513)
    ·
      refine ⟨17904796802599691658106135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23873062403466255544141513 17904796802599691658106135)
      ·
        refine ⟨26857195203899537487159203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17904796802599691658106135 26857195203899537487159203)
        ·
          refine ⟨40285792805849306230738805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26857195203899537487159203 40285792805849306230738805)
          ·
            refine ⟨3776793075548372459131763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40285792805849306230738805 3776793075548372459131763)
            ·
              refine ⟨5665189613322558688697645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776793075548372459131763 5665189613322558688697645)
              ·
                refine ⟨2124446104995959508261617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5665189613322558688697645 2124446104995959508261617)
                ·
                  refine ⟨1593334578746969631196213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2124446104995959508261617 1593334578746969631196213)
                  ·
                    refine ⟨149375116757528402924645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1593334578746969631196213 149375116757528402924645)
                    ·
                      rfl

theorem cell23_872721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_872721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872721 prefixEnd_872721 := by exact prefixLift 872721
  have htrace : WordTrace (prefixWord ++ tailWord_872721) baseStart_872721 baseEnd_872721 := by
    simpa [prefixWord, tailWord_872721, baseEnd_872721] using wordTrace_append hprefix tailTrace_872721
  have hstable : (prefixWord ++ tailWord_872721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872721).length < 2 ^ (prefixWord ++ tailWord_872721).sum := by decide
  have hdescent : baseEnd_872721 < baseStart_872721 := by decide
  rcases family_descends (prefixWord ++ tailWord_872721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872738 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_872738 : Nat := 118140960795 + 872738 * 2 ^ 59
def prefixEnd_872738 : Nat := 4983230072969 + 3 ^ 40 * 872738 * 2
def baseEnd_872738 : Nat := 149378026481237214087119

theorem tailTrace_872738 : CollatzResearch.WordTrace tailWord_872738 prefixEnd_872738 149378026481237214087119 := by
  unfold tailWord_872738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957842478056688157222717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21220913274817835085927245 7957842478056688157222717)
  ·
    refine ⟨2984190929271258058958519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7957842478056688157222717 2984190929271258058958519)
    ·
      refine ⟨4476286393906887088437779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2984190929271258058958519 4476286393906887088437779)
      ·
        refine ⟨6714429590860330632656669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4476286393906887088437779 6714429590860330632656669)
        ·
          refine ⟨2517911096572623987246251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6714429590860330632656669 2517911096572623987246251)
          ·
            refine ⟨3776866644858935980869377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517911096572623987246251 3776866644858935980869377)
            ·
              refine ⟨2832649983644201985652033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3776866644858935980869377 2832649983644201985652033)
              ·
                refine ⟨2124487487733151489239025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832649983644201985652033 2124487487733151489239025)
                ·
                  refine ⟨1593365615799863616929269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2124487487733151489239025 1593365615799863616929269)
                  ·
                    refine ⟨149378026481237214087119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1593365615799863616929269 149378026481237214087119)
                    ·
                      rfl

theorem cell23_872738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_872738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872738 prefixEnd_872738 := by exact prefixLift 872738
  have htrace : WordTrace (prefixWord ++ tailWord_872738) baseStart_872738 baseEnd_872738 := by
    simpa [prefixWord, tailWord_872738, baseEnd_872738] using wordTrace_append hprefix tailTrace_872738
  have hstable : (prefixWord ++ tailWord_872738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872738).length < 2 ^ (prefixWord ++ tailWord_872738).sum := by decide
  have hdescent : baseEnd_872738 < baseStart_872738 := by decide
  rcases family_descends (prefixWord ++ tailWord_872738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872772 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_872772 : Nat := 118140960795 + 872772 * 2 ^ 59
def prefixEnd_872772 : Nat := 4983230072969 + 3 ^ 40 * 872772 * 2
def baseEnd_872772 : Nat := 149383845928654836412067

theorem tailTrace_872772 : CollatzResearch.WordTrace tailWord_872772 prefixEnd_872772 149383845928654836412067 := by
  unfold tailWord_872772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916304997051788217814285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21221739996069050957085713 15916304997051788217814285)
  ·
    refine ⟨5968614373894420581680357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15916304997051788217814285 5968614373894420581680357)
    ·
      refine ⟨1119115195105203859065067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5968614373894420581680357 1119115195105203859065067)
      ·
        refine ⟨1678672792657805788597601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119115195105203859065067 1678672792657805788597601)
        ·
          refine ⟨1259004594493354341448201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678672792657805788597601 1259004594493354341448201)
          ·
            refine ⟨944253445870015756086151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259004594493354341448201 944253445870015756086151)
            ·
              refine ⟨1416380168805023634129227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944253445870015756086151 1416380168805023634129227)
              ·
                refine ⟨2124570253207535451193841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416380168805023634129227 2124570253207535451193841)
                ·
                  refine ⟨1593427689905651588395381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2124570253207535451193841 1593427689905651588395381)
                  ·
                    refine ⟨149383845928654836412067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1593427689905651588395381 149383845928654836412067)
                    ·
                      rfl

theorem cell23_872772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_872772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872772 prefixEnd_872772 := by exact prefixLift 872772
  have htrace : WordTrace (prefixWord ++ tailWord_872772) baseStart_872772 baseEnd_872772 := by
    simpa [prefixWord, tailWord_872772, baseEnd_872772] using wordTrace_append hprefix tailTrace_872772
  have hstable : (prefixWord ++ tailWord_872772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872772).length < 2 ^ (prefixWord ++ tailWord_872772).sum := by decide
  have hdescent : baseEnd_872772 < baseStart_872772 := by decide
  rcases family_descends (prefixWord ++ tailWord_872772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872785 : List Nat := [1, 2, 2, 1, 4, 2, 1, 5, 1, 4]
def baseStart_872785 : Nat := 118140960795 + 872785 * 2 ^ 59
def prefixEnd_872785 : Nat := 4983230072969 + 3 ^ 40 * 872785 * 2
def baseEnd_872785 : Nat := 149386071011490986124547

theorem tailTrace_872785 : CollatzResearch.WordTrace tailWord_872785 prefixEnd_872785 149386071011490986124547 := by
  unfold tailWord_872785
  simp only [CollatzResearch.WordTrace]
  refine ⟨31833084143056479655851809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21222056095370986437234539 31833084143056479655851809)
  ·
    refine ⟨23874813107292359741888857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31833084143056479655851809 23874813107292359741888857)
    ·
      refine ⟨17906109830469269806416643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23874813107292359741888857 17906109830469269806416643)
      ·
        refine ⟨26859164745703904709624965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17906109830469269806416643 26859164745703904709624965)
        ·
          refine ⟨5036093389819482133054681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26859164745703904709624965 5036093389819482133054681)
          ·
            refine ⟨3777070042364611599791011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5036093389819482133054681 3777070042364611599791011)
            ·
              refine ⟨5665605063546917399686517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777070042364611599791011 5665605063546917399686517)
              ·
                refine ⟨531150474707523506220611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5665605063546917399686517 531150474707523506220611)
                ·
                  refine ⟨796725712061285259330917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531150474707523506220611 796725712061285259330917)
                  ·
                    refine ⟨149386071011490986124547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796725712061285259330917 149386071011490986124547)
                    ·
                      rfl

theorem cell23_872785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_872785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872785 prefixEnd_872785 := by exact prefixLift 872785
  have htrace : WordTrace (prefixWord ++ tailWord_872785) baseStart_872785 baseEnd_872785 := by
    simpa [prefixWord, tailWord_872785, baseEnd_872785] using wordTrace_append hprefix tailTrace_872785
  have hstable : (prefixWord ++ tailWord_872785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872785).length < 2 ^ (prefixWord ++ tailWord_872785).sum := by decide
  have hdescent : baseEnd_872785 < baseStart_872785 := by decide
  rcases family_descends (prefixWord ++ tailWord_872785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872802 : List Nat := [3, 3, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_872802 : Nat := 118140960795 + 872802 * 2 ^ 59
def prefixEnd_872802 : Nat := 4983230072969 + 3 ^ 40 * 872802 * 2
def baseEnd_872802 : Nat := 149388980735199797287021

theorem tailTrace_872802 : CollatzResearch.WordTrace tailWord_872802 prefixEnd_872802 149388980735199797287021 := by
  unfold tailWord_872802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958426045998722889805165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21222469455996594372813773 7958426045998722889805165)
  ·
    refine ⟨2984409767249521083676937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7958426045998722889805165 2984409767249521083676937)
    ·
      refine ⟨2238307325437140812757703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2984409767249521083676937 2238307325437140812757703)
      ·
        refine ⟨3357460988155711219136555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238307325437140812757703 3357460988155711219136555)
        ·
          refine ⟨5036191482233566828704833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357460988155711219136555 5036191482233566828704833)
          ·
            refine ⟨3777143611675175121528625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5036191482233566828704833 3777143611675175121528625)
            ·
              refine ⟨2832857708756381341146469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777143611675175121528625 2832857708756381341146469)
              ·
                refine ⟨531160820391821501464963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2832857708756381341146469 531160820391821501464963)
                ·
                  refine ⟨796741230587732252197445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531160820391821501464963 796741230587732252197445)
                  ·
                    refine ⟨149388980735199797287021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796741230587732252197445 149388980735199797287021)
                    ·
                      rfl

theorem cell23_872802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_872802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872802 prefixEnd_872802 := by exact prefixLift 872802
  have htrace : WordTrace (prefixWord ++ tailWord_872802) baseStart_872802 baseEnd_872802 := by
    simpa [prefixWord, tailWord_872802, baseEnd_872802] using wordTrace_append hprefix tailTrace_872802
  have hstable : (prefixWord ++ tailWord_872802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872802).length < 2 ^ (prefixWord ++ tailWord_872802).sum := by decide
  have hdescent : baseEnd_872802 < baseStart_872802 := by decide
  rcases family_descends (prefixWord ++ tailWord_872802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872868 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_872868 : Nat := 118140960795 + 872868 * 2 ^ 59
def prefixEnd_872868 : Nat := 4983230072969 + 3 ^ 40 * 872868 * 2
def baseEnd_872868 : Nat := 448200831928796133635759

theorem tailTrace_872868 : CollatzResearch.WordTrace tailWord_872868 prefixEnd_872868 448200831928796133635759 := by
  unfold tailWord_872868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15918055700877892415561629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21224074267837189887415505 15918055700877892415561629)
  ·
    refine ⟨5969270887829209655835611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15918055700877892415561629 5969270887829209655835611)
    ·
      refine ⟨8953906331743814483753417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969270887829209655835611 8953906331743814483753417)
      ·
        refine ⟨6715429748807860862815063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8953906331743814483753417 6715429748807860862815063)
        ·
          refine ⟨10073144623211791294222595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715429748807860862815063 10073144623211791294222595)
          ·
            refine ⟨15109716934817686941333893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10073144623211791294222595 15109716934817686941333893)
            ·
              refine ⟨2833071925278316301500105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15109716934817686941333893 2833071925278316301500105)
              ·
                refine ⟨2124803943958737226125079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833071925278316301500105 2124803943958737226125079)
                ·
                  refine ⟨3187205915938105839187619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124803943958737226125079 3187205915938105839187619)
                  ·
                    refine ⟨4780808873907158758781429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3187205915938105839187619 4780808873907158758781429)
                    ·
                      refine ⟨448200831928796133635759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4780808873907158758781429 448200831928796133635759)
                      ·
                        rfl

theorem cell23_872868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_872868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872868 prefixEnd_872868 := by exact prefixLift 872868
  have htrace : WordTrace (prefixWord ++ tailWord_872868) baseStart_872868 baseEnd_872868 := by
    simpa [prefixWord, tailWord_872868, baseEnd_872868] using wordTrace_append hprefix tailTrace_872868
  have hstable : (prefixWord ++ tailWord_872868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872868).length < 2 ^ (prefixWord ++ tailWord_872868).sum := by decide
  have hdescent : baseEnd_872868 < baseStart_872868 := by decide
  rcases family_descends (prefixWord ++ tailWord_872868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872901 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_872901 : Nat := 118140960795 + 872901 * 2 ^ 59
def prefixEnd_872901 : Nat := 4983230072969 + 3 ^ 40 * 872901 * 2
def baseEnd_872901 : Nat := 149405925596798168174369

theorem tailTrace_872901 : CollatzResearch.WordTrace tailWord_872901 prefixEnd_872901 149405925596798168174369 := by
  unfold tailWord_872901
  simp only [CollatzResearch.WordTrace]
  refine ⟨31837315010636231467074557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21224876673757487644716371 31837315010636231467074557)
  ·
    refine ⟨11938993128988586800152959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31837315010636231467074557 11938993128988586800152959)
    ·
      refine ⟨17908489693482880200229439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11938993128988586800152959 17908489693482880200229439)
      ·
        refine ⟨26862734540224320300344159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17908489693482880200229439 26862734540224320300344159)
        ·
          refine ⟨40294101810336480450516239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26862734540224320300344159 40294101810336480450516239)
          ·
            refine ⟨60441152715504720675774359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40294101810336480450516239 60441152715504720675774359)
            ·
              refine ⟨90661729073257081013661539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60441152715504720675774359 90661729073257081013661539)
              ·
                refine ⟨135992593609885621520492309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90661729073257081013661539 135992593609885621520492309)
                ·
                  refine ⟨6374652825463388508773077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135992593609885621520492309 6374652825463388508773077)
                  ·
                    refine ⟨149405925596798168174369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6374652825463388508773077 149405925596798168174369)
                    ·
                      rfl

theorem cell23_872901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_872901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872901 prefixEnd_872901 := by exact prefixLift 872901
  have htrace : WordTrace (prefixWord ++ tailWord_872901) baseStart_872901 baseEnd_872901 := by
    simpa [prefixWord, tailWord_872901, baseEnd_872901] using wordTrace_append hprefix tailTrace_872901
  have hstable : (prefixWord ++ tailWord_872901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872901).length < 2 ^ (prefixWord ++ tailWord_872901).sum := by decide
  have hdescent : baseEnd_872901 < baseStart_872901 := by decide
  rcases family_descends (prefixWord ++ tailWord_872901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872916 : List Nat := [2, 4, 1, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_872916 : Nat := 118140960795 + 872916 * 2 ^ 59
def prefixEnd_872916 : Nat := 4983230072969 + 3 ^ 40 * 872916 * 2
def baseEnd_872916 : Nat := 448225479000211945835539

theorem tailTrace_872916 : CollatzResearch.WordTrace tailWord_872916 prefixEnd_872916 448225479000211945835539 := by
  unfold tailWord_872916
  simp only [CollatzResearch.WordTrace]
  refine ⟨15918931052790944514435301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21225241403721259352580401 15918931052790944514435301)
  ·
    refine ⟨2984799572398302096456619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15918931052790944514435301 2984799572398302096456619)
    ·
      refine ⟨4477199358597453144684929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2984799572398302096456619 4477199358597453144684929)
      ·
        refine ⟨3357899518948089858513697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4477199358597453144684929 3357899518948089858513697)
        ·
          refine ⟨2518424639211067393885273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3357899518948089858513697 2518424639211067393885273)
          ·
            refine ⟨1888818479408300545413955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518424639211067393885273 1888818479408300545413955)
            ·
              refine ⟨2833227719112450818120933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888818479408300545413955 2833227719112450818120933)
              ·
                refine ⟨531230197333584528397675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2833227719112450818120933 531230197333584528397675)
                ·
                  refine ⟨796845296000376792596513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531230197333584528397675 796845296000376792596513)
                  ·
                    refine ⟨597633972000282594447385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796845296000376792596513 597633972000282594447385)
                    ·
                      refine ⟨448225479000211945835539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597633972000282594447385 448225479000211945835539)
                      ·
                        rfl

theorem cell23_872916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_872916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872916 prefixEnd_872916 := by exact prefixLift 872916
  have htrace : WordTrace (prefixWord ++ tailWord_872916) baseStart_872916 baseEnd_872916 := by
    simpa [prefixWord, tailWord_872916, baseEnd_872916] using wordTrace_append hprefix tailTrace_872916
  have hstable : (prefixWord ++ tailWord_872916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872916).length < 2 ^ (prefixWord ++ tailWord_872916).sum := by decide
  have hdescent : baseEnd_872916 < baseStart_872916 := by decide
  rcases family_descends (prefixWord ++ tailWord_872916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872942 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_872942 : Nat := 118140960795 + 872942 * 2 ^ 59
def prefixEnd_872942 : Nat := 4983230072969 + 3 ^ 40 * 872942 * 2
def baseEnd_872942 : Nat := 448238829497228844110419

theorem tailTrace_872942 : CollatzResearch.WordTrace tailWord_872942 prefixEnd_872942 448238829497228844110419 := by
  unfold tailWord_872942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3979851300435961933664635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21225873602325130312878053 3979851300435961933664635)
  ·
    refine ⟨5969776950653942900496953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3979851300435961933664635 5969776950653942900496953)
    ·
      refine ⟨4477332712990457175372715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5969776950653942900496953 4477332712990457175372715)
      ·
        refine ⟨6715999069485685763059073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477332712990457175372715 6715999069485685763059073)
        ·
          refine ⟨5036999302114264322294305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6715999069485685763059073 5036999302114264322294305)
          ·
            refine ⟨3777749476585698241720729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5036999302114264322294305 3777749476585698241720729)
            ·
              refine ⟨2833312107439273681290547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777749476585698241720729 2833312107439273681290547)
              ·
                refine ⟨4249968161158910521935821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833312107439273681290547 4249968161158910521935821)
                ·
                  refine ⟨1593738060434591445725933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4249968161158910521935821 1593738060434591445725933)
                  ·
                    refine ⟨597651772662971792147225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593738060434591445725933 597651772662971792147225)
                    ·
                      refine ⟨448238829497228844110419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597651772662971792147225 448238829497228844110419)
                      ·
                        rfl

theorem cell23_872942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_872942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872942 prefixEnd_872942 := by exact prefixLift 872942
  have htrace : WordTrace (prefixWord ++ tailWord_872942) baseStart_872942 baseEnd_872942 := by
    simpa [prefixWord, tailWord_872942, baseEnd_872942] using wordTrace_append hprefix tailTrace_872942
  have hstable : (prefixWord ++ tailWord_872942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872942).length < 2 ^ (prefixWord ++ tailWord_872942).sum := by decide
  have hdescent : baseEnd_872942 < baseStart_872942 := by decide
  rcases family_descends (prefixWord ++ tailWord_872942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872989 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_872989 : Nat := 118140960795 + 872989 * 2 ^ 59
def prefixEnd_872989 : Nat := 4983230072969 + 3 ^ 40 * 872989 * 2
def baseEnd_872989 : Nat := 448262963087990160222703

theorem tailTrace_872989 : CollatzResearch.WordTrace tailWord_872989 prefixEnd_872989 448262963087990160222703 := by
  unfold tailWord_872989
  simp only [CollatzResearch.WordTrace]
  refine ⟨31840524634317422496278021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21227016422878281664185347 31840524634317422496278021)
  ·
    refine ⟨5970098368934516718052129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31840524634317422496278021 5970098368934516718052129)
    ·
      refine ⟨4477573776700887538539097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5970098368934516718052129 4477573776700887538539097)
      ·
        refine ⟨3358180332525665653904323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4477573776700887538539097 3358180332525665653904323)
        ·
          refine ⟨5037270498788498480856485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358180332525665653904323 5037270498788498480856485)
          ·
            refine ⟨944488218522843465160591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5037270498788498480856485 944488218522843465160591)
            ·
              refine ⟨1416732327784265197740887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944488218522843465160591 1416732327784265197740887)
              ·
                refine ⟨2125098491676397796611331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416732327784265197740887 2125098491676397796611331)
                ·
                  refine ⟨3187647737514596694916997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125098491676397796611331 3187647737514596694916997)
                  ·
                    refine ⟨597683950783986880296937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3187647737514596694916997 597683950783986880296937)
                    ·
                      refine ⟨448262963087990160222703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597683950783986880296937 448262963087990160222703)
                      ·
                        rfl

theorem cell23_872989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_872989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_872989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_872989 prefixEnd_872989 := by exact prefixLift 872989
  have htrace : WordTrace (prefixWord ++ tailWord_872989) baseStart_872989 baseEnd_872989 := by
    simpa [prefixWord, tailWord_872989, baseEnd_872989] using wordTrace_append hprefix tailTrace_872989
  have hstable : (prefixWord ++ tailWord_872989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872989).length < 2 ^ (prefixWord ++ tailWord_872989).sum := by decide
  have hdescent : baseEnd_872989 < baseStart_872989 := by decide
  rcases family_descends (prefixWord ++ tailWord_872989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873008 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 1, 7]
def baseStart_873008 : Nat := 118140960795 + 873008 * 2 ^ 59
def prefixEnd_873008 : Nat := 4983230072969 + 3 ^ 40 * 873008 * 2
def baseEnd_873008 : Nat := 149424239740141861961705

theorem tailTrace_873008 : CollatzResearch.WordTrace tailWord_873008 prefixEnd_873008 149424239740141861961705 := by
  unfold tailWord_873008
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920608810624294370609839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21227478414165725827479785 15920608810624294370609839)
  ·
    refine ⟨23880913215936441555914759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15920608810624294370609839 23880913215936441555914759)
    ·
      refine ⟨35821369823904662333872139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23880913215936441555914759 35821369823904662333872139)
      ·
        refine ⟨53732054735856993500808209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35821369823904662333872139 53732054735856993500808209)
        ·
          refine ⟨40299041051892745125606157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53732054735856993500808209 40299041051892745125606157)
          ·
            refine ⟨15112140394459779422102309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40299041051892745125606157 15112140394459779422102309)
            ·
              refine ⟨2833526323961208641644183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15112140394459779422102309 2833526323961208641644183)
              ·
                refine ⟨4250289485941812962466275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2833526323961208641644183 4250289485941812962466275)
                ·
                  refine ⟨6375434228912719443699413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250289485941812962466275 6375434228912719443699413)
                  ·
                    refine ⟨149424239740141861961705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6375434228912719443699413 149424239740141861961705)
                    ·
                      rfl

theorem cell23_873008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_873008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873008 prefixEnd_873008 := by exact prefixLift 873008
  have htrace : WordTrace (prefixWord ++ tailWord_873008) baseStart_873008 baseEnd_873008 := by
    simpa [prefixWord, tailWord_873008, baseEnd_873008] using wordTrace_append hprefix tailTrace_873008
  have hstable : (prefixWord ++ tailWord_873008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873008).length < 2 ^ (prefixWord ++ tailWord_873008).sum := by decide
  have hdescent : baseEnd_873008 < baseStart_873008 := by decide
  rcases family_descends (prefixWord ++ tailWord_873008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873025 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 4, 5]
def baseStart_873025 : Nat := 118140960795 + 873025 * 2 ^ 59
def prefixEnd_873025 : Nat := 4983230072969 + 3 ^ 40 * 873025 * 2
def baseEnd_873025 : Nat := 149427149463850673124179

theorem tailTrace_873025 : CollatzResearch.WordTrace tailWord_873025 prefixEnd_873025 149427149463850673124179 := by
  unfold tailWord_873025
  simp only [CollatzResearch.WordTrace]
  refine ⟨31841837662187000644588529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21227891774791333763059019 31841837662187000644588529)
  ·
    refine ⟨23881378246640250483441397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31841837662187000644588529 23881378246640250483441397)
    ·
      refine ⟨2238879210622523482822631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23881378246640250483441397 2238879210622523482822631)
      ·
        refine ⟨3358318815933785224233947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238879210622523482822631 3358318815933785224233947)
        ·
          refine ⟨5037478223900677836350921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358318815933785224233947 5037478223900677836350921)
          ·
            refine ⟨3778108667925508377263191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5037478223900677836350921 3778108667925508377263191)
            ·
              refine ⟨5667163001888262565894787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778108667925508377263191 5667163001888262565894787)
              ·
                refine ⟨8500744502832393848842181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667163001888262565894787 8500744502832393848842181)
                ·
                  refine ⟨1593889594281073846657909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8500744502832393848842181 1593889594281073846657909)
                  ·
                    refine ⟨149427149463850673124179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1593889594281073846657909 149427149463850673124179)
                    ·
                      rfl

theorem cell23_873025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_873025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873025 prefixEnd_873025 := by exact prefixLift 873025
  have htrace : WordTrace (prefixWord ++ tailWord_873025) baseStart_873025 baseEnd_873025 := by
    simpa [prefixWord, tailWord_873025, baseEnd_873025] using wordTrace_append hprefix tailTrace_873025
  have hstable : (prefixWord ++ tailWord_873025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873025).length < 2 ^ (prefixWord ++ tailWord_873025).sum := by decide
  have hdescent : baseEnd_873025 < baseStart_873025 := by decide
  rcases family_descends (prefixWord ++ tailWord_873025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873055 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 3, 4]
def baseStart_873055 : Nat := 118140960795 + 873055 * 2 ^ 59
def prefixEnd_873055 : Nat := 4983230072969 + 3 ^ 40 * 873055 * 2
def baseEnd_873055 : Nat := 149432284270395633999133

theorem tailTrace_873055 : CollatzResearch.WordTrace tailWord_873055 prefixEnd_873055 149432284270395633999133 := by
  unfold tailWord_873055
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842931852078315768180619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21228621234718877178787079 31842931852078315768180619)
  ·
    refine ⟨47764397778117473652270929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31842931852078315768180619 47764397778117473652270929)
    ·
      refine ⟨35823298333588105239203197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47764397778117473652270929 35823298333588105239203197)
      ·
        refine ⟨13433736875095539464701199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35823298333588105239203197 13433736875095539464701199)
        ·
          refine ⟨20150605312643309197051799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13433736875095539464701199 20150605312643309197051799)
          ·
            refine ⟨30225907968964963795577699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20150605312643309197051799 30225907968964963795577699)
            ·
              refine ⟨45338861953447445693366549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30225907968964963795577699 45338861953447445693366549)
              ·
                refine ⟨2125259154067849016876557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45338861953447445693366549 2125259154067849016876557)
                ·
                  refine ⟨796972182775443381328709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2125259154067849016876557 796972182775443381328709)
                  ·
                    refine ⟨149432284270395633999133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796972182775443381328709 149432284270395633999133)
                    ·
                      rfl

theorem cell23_873055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_873055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873055 prefixEnd_873055 := by exact prefixLift 873055
  have htrace : WordTrace (prefixWord ++ tailWord_873055) baseStart_873055 baseEnd_873055 := by
    simpa [prefixWord, tailWord_873055, baseEnd_873055] using wordTrace_append hprefix tailTrace_873055
  have hstable : (prefixWord ++ tailWord_873055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873055).length < 2 ^ (prefixWord ++ tailWord_873055).sum := by decide
  have hdescent : baseEnd_873055 < baseStart_873055 := by decide
  rcases family_descends (prefixWord ++ tailWord_873055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873068 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 10]
def baseStart_873068 : Nat := 118140960795 + 873068 * 2 ^ 59
def prefixEnd_873068 : Nat := 4983230072969 + 3 ^ 40 * 873068 * 2
def baseEnd_873068 : Nat := 49811503117743927903871

theorem tailTrace_873068 : CollatzResearch.WordTrace tailWord_873068 prefixEnd_873068 49811503117743927903871 := by
  unfold tailWord_873068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921703000515609494201929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21228937334020812658935905 15921703000515609494201929)
  ·
    refine ⟨11941277250386707120651447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15921703000515609494201929 11941277250386707120651447)
    ·
      refine ⟨17911915875580060680977171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11941277250386707120651447 17911915875580060680977171)
      ·
        refine ⟨26867873813370091021465757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17911915875580060680977171 26867873813370091021465757)
        ·
          refine ⟨10075452680013784133049659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26867873813370091021465757 10075452680013784133049659)
          ·
            refine ⟨15113179020020676199574489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075452680013784133049659 15113179020020676199574489)
            ·
              refine ⟨11334884265015507149680867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15113179020020676199574489 11334884265015507149680867)
              ·
                refine ⟨17002326397523260724521301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11334884265015507149680867 17002326397523260724521301)
                ·
                  refine ⟨49811503117743927903871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 17002326397523260724521301 49811503117743927903871)
                  ·
                    rfl

theorem cell23_873068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_873068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873068 prefixEnd_873068 := by exact prefixLift 873068
  have htrace : WordTrace (prefixWord ++ tailWord_873068) baseStart_873068 baseEnd_873068 := by
    simpa [prefixWord, tailWord_873068, baseEnd_873068] using wordTrace_append hprefix tailTrace_873068
  have hstable : (prefixWord ++ tailWord_873068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873068).length < 2 ^ (prefixWord ++ tailWord_873068).sum := by decide
  have hdescent : baseEnd_873068 < baseStart_873068 := by decide
  rcases family_descends (prefixWord ++ tailWord_873068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873089 : List Nat := [1, 2, 4, 2, 1, 1, 3, 4, 1, 4]
def baseStart_873089 : Nat := 118140960795 + 873089 * 2 ^ 59
def prefixEnd_873089 : Nat := 4983230072969 + 3 ^ 40 * 873089 * 2
def baseEnd_873089 : Nat := 149438103717813256324081

theorem tailTrace_873089 : CollatzResearch.WordTrace tailWord_873089 prefixEnd_873089 149438103717813256324081 := by
  unfold tailWord_873089
  simp only [CollatzResearch.WordTrace]
  refine ⟨31844171933955139574918321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21229447955970093049945547 31844171933955139574918321)
  ·
    refine ⟨23883128950466354681188741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31844171933955139574918321 23883128950466354681188741)
    ·
      refine ⟨4478086678212441502722889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23883128950466354681188741 4478086678212441502722889)
      ·
        refine ⟨3358565008659331127042167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4478086678212441502722889 3358565008659331127042167)
        ·
          refine ⟨5037847512988996690563251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358565008659331127042167 5037847512988996690563251)
          ·
            refine ⟨7556771269483495035844877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037847512988996690563251 7556771269483495035844877)
            ·
              refine ⟨2833789226056310638441829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7556771269483495035844877 2833789226056310638441829)
              ·
                refine ⟨531335479885558244707843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2833789226056310638441829 531335479885558244707843)
                ·
                  refine ⟨797003219828337367061765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531335479885558244707843 797003219828337367061765)
                  ·
                    refine ⟨149438103717813256324081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797003219828337367061765 149438103717813256324081)
                    ·
                      rfl

theorem cell23_873089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_873089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873089 prefixEnd_873089 := by exact prefixLift 873089
  have htrace : WordTrace (prefixWord ++ tailWord_873089) baseStart_873089 baseEnd_873089 := by
    simpa [prefixWord, tailWord_873089, baseEnd_873089] using wordTrace_append hprefix tailTrace_873089
  have hstable : (prefixWord ++ tailWord_873089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873089).length < 2 ^ (prefixWord ++ tailWord_873089).sum := by decide
  have hdescent : baseEnd_873089 < baseStart_873089 := by decide
  rcases family_descends (prefixWord ++ tailWord_873089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873129 : List Nat := [1, 2, 1, 1, 1, 1, 2, 9, 1, 1, 3]
def baseStart_873129 : Nat := 118140960795 + 873129 * 2 ^ 59
def prefixEnd_873129 : Nat := 4983230072969 + 3 ^ 40 * 873129 * 2
def baseEnd_873129 : Nat := 448334850379619612472059

theorem tailTrace_873129 : CollatzResearch.WordTrace tailWord_873129 prefixEnd_873129 448334850379619612472059 := by
  unfold tailWord_873129
  simp only [CollatzResearch.WordTrace]
  refine ⟨31845630853810226406374441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21230420569206817604249627 31845630853810226406374441)
  ·
    refine ⟨23884223140357669804780831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31845630853810226406374441 23884223140357669804780831)
    ·
      refine ⟨35826334710536504707171247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23884223140357669804780831 35826334710536504707171247)
      ·
        refine ⟨53739502065804757060756871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35826334710536504707171247 53739502065804757060756871)
        ·
          refine ⟨80609253098707135591135307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53739502065804757060756871 80609253098707135591135307)
          ·
            refine ⟨120913879648060703386702961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80609253098707135591135307 120913879648060703386702961)
            ·
              refine ⟨90685409736045527540027221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120913879648060703386702961 90685409736045527540027221)
              ·
                refine ⟨531359822672141762929847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 90685409736045527540027221 531359822672141762929847)
                ·
                  refine ⟨797039734008212644394771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531359822672141762929847 797039734008212644394771)
                  ·
                    refine ⟨1195559601012318966592157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 797039734008212644394771 1195559601012318966592157)
                    ·
                      refine ⟨448334850379619612472059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1195559601012318966592157 448334850379619612472059)
                      ·
                        rfl

theorem cell23_873129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 1, 3].length) (baseStart_873129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873129 prefixEnd_873129 := by exact prefixLift 873129
  have htrace : WordTrace (prefixWord ++ tailWord_873129) baseStart_873129 baseEnd_873129 := by
    simpa [prefixWord, tailWord_873129, baseEnd_873129] using wordTrace_append hprefix tailTrace_873129
  have hstable : (prefixWord ++ tailWord_873129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873129).length < 2 ^ (prefixWord ++ tailWord_873129).sum := by decide
  have hdescent : baseEnd_873129 < baseStart_873129 := by decide
  rcases family_descends (prefixWord ++ tailWord_873129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873162 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_873162 : Nat := 118140960795 + 873162 * 2 ^ 59
def prefixEnd_873162 : Nat := 4983230072969 + 3 ^ 40 * 873162 * 2
def baseEnd_873162 : Nat := 149450598413739327786469

theorem tailTrace_873162 : CollatzResearch.WordTrace tailWord_873162 prefixEnd_873162 149450598413739327786469 := by
  unfold tailWord_873162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961708615672668260581435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21231222975127115361550493 7961708615672668260581435)
  ·
    refine ⟨11942562923509002390872153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7961708615672668260581435 11942562923509002390872153)
    ·
      refine ⟨8956922192631751793154115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11942562923509002390872153 8956922192631751793154115)
      ·
        refine ⟨13435383288947627689731173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956922192631751793154115 13435383288947627689731173)
        ·
          refine ⟨2519134366677680191824595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13435383288947627689731173 2519134366677680191824595)
          ·
            refine ⟨3778701550016520287736893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519134366677680191824595 3778701550016520287736893)
            ·
              refine ⟨1417013081256195107901335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3778701550016520287736893 1417013081256195107901335)
              ·
                refine ⟨2125519621884292661852003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417013081256195107901335 2125519621884292661852003)
                ·
                  refine ⟨3188279432826438992778005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125519621884292661852003 3188279432826438992778005)
                  ·
                    refine ⟨149450598413739327786469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3188279432826438992778005 149450598413739327786469)
                    ·
                      rfl

theorem cell23_873162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_873162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873162 prefixEnd_873162 := by exact prefixLift 873162
  have htrace : WordTrace (prefixWord ++ tailWord_873162) baseStart_873162 baseEnd_873162 := by
    simpa [prefixWord, tailWord_873162, baseEnd_873162] using wordTrace_append hprefix tailTrace_873162
  have hstable : (prefixWord ++ tailWord_873162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873162).length < 2 ^ (prefixWord ++ tailWord_873162).sum := by decide
  have hdescent : baseEnd_873162 < baseStart_873162 := by decide
  rcases family_descends (prefixWord ++ tailWord_873162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873169 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 3, 2, 2]
def baseStart_873169 : Nat := 118140960795 + 873169 * 2 ^ 59
def prefixEnd_873169 : Nat := 4983230072969 + 3 ^ 40 * 873169 * 2
def baseEnd_873169 : Nat := 448355389605799455971875

theorem tailTrace_873169 : CollatzResearch.WordTrace tailWord_873169 prefixEnd_873169 448355389605799455971875 := by
  unfold tailWord_873169
  simp only [CollatzResearch.WordTrace]
  refine ⟨31847089773665313237830561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21231393182443542158553707 31847089773665313237830561)
  ·
    refine ⟨23885317330248984928372921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31847089773665313237830561 23885317330248984928372921)
    ·
      refine ⟨17913987997686738696279691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23885317330248984928372921 17913987997686738696279691)
      ·
        refine ⟨26870981996530108044419537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17913987997686738696279691 26870981996530108044419537)
        ·
          refine ⟨20153236497397581033314653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26870981996530108044419537 20153236497397581033314653)
          ·
            refine ⟨7557463686524092887492995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20153236497397581033314653 7557463686524092887492995)
            ·
              refine ⟨11336195529786139331239493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557463686524092887492995 11336195529786139331239493)
              ·
                refine ⟨2125536661834901124607405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11336195529786139331239493 2125536661834901124607405)
                ·
                  refine ⟨797076248188087921727777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2125536661834901124607405 797076248188087921727777)
                  ·
                    refine ⟨597807186141065941295833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 797076248188087921727777 597807186141065941295833)
                    ·
                      refine ⟨448355389605799455971875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 597807186141065941295833 448355389605799455971875)
                      ·
                        rfl

theorem cell23_873169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_873169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873169 prefixEnd_873169 := by exact prefixLift 873169
  have htrace : WordTrace (prefixWord ++ tailWord_873169) baseStart_873169 baseEnd_873169 := by
    simpa [prefixWord, tailWord_873169, baseEnd_873169] using wordTrace_append hprefix tailTrace_873169
  have hstable : (prefixWord ++ tailWord_873169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873169).length < 2 ^ (prefixWord ++ tailWord_873169).sum := by decide
  have hdescent : baseEnd_873169 < baseStart_873169 := by decide
  rcases family_descends (prefixWord ++ tailWord_873169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873175 : List Nat := [1, 1, 3, 2, 1, 5, 1, 9]
def baseStart_873175 : Nat := 118140960795 + 873175 * 2 ^ 59
def prefixEnd_873175 : Nat := 4983230072969 + 3 ^ 40 * 873175 * 2
def baseEnd_873175 : Nat := 16605869277397275277661

theorem tailTrace_873175 : CollatzResearch.WordTrace tailWord_873175 prefixEnd_873175 16605869277397275277661 := by
  unfold tailWord_873175
  simp only [CollatzResearch.WordTrace]
  refine ⟨31847308611643576262548979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21231539074429050841699319 31847308611643576262548979)
  ·
    refine ⟨47770962917465364393823469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31847308611643576262548979 47770962917465364393823469)
    ·
      refine ⟨17914111094049511647683801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47770962917465364393823469 17914111094049511647683801)
      ·
        refine ⟨13435583320537133735762851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17914111094049511647683801 13435583320537133735762851)
        ·
          refine ⟨20153374980805700603644277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13435583320537133735762851 20153374980805700603644277)
          ·
            refine ⟨1889378904450534431591651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20153374980805700603644277 1889378904450534431591651)
            ·
              refine ⟨2834068356675801647387477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889378904450534431591651 2834068356675801647387477)
              ·
                refine ⟨16605869277397275277661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2834068356675801647387477 16605869277397275277661)
                ·
                  rfl

theorem cell23_873175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 9].length) (baseStart_873175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873175 prefixEnd_873175 := by exact prefixLift 873175
  have htrace : WordTrace (prefixWord ++ tailWord_873175) baseStart_873175 baseEnd_873175 := by
    simpa [prefixWord, tailWord_873175, baseEnd_873175] using wordTrace_append hprefix tailTrace_873175
  have hstable : (prefixWord ++ tailWord_873175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873175).length < 2 ^ (prefixWord ++ tailWord_873175).sum := by decide
  have hdescent : baseEnd_873175 < baseStart_873175 := by decide
  rcases family_descends (prefixWord ++ tailWord_873175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873180 : List Nat := [2, 2, 5, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_873180 : Nat := 118140960795 + 873180 * 2 ^ 59
def prefixEnd_873180 : Nat := 4983230072969 + 3 ^ 40 * 873180 * 2
def baseEnd_873180 : Nat := 448361037892998912934325

theorem tailTrace_873180 : CollatzResearch.WordTrace tailWord_873180 prefixEnd_873180 448361037892998912934325 := by
  unfold tailWord_873180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15923745488312731058240497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21231660651083641410987329 15923745488312731058240497)
  ·
    refine ⟨11942809116234548293680373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15923745488312731058240497 11942809116234548293680373)
    ·
      refine ⟨1119638354646988902532535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11942809116234548293680373 1119638354646988902532535)
      ·
        refine ⟨1679457531970483353798803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119638354646988902532535 1679457531970483353798803)
        ·
          refine ⟨2519186297955725030698205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679457531970483353798803 2519186297955725030698205)
          ·
            refine ⟨944694861733396886511827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2519186297955725030698205 944694861733396886511827)
            ·
              refine ⟨1417042292600095329767741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944694861733396886511827 1417042292600095329767741)
              ·
                refine ⟨531390859725035748662903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417042292600095329767741 531390859725035748662903)
                ·
                  refine ⟨797086289587553622994355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531390859725035748662903 797086289587553622994355)
                  ·
                    refine ⟨1195629434381330434491533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 797086289587553622994355 1195629434381330434491533)
                    ·
                      refine ⟨448361037892998912934325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1195629434381330434491533 448361037892998912934325)
                      ·
                        rfl

theorem cell23_873180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_873180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873180 prefixEnd_873180 := by exact prefixLift 873180
  have htrace : WordTrace (prefixWord ++ tailWord_873180) baseStart_873180 baseEnd_873180 := by
    simpa [prefixWord, tailWord_873180, baseEnd_873180] using wordTrace_append hprefix tailTrace_873180
  have hstable : (prefixWord ++ tailWord_873180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873180).length < 2 ^ (prefixWord ++ tailWord_873180).sum := by decide
  have hdescent : baseEnd_873180 < baseStart_873180 := by decide
  rcases family_descends (prefixWord ++ tailWord_873180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873189 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_873189 : Nat := 118140960795 + 873189 * 2 ^ 59
def prefixEnd_873189 : Nat := 4983230072969 + 3 ^ 40 * 873189 * 2
def baseEnd_873189 : Nat := 448365659218889377721783

theorem tailTrace_873189 : CollatzResearch.WordTrace tailWord_873189 prefixEnd_873189 448365659218889377721783 := by
  unfold tailWord_873189
  simp only [CollatzResearch.WordTrace]
  refine ⟨31847819233592856653558621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21231879489061904435705747 31847819233592856653558621)
  ·
    refine ⟨11942932212597321245084483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31847819233592856653558621 11942932212597321245084483)
    ·
      refine ⟨17914398318895981867626725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11942932212597321245084483 17914398318895981867626725)
      ·
        refine ⟨3358949684792996600180011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17914398318895981867626725 3358949684792996600180011)
        ·
          refine ⟨5038424527189494900270017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358949684792996600180011 5038424527189494900270017)
          ·
            refine ⟨3778818395392121175202513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5038424527189494900270017 3778818395392121175202513)
            ·
              refine ⟨2834113796544090881401885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3778818395392121175202513 2834113796544090881401885)
              ·
                refine ⟨1062792673704034080525707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2834113796544090881401885 1062792673704034080525707)
                ·
                  refine ⟨1594189010556051120788561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062792673704034080525707 1594189010556051120788561)
                  ·
                    refine ⟨1195641757917038340591421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1594189010556051120788561 1195641757917038340591421)
                    ·
                      refine ⟨448365659218889377721783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1195641757917038340591421 448365659218889377721783)
                      ·
                        rfl

theorem cell23_873189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_873189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873189 prefixEnd_873189 := by exact prefixLift 873189
  have htrace : WordTrace (prefixWord ++ tailWord_873189) baseStart_873189 baseEnd_873189 := by
    simpa [prefixWord, tailWord_873189, baseEnd_873189] using wordTrace_append hprefix tailTrace_873189
  have hstable : (prefixWord ++ tailWord_873189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873189).length < 2 ^ (prefixWord ++ tailWord_873189).sum := by decide
  have hdescent : baseEnd_873189 < baseStart_873189 := by decide
  rcases family_descends (prefixWord ++ tailWord_873189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873192 : List Nat := [2, 1, 4, 1, 4, 2, 9]
def baseStart_873192 : Nat := 118140960795 + 873192 * 2 ^ 59
def prefixEnd_873192 : Nat := 4983230072969 + 3 ^ 40 * 873192 * 2
def baseEnd_873192 : Nat := 5535397526677195876349

theorem tailTrace_873192 : CollatzResearch.WordTrace tailWord_873192 prefixEnd_873192 5535397526677195876349 := by
  unfold tailWord_873192
  simp only [CollatzResearch.WordTrace]
  refine ⟨15923964326290994082958915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21231952435054658777278553 15923964326290994082958915)
  ·
    refine ⟨23885946489436491124438373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15923964326290994082958915 23885946489436491124438373)
    ·
      refine ⟨4478614966769342085832195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23885946489436491124438373 4478614966769342085832195)
      ·
        refine ⟨6717922450154013128748293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478614966769342085832195 6717922450154013128748293)
        ·
          refine ⟨1259610459403877461640305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6717922450154013128748293 1259610459403877461640305)
          ·
            refine ⟨944707844552908096230229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259610459403877461640305 944707844552908096230229)
            ·
              refine ⟨5535397526677195876349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 944707844552908096230229 5535397526677195876349)
              ·
                rfl

theorem cell23_873192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 9].length) (baseStart_873192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873192 prefixEnd_873192 := by exact prefixLift 873192
  have htrace : WordTrace (prefixWord ++ tailWord_873192) baseStart_873192 baseEnd_873192 := by
    simpa [prefixWord, tailWord_873192, baseEnd_873192] using wordTrace_append hprefix tailTrace_873192
  have hstable : (prefixWord ++ tailWord_873192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873192).length < 2 ^ (prefixWord ++ tailWord_873192).sum := by decide
  have hdescent : baseEnd_873192 < baseStart_873192 := by decide
  rcases family_descends (prefixWord ++ tailWord_873192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873272 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_873272 : Nat := 118140960795 + 873272 * 2 ^ 59
def prefixEnd_873272 : Nat := 4983230072969 + 3 ^ 40 * 873272 * 2
def baseEnd_873272 : Nat := 448408278113212552983901

theorem tailTrace_873272 : CollatzResearch.WordTrace tailWord_873272 prefixEnd_873272 448408278113212552983901 := by
  unfold tailWord_873272
  simp only [CollatzResearch.WordTrace]
  refine ⟨15925423246146080914415035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21233897661528107885886713 15925423246146080914415035)
  ·
    refine ⟨23888134869219121371622553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15925423246146080914415035 23888134869219121371622553)
    ·
      refine ⟨17916101151914341028716915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23888134869219121371622553 17916101151914341028716915)
      ·
        refine ⟨26874151727871511543075373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17916101151914341028716915 26874151727871511543075373)
        ·
          refine ⟨10077806897951816828653265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26874151727871511543075373 10077806897951816828653265)
          ·
            refine ⟨7558355173463862621489949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10077806897951816828653265 7558355173463862621489949)
            ·
              refine ⟨2834383190048948483058731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7558355173463862621489949 2834383190048948483058731)
              ·
                refine ⟨4251574785073422724588097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834383190048948483058731 4251574785073422724588097)
                ·
                  refine ⟨3188681088805067043441073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4251574785073422724588097 3188681088805067043441073)
                  ·
                    refine ⟨2391510816603800282580805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3188681088805067043441073 2391510816603800282580805)
                    ·
                      refine ⟨448408278113212552983901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2391510816603800282580805 448408278113212552983901)
                      ·
                        rfl

theorem cell23_873272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_873272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873272 prefixEnd_873272 := by exact prefixLift 873272
  have htrace : WordTrace (prefixWord ++ tailWord_873272) baseStart_873272 baseEnd_873272 := by
    simpa [prefixWord, tailWord_873272, baseEnd_873272] using wordTrace_append hprefix tailTrace_873272
  have hstable : (prefixWord ++ tailWord_873272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873272).length < 2 ^ (prefixWord ++ tailWord_873272).sum := by decide
  have hdescent : baseEnd_873272 < baseStart_873272 := by decide
  rcases family_descends (prefixWord ++ tailWord_873272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873312 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 4, 5]
def baseStart_873312 : Nat := 118140960795 + 873312 * 2 ^ 59
def prefixEnd_873312 : Nat := 4983230072969 + 3 ^ 40 * 873312 * 2
def baseEnd_873312 : Nat := 149476272446464132161239

theorem tailTrace_873312 : CollatzResearch.WordTrace tailWord_873312 prefixEnd_873312 149476272446464132161239 := by
  unfold tailWord_873312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15926152706073624330143095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21234870274764832440190793 15926152706073624330143095)
  ·
    refine ⟨23889229059110436495214643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15926152706073624330143095 23889229059110436495214643)
    ·
      refine ⟨35833843588665654742821965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23889229059110436495214643 35833843588665654742821965)
      ·
        refine ⟨13437691345749620528558237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35833843588665654742821965 13437691345749620528558237)
        ·
          refine ⟨5039134254656107698209339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13437691345749620528558237 5039134254656107698209339)
          ·
            refine ⟨7558701381984161547314009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039134254656107698209339 7558701381984161547314009)
            ·
              refine ⟨5669026036488121160485507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7558701381984161547314009 5669026036488121160485507)
              ·
                refine ⟨8503539054732181740728261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669026036488121160485507 8503539054732181740728261)
                ·
                  refine ⟨1594413572762284076386549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8503539054732181740728261 1594413572762284076386549)
                  ·
                    refine ⟨149476272446464132161239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1594413572762284076386549 149476272446464132161239)
                    ·
                      rfl

theorem cell23_873312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_873312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873312 prefixEnd_873312 := by exact prefixLift 873312
  have htrace : WordTrace (prefixWord ++ tailWord_873312) baseStart_873312 baseEnd_873312 := by
    simpa [prefixWord, tailWord_873312, baseEnd_873312] using wordTrace_append hprefix tailTrace_873312
  have hstable : (prefixWord ++ tailWord_873312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873312).length < 2 ^ (prefixWord ++ tailWord_873312).sum := by decide
  have hdescent : baseEnd_873312 < baseStart_873312 := by decide
  rcases family_descends (prefixWord ++ tailWord_873312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873376 : List Nat := [2, 1, 1, 4, 1, 1, 2, 6, 1, 4]
def baseStart_873376 : Nat := 118140960795 + 873376 * 2 ^ 59
def prefixEnd_873376 : Nat := 4983230072969 + 3 ^ 40 * 873376 * 2
def baseEnd_873376 : Nat := 149487226700426715361141

theorem tailTrace_873376 : CollatzResearch.WordTrace tailWord_873376 prefixEnd_873376 149487226700426715361141 := by
  unfold tailWord_873376
  simp only [CollatzResearch.WordTrace]
  refine ⟨15927319841957693795307991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21236426455943591727077321 15927319841957693795307991)
  ·
    refine ⟨23890979762936540692961987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15927319841957693795307991 23890979762936540692961987)
    ·
      refine ⟨35836469644404811039442981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23890979762936540692961987 35836469644404811039442981)
      ·
        refine ⟨6719338058325902069895559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35836469644404811039442981 6719338058325902069895559)
        ·
          refine ⟨10079007087488853104843339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6719338058325902069895559 10079007087488853104843339)
          ·
            refine ⟨15118510631233279657265009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10079007087488853104843339 15118510631233279657265009)
            ·
              refine ⟨11338882973424959742948757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15118510631233279657265009 11338882973424959742948757)
              ·
                refine ⟨531510139379294987950723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11338882973424959742948757 531510139379294987950723)
                ·
                  refine ⟨797265209068942481926085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531510139379294987950723 797265209068942481926085)
                  ·
                    refine ⟨149487226700426715361141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797265209068942481926085 149487226700426715361141)
                    ·
                      rfl

theorem cell23_873376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 4].length) (baseStart_873376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873376 prefixEnd_873376 := by exact prefixLift 873376
  have htrace : WordTrace (prefixWord ++ tailWord_873376) baseStart_873376 baseEnd_873376 := by
    simpa [prefixWord, tailWord_873376, baseEnd_873376] using wordTrace_append hprefix tailTrace_873376
  have hstable : (prefixWord ++ tailWord_873376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873376).length < 2 ^ (prefixWord ++ tailWord_873376).sum := by decide
  have hdescent : baseEnd_873376 < baseStart_873376 := by decide
  rcases family_descends (prefixWord ++ tailWord_873376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873472 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_873472 : Nat := 118140960795 + 873472 * 2 ^ 59
def prefixEnd_873472 : Nat := 4983230072969 + 3 ^ 40 * 873472 * 2
def baseEnd_873472 : Nat := 448510974244111770482981

theorem tailTrace_873472 : CollatzResearch.WordTrace tailWord_873472 prefixEnd_873472 448510974244111770482981 := by
  unfold tailWord_873472
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929070545783797993055335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21238760727711730657407113 15929070545783797993055335)
  ·
    refine ⟨23893605818675696989583003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15929070545783797993055335 23893605818675696989583003)
    ·
      refine ⟨35840408728013545484374505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23893605818675696989583003 35840408728013545484374505)
      ·
        refine ⟨26880306546010159113280879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35840408728013545484374505 26880306546010159113280879)
        ·
          refine ⟨40320459819015238669921319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26880306546010159113280879 40320459819015238669921319)
          ·
            refine ⟨60480689728522858004881979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40320459819015238669921319 60480689728522858004881979)
            ·
              refine ⟨90721034592784287007322969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60480689728522858004881979 90721034592784287007322969)
              ·
                refine ⟨68040775944588215255492227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90721034592784287007322969 68040775944588215255492227)
                ·
                  refine ⟨102061163916882322883238341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68040775944588215255492227 102061163916882322883238341)
                  ·
                    refine ⟨19136468234415435540607189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102061163916882322883238341 19136468234415435540607189)
                    ·
                      refine ⟨448510974244111770482981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19136468234415435540607189 448510974244111770482981)
                      ·
                        rfl

theorem cell23_873472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_873472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873472 prefixEnd_873472 := by exact prefixLift 873472
  have htrace : WordTrace (prefixWord ++ tailWord_873472) baseStart_873472 baseEnd_873472 := by
    simpa [prefixWord, tailWord_873472, baseEnd_873472] using wordTrace_append hprefix tailTrace_873472
  have hstable : (prefixWord ++ tailWord_873472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873472).length < 2 ^ (prefixWord ++ tailWord_873472).sum := by decide
  have hdescent : baseEnd_873472 < baseStart_873472 := by decide
  rcases family_descends (prefixWord ++ tailWord_873472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873473 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_873473 : Nat := 118140960795 + 873473 * 2 ^ 59
def prefixEnd_873473 : Nat := 4983230072969 + 3 ^ 40 * 873473 * 2
def baseEnd_873473 : Nat := 448511487724766266570477

theorem tailTrace_873473 : CollatzResearch.WordTrace tailWord_873473 prefixEnd_873473 448511487724766266570477 := by
  unfold tailWord_873473
  simp only [CollatzResearch.WordTrace]
  refine ⟨31858177564563973156897073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21238785043042648771264715 31858177564563973156897073)
  ·
    refine ⟨23893633173422979867672805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31858177564563973156897073 23893633173422979867672805)
    ·
      refine ⟨4480056220016808725188651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23893633173422979867672805 4480056220016808725188651)
      ·
        refine ⟨6720084330025213087782977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480056220016808725188651 6720084330025213087782977)
        ·
          refine ⟨5040063247518909815837233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6720084330025213087782977 5040063247518909815837233)
          ·
            refine ⟨3780047435639182361877925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5040063247518909815837233 3780047435639182361877925)
            ·
              refine ⟨708758894182346692852111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3780047435639182361877925 708758894182346692852111)
              ·
                refine ⟨1063138341273520039278167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708758894182346692852111 1063138341273520039278167)
                ·
                  refine ⟨1594707511910280058917251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063138341273520039278167 1594707511910280058917251)
                  ·
                    refine ⟨2392061267865420088375877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1594707511910280058917251 2392061267865420088375877)
                    ·
                      refine ⟨448511487724766266570477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2392061267865420088375877 448511487724766266570477)
                      ·
                        rfl

theorem cell23_873473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_873473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873473 prefixEnd_873473 := by exact prefixLift 873473
  have htrace : WordTrace (prefixWord ++ tailWord_873473) baseStart_873473 baseEnd_873473 := by
    simpa [prefixWord, tailWord_873473, baseEnd_873473] using wordTrace_append hprefix tailTrace_873473
  have hstable : (prefixWord ++ tailWord_873473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873473).length < 2 ^ (prefixWord ++ tailWord_873473).sum := by decide
  have hdescent : baseEnd_873473 < baseStart_873473 := by decide
  rcases family_descends (prefixWord ++ tailWord_873473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873483 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 2, 4]
def baseStart_873483 : Nat := 118140960795 + 873483 * 2 ^ 59
def prefixEnd_873483 : Nat := 4983230072969 + 3 ^ 40 * 873483 * 2
def baseEnd_873483 : Nat := 149505540843770409148477

theorem tailTrace_873483 : CollatzResearch.WordTrace tailWord_873483 prefixEnd_873483 149505540843770409148477 := by
  unfold tailWord_873483
  simp only [CollatzResearch.WordTrace]
  refine ⟨31858542294527744864761103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21239028196351829909840735 31858542294527744864761103)
  ·
    refine ⟨47787813441791617297141655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31858542294527744864761103 47787813441791617297141655)
    ·
      refine ⟨71681720162687425945712483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47787813441791617297141655 71681720162687425945712483)
      ·
        refine ⟨107522580244031138918568725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71681720162687425945712483 107522580244031138918568725)
        ·
          refine ⟨5040120948938959636807909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107522580244031138918568725 5040120948938959636807909)
          ·
            refine ⟨945022677926054931901483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5040120948938959636807909 945022677926054931901483)
            ·
              refine ⟨1417534016889082397852225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945022677926054931901483 1417534016889082397852225)
              ·
                refine ⟨1063150512666811798389169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417534016889082397852225 1063150512666811798389169)
                ·
                  refine ⟨797362884500108848791877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063150512666811798389169 797362884500108848791877)
                  ·
                    refine ⟨149505540843770409148477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797362884500108848791877 149505540843770409148477)
                    ·
                      rfl

theorem cell23_873483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 4].length) (baseStart_873483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873483 prefixEnd_873483 := by exact prefixLift 873483
  have htrace : WordTrace (prefixWord ++ tailWord_873483) baseStart_873483 baseEnd_873483 := by
    simpa [prefixWord, tailWord_873483, baseEnd_873483] using wordTrace_append hprefix tailTrace_873483
  have hstable : (prefixWord ++ tailWord_873483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873483).length < 2 ^ (prefixWord ++ tailWord_873483).sum := by decide
  have hdescent : baseEnd_873483 < baseStart_873483 := by decide
  rcases family_descends (prefixWord ++ tailWord_873483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873489 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_873489 : Nat := 118140960795 + 873489 * 2 ^ 59
def prefixEnd_873489 : Nat := 4983230072969 + 3 ^ 40 * 873489 * 2
def baseEnd_873489 : Nat := 448519703415238203970403

theorem tailTrace_873489 : CollatzResearch.WordTrace tailWord_873489 prefixEnd_873489 448519703415238203970403 := by
  unfold tailWord_873489
  simp only [CollatzResearch.WordTrace]
  refine ⟨31858761132506007889479521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21239174088337338592986347 31858761132506007889479521)
  ·
    refine ⟨23894070849379505917109641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31858761132506007889479521 23894070849379505917109641)
    ·
      refine ⟨17920553137034629437832231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23894070849379505917109641 17920553137034629437832231)
      ·
        refine ⟨26880829705551944156748347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17920553137034629437832231 26880829705551944156748347)
        ·
          refine ⟨40321244558327916235122521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26880829705551944156748347 40321244558327916235122521)
          ·
            refine ⟨30240933418745937176341891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40321244558327916235122521 30240933418745937176341891)
            ·
              refine ⟨45361400128118905764512837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30240933418745937176341891 45361400128118905764512837)
              ·
                refine ⟨8505262524022294830846157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45361400128118905764512837 8505262524022294830846157)
                ·
                  refine ⟨3189473446508360561567309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8505262524022294830846157 3189473446508360561567309)
                  ·
                    refine ⟨1196052542440635210587741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189473446508360561567309 1196052542440635210587741)
                    ·
                      refine ⟨448519703415238203970403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196052542440635210587741 448519703415238203970403)
                      ·
                        rfl

theorem cell23_873489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_873489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873489 prefixEnd_873489 := by exact prefixLift 873489
  have htrace : WordTrace (prefixWord ++ tailWord_873489) baseStart_873489 baseEnd_873489 := by
    simpa [prefixWord, tailWord_873489, baseEnd_873489] using wordTrace_append hprefix tailTrace_873489
  have hstable : (prefixWord ++ tailWord_873489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873489).length < 2 ^ (prefixWord ++ tailWord_873489).sum := by decide
  have hdescent : baseEnd_873489 < baseStart_873489 := by decide
  rcases family_descends (prefixWord ++ tailWord_873489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873500 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_873500 : Nat := 118140960795 + 873500 * 2 ^ 59
def prefixEnd_873500 : Nat := 4983230072969 + 3 ^ 40 * 873500 * 2
def baseEnd_873500 : Nat := 149508450567479220310951

theorem tailTrace_873500 : CollatzResearch.WordTrace tailWord_873500 prefixEnd_873500 149508450567479220310951 := by
  unfold tailWord_873500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929581167733078384064977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21239441556977437845419969 15929581167733078384064977)
  ·
    refine ⟨11947185875799808788048733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15929581167733078384064977 11947185875799808788048733)
    ·
      refine ⟨4480194703424928295518275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11947185875799808788048733 4480194703424928295518275)
      ·
        refine ⟨6720292055137392443277413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480194703424928295518275 6720292055137392443277413)
        ·
          refine ⟨1260054760338261083114515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6720292055137392443277413 1260054760338261083114515)
          ·
            refine ⟨1890082140507391624671773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260054760338261083114515 1890082140507391624671773)
            ·
              refine ⟨708780802690271859251915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1890082140507391624671773 708780802690271859251915)
              ·
                refine ⟨1063171204035407788877873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708780802690271859251915 1063171204035407788877873)
                ·
                  refine ⟨797378403026555841658405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063171204035407788877873 797378403026555841658405)
                  ·
                    refine ⟨149508450567479220310951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797378403026555841658405 149508450567479220310951)
                    ·
                      rfl

theorem cell23_873500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_873500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873500 prefixEnd_873500 := by exact prefixLift 873500
  have htrace : WordTrace (prefixWord ++ tailWord_873500) baseStart_873500 baseEnd_873500 := by
    simpa [prefixWord, tailWord_873500, baseEnd_873500] using wordTrace_append hprefix tailTrace_873500
  have hstable : (prefixWord ++ tailWord_873500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873500).length < 2 ^ (prefixWord ++ tailWord_873500).sum := by decide
  have hdescent : baseEnd_873500 < baseStart_873500 := by decide
  rcases family_descends (prefixWord ++ tailWord_873500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873524 : List Nat := [2, 5, 1, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_873524 : Nat := 118140960795 + 873524 * 2 ^ 59
def prefixEnd_873524 : Nat := 4983230072969 + 3 ^ 40 * 873524 * 2
def baseEnd_873524 : Nat := 448537675238145567032743

theorem tailTrace_873524 : CollatzResearch.WordTrace tailWord_873524 prefixEnd_873524 448537675238145567032743 := by
  unfold tailWord_873524
  simp only [CollatzResearch.WordTrace]
  refine ⟨15930018843689604433501813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21240025124919472578002417 15930018843689604433501813)
  ·
    refine ⟨1493439266595900415640795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15930018843689604433501813 1493439266595900415640795)
    ·
      refine ⟨2240158899893850623461193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493439266595900415640795 2240158899893850623461193)
      ·
        refine ⟨1680119174920387967595895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240158899893850623461193 1680119174920387967595895)
        ·
          refine ⟨2520178762380581951393843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680119174920387967595895 2520178762380581951393843)
          ·
            refine ⟨3780268143570872927090765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520178762380581951393843 3780268143570872927090765)
            ·
              refine ⟨1417600553839077347659037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3780268143570872927090765 1417600553839077347659037)
              ·
                refine ⟨531600207689654005372139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417600553839077347659037 531600207689654005372139)
                ·
                  refine ⟨797400311534481008058209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531600207689654005372139 797400311534481008058209)
                  ·
                    refine ⟨598050233650860756043657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 797400311534481008058209 598050233650860756043657)
                    ·
                      refine ⟨448537675238145567032743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598050233650860756043657 448537675238145567032743)
                      ·
                        rfl

theorem cell23_873524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_873524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873524 prefixEnd_873524 := by exact prefixLift 873524
  have htrace : WordTrace (prefixWord ++ tailWord_873524) baseStart_873524 baseEnd_873524 := by
    simpa [prefixWord, tailWord_873524, baseEnd_873524] using wordTrace_append hprefix tailTrace_873524
  have hstable : (prefixWord ++ tailWord_873524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873524).length < 2 ^ (prefixWord ++ tailWord_873524).sum := by decide
  have hdescent : baseEnd_873524 < baseStart_873524 := by decide
  rcases family_descends (prefixWord ++ tailWord_873524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873559 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_873559 : Nat := 118140960795 + 873559 * 2 ^ 59
def prefixEnd_873559 : Nat := 4983230072969 + 3 ^ 40 * 873559 * 2
def baseEnd_873559 : Nat := 448555647061052930095081

theorem tailTrace_873559 : CollatzResearch.WordTrace tailWord_873559 prefixEnd_873559 448555647061052930095081 := by
  unfold tailWord_873559
  simp only [CollatzResearch.WordTrace]
  refine ⟨31861314242252409844527731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21240876161501606563018487 31861314242252409844527731)
  ·
    refine ⟨47791971363378614766791597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31861314242252409844527731 47791971363378614766791597)
    ·
      refine ⟨17921989261266980537546849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47791971363378614766791597 17921989261266980537546849)
      ·
        refine ⟨13441491945950235403160137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17921989261266980537546849 13441491945950235403160137)
        ·
          refine ⟨10081118959462676552370103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13441491945950235403160137 10081118959462676552370103)
          ·
            refine ⟨15121678439194014828555155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081118959462676552370103 15121678439194014828555155)
            ·
              refine ⟨22682517658791022242832733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15121678439194014828555155 22682517658791022242832733)
              ·
                refine ⟨8505944122046633341062275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22682517658791022242832733 8505944122046633341062275)
                ·
                  refine ⟨12758916183069950011593413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8505944122046633341062275 12758916183069950011593413)
                  ·
                    refine ⟨2392296784325615627173765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12758916183069950011593413 2392296784325615627173765)
                    ·
                      refine ⟨448555647061052930095081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2392296784325615627173765 448555647061052930095081)
                      ·
                        rfl

theorem cell23_873559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_873559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873559 prefixEnd_873559 := by exact prefixLift 873559
  have htrace : WordTrace (prefixWord ++ tailWord_873559) baseStart_873559 baseEnd_873559 := by
    simpa [prefixWord, tailWord_873559, baseEnd_873559] using wordTrace_append hprefix tailTrace_873559
  have hstable : (prefixWord ++ tailWord_873559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873559).length < 2 ^ (prefixWord ++ tailWord_873559).sum := by decide
  have hdescent : baseEnd_873559 < baseStart_873559 := by decide
  rcases family_descends (prefixWord ++ tailWord_873559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873569 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 7]
def baseStart_873569 : Nat := 118140960795 + 873569 * 2 ^ 59
def prefixEnd_873569 : Nat := 4983230072969 + 3 ^ 40 * 873569 * 2
def baseEnd_873569 : Nat := 49840086874177543441115

theorem tailTrace_873569 : CollatzResearch.WordTrace tailWord_873569 prefixEnd_873569 49840086874177543441115 := by
  unfold tailWord_873569
  simp only [CollatzResearch.WordTrace]
  refine ⟨31861678972216181552391761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21241119314810787701594507 31861678972216181552391761)
  ·
    refine ⟨23896259229162136164293821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31861678972216181552391761 23896259229162136164293821)
    ·
      refine ⟨8961097210935801061610183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23896259229162136164293821 8961097210935801061610183)
      ·
        refine ⟨13441645816403701592415275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8961097210935801061610183 13441645816403701592415275)
        ·
          refine ⟨20162468724605552388622913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13441645816403701592415275 20162468724605552388622913)
          ·
            refine ⟨15121851543454164291467185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20162468724605552388622913 15121851543454164291467185)
            ·
              refine ⟨11341388657590623218600389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15121851543454164291467185 11341388657590623218600389)
              ·
                refine ⟨2126510373298241853487573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11341388657590623218600389 2126510373298241853487573)
                ·
                  refine ⟨49840086874177543441115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2126510373298241853487573 49840086874177543441115)
                  ·
                    rfl

theorem cell23_873569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 7].length) (baseStart_873569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873569 prefixEnd_873569 := by exact prefixLift 873569
  have htrace : WordTrace (prefixWord ++ tailWord_873569) baseStart_873569 baseEnd_873569 := by
    simpa [prefixWord, tailWord_873569, baseEnd_873569] using wordTrace_append hprefix tailTrace_873569
  have hstable : (prefixWord ++ tailWord_873569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873569).length < 2 ^ (prefixWord ++ tailWord_873569).sum := by decide
  have hdescent : baseEnd_873569 < baseStart_873569 := by decide
  rcases family_descends (prefixWord ++ tailWord_873569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873596 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_873596 : Nat := 118140960795 + 873596 * 2 ^ 59
def prefixEnd_873596 : Nat := 4983230072969 + 3 ^ 40 * 873596 * 2
def baseEnd_873596 : Nat := 448574645845269285332411

theorem tailTrace_873596 : CollatzResearch.WordTrace tailWord_873596 prefixEnd_873596 448574645845269285332411 := by
  unfold tailWord_873596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931331871559182581812321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21241775828745576775749761 15931331871559182581812321)
  ·
    refine ⟨11948498903669386936359241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15931331871559182581812321 11948498903669386936359241)
    ·
      refine ⟨8961374177752040202269431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11948498903669386936359241 8961374177752040202269431)
      ·
        refine ⟨13442061266628060303404147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8961374177752040202269431 13442061266628060303404147)
        ·
          refine ⟨20163091899942090455106221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13442061266628060303404147 20163091899942090455106221)
          ·
            refine ⟨7561159462478283920664833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20163091899942090455106221 7561159462478283920664833)
            ·
              refine ⟨5670869596858712940498625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7561159462478283920664833 5670869596858712940498625)
              ·
                refine ⟨4253152197644034705373969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5670869596858712940498625 4253152197644034705373969)
                ·
                  refine ⟨3189864148233026029030477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4253152197644034705373969 3189864148233026029030477)
                  ·
                    refine ⟨1196199055587384760886429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3189864148233026029030477 1196199055587384760886429)
                    ·
                      refine ⟨448574645845269285332411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196199055587384760886429 448574645845269285332411)
                      ·
                        rfl

theorem cell23_873596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_873596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873596 prefixEnd_873596 := by exact prefixLift 873596
  have htrace : WordTrace (prefixWord ++ tailWord_873596) baseStart_873596 baseEnd_873596 := by
    simpa [prefixWord, tailWord_873596, baseEnd_873596] using wordTrace_append hprefix tailTrace_873596
  have hstable : (prefixWord ++ tailWord_873596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873596).length < 2 ^ (prefixWord ++ tailWord_873596).sum := by decide
  have hdescent : baseEnd_873596 < baseStart_873596 := by decide
  rcases family_descends (prefixWord ++ tailWord_873596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873697 : List Nat := [1, 2, 3, 1, 3, 4, 1, 3, 1, 4]
def baseStart_873697 : Nat := 118140960795 + 873697 * 2 ^ 59
def prefixEnd_873697 : Nat := 4983230072969 + 3 ^ 40 * 873697 * 2
def baseEnd_873697 : Nat := 149542169130457796723149

theorem tailTrace_873697 : CollatzResearch.WordTrace tailWord_873697 prefixEnd_873697 149542169130457796723149 := by
  unfold tailWord_873697
  simp only [CollatzResearch.WordTrace]
  refine ⟨31866347515752459413051345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21244231677168306275367563 31866347515752459413051345)
  ·
    refine ⟨23899760636814344559788509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31866347515752459413051345 23899760636814344559788509)
    ·
      refine ⟨8962410238805379209920691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23899760636814344559788509 8962410238805379209920691)
      ·
        refine ⟨13443615358208068814881037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8962410238805379209920691 13443615358208068814881037)
        ·
          refine ⟨5041355759328025805580389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13443615358208068814881037 5041355759328025805580389)
          ·
            refine ⟨945254204874004838546323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5041355759328025805580389 945254204874004838546323)
            ·
              refine ⟨1417881307311007257819485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945254204874004838546323 1417881307311007257819485)
              ·
                refine ⟨531705490241627721682307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417881307311007257819485 531705490241627721682307)
                ·
                  refine ⟨797558235362441582523461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531705490241627721682307 797558235362441582523461)
                  ·
                    refine ⟨149542169130457796723149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797558235362441582523461 149542169130457796723149)
                    ·
                      rfl

theorem cell23_873697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_873697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873697 prefixEnd_873697 := by exact prefixLift 873697
  have htrace : WordTrace (prefixWord ++ tailWord_873697) baseStart_873697 baseEnd_873697 := by
    simpa [prefixWord, tailWord_873697, baseEnd_873697] using wordTrace_append hprefix tailTrace_873697
  have hstable : (prefixWord ++ tailWord_873697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873697).length < 2 ^ (prefixWord ++ tailWord_873697).sum := by decide
  have hdescent : baseEnd_873697 < baseStart_873697 := by decide
  rcases family_descends (prefixWord ++ tailWord_873697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873714 : List Nat := [3, 2, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_873714 : Nat := 118140960795 + 873714 * 2 ^ 59
def prefixEnd_873714 : Nat := 4983230072969 + 3 ^ 40 * 873714 * 2
def baseEnd_873714 : Nat := 149545078854166607885623

theorem tailTrace_873714 : CollatzResearch.WordTrace tailWord_873714 prefixEnd_873714 149545078854166607885623 := by
  unfold tailWord_873714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966741889172717829105049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21244645037793914210946797 7966741889172717829105049)
  ·
    refine ⟨5975056416879538371828787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7966741889172717829105049 5975056416879538371828787)
    ·
      refine ⟨8962584625319307557743181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5975056416879538371828787 8962584625319307557743181)
      ·
        refine ⟨3360969234494740334153693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8962584625319307557743181 3360969234494740334153693)
        ·
          refine ⟨1260363462935527625307635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3360969234494740334153693 1260363462935527625307635)
          ·
            refine ⟨1890545194403291437961453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260363462935527625307635 1890545194403291437961453)
            ·
              refine ⟨708954447901234289235545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1890545194403291437961453 708954447901234289235545)
              ·
                refine ⟨531715835925925716926659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708954447901234289235545 531715835925925716926659)
                ·
                  refine ⟨797573753888888575389989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531715835925925716926659 797573753888888575389989)
                  ·
                    refine ⟨149545078854166607885623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797573753888888575389989 149545078854166607885623)
                    ·
                      rfl

theorem cell23_873714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_873714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873714 prefixEnd_873714 := by exact prefixLift 873714
  have htrace : WordTrace (prefixWord ++ tailWord_873714) baseStart_873714 baseEnd_873714 := by
    simpa [prefixWord, tailWord_873714, baseEnd_873714] using wordTrace_append hprefix tailTrace_873714
  have hstable : (prefixWord ++ tailWord_873714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873714).length < 2 ^ (prefixWord ++ tailWord_873714).sum := by decide
  have hdescent : baseEnd_873714 < baseStart_873714 := by decide
  rcases family_descends (prefixWord ++ tailWord_873714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873740 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_873740 : Nat := 118140960795 + 873740 * 2 ^ 59
def prefixEnd_873740 : Nat := 4983230072969 + 3 ^ 40 * 873740 * 2
def baseEnd_873740 : Nat := 149549529019838907310583

theorem tailTrace_873740 : CollatzResearch.WordTrace tailWord_873740 prefixEnd_873740 149549529019838907310583 := by
  unfold tailWord_873740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15933957927298338878433337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21245277236397785171244449 15933957927298338878433337)
  ·
    refine ⟨11950468445473754158825003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15933957927298338878433337 11950468445473754158825003)
    ·
      refine ⟨17925702668210631238237505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11950468445473754158825003 17925702668210631238237505)
      ·
        refine ⟨13444277001157973428678129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17925702668210631238237505 13444277001157973428678129)
        ·
          refine ⟨10083207750868480071508597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13444277001157973428678129 10083207750868480071508597)
          ·
            refine ⟨945300726643920006703931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10083207750868480071508597 945300726643920006703931)
            ·
              refine ⟨1417951089965880010055897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945300726643920006703931 1417951089965880010055897)
              ·
                refine ⟨1063463317474410007541923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417951089965880010055897 1063463317474410007541923)
                ·
                  refine ⟨1595194976211615011312885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063463317474410007541923 1595194976211615011312885)
                  ·
                    refine ⟨149549529019838907310583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1595194976211615011312885 149549529019838907310583)
                    ·
                      rfl

theorem cell23_873740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_873740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873740 prefixEnd_873740 := by exact prefixLift 873740
  have htrace : WordTrace (prefixWord ++ tailWord_873740) baseStart_873740 baseEnd_873740 := by
    simpa [prefixWord, tailWord_873740, baseEnd_873740] using wordTrace_append hprefix tailTrace_873740
  have hstable : (prefixWord ++ tailWord_873740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873740).length < 2 ^ (prefixWord ++ tailWord_873740).sum := by decide
  have hdescent : baseEnd_873740 < baseStart_873740 := by decide
  rcases family_descends (prefixWord ++ tailWord_873740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873757 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_873757 : Nat := 118140960795 + 873757 * 2 ^ 59
def prefixEnd_873757 : Nat := 4983230072969 + 3 ^ 40 * 873757 * 2
def baseEnd_873757 : Nat := 149552438743547718473057

theorem tailTrace_873757 : CollatzResearch.WordTrace tailWord_873757 prefixEnd_873757 149552438743547718473057 := by
  unfold tailWord_873757
  simp only [CollatzResearch.WordTrace]
  refine ⟨31868535895535089660235525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21245690597023393106823683 31868535895535089660235525)
  ·
    refine ⟨5975350480412829311294161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31868535895535089660235525 5975350480412829311294161)
    ·
      refine ⟨4481512860309621983470621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5975350480412829311294161 4481512860309621983470621)
      ·
        refine ⟨1680567322616108243801483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4481512860309621983470621 1680567322616108243801483)
        ·
          refine ⟨2520850983924162365702225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680567322616108243801483 2520850983924162365702225)
          ·
            refine ⟨1890638237943121774276669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2520850983924162365702225 1890638237943121774276669)
            ·
              refine ⟨708989339228670665353751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1890638237943121774276669 708989339228670665353751)
              ·
                refine ⟨1063484008843005998030627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708989339228670665353751 1063484008843005998030627)
                ·
                  refine ⟨1595226013264508997045941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063484008843005998030627 1595226013264508997045941)
                  ·
                    refine ⟨149552438743547718473057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1595226013264508997045941 149552438743547718473057)
                    ·
                      rfl

theorem cell23_873757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_873757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873757 prefixEnd_873757 := by exact prefixLift 873757
  have htrace : WordTrace (prefixWord ++ tailWord_873757) baseStart_873757 baseEnd_873757 := by
    simpa [prefixWord, tailWord_873757, baseEnd_873757] using wordTrace_append hprefix tailTrace_873757
  have hstable : (prefixWord ++ tailWord_873757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873757).length < 2 ^ (prefixWord ++ tailWord_873757).sum := by decide
  have hdescent : baseEnd_873757 < baseStart_873757 := by decide
  rcases family_descends (prefixWord ++ tailWord_873757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873763 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 5]
def baseStart_873763 : Nat := 118140960795 + 873763 * 2 ^ 59
def prefixEnd_873763 : Nat := 4983230072969 + 3 ^ 40 * 873763 * 2
def baseEnd_873763 : Nat := 448660397114570131944143

theorem tailTrace_873763 : CollatzResearch.WordTrace tailWord_873763 prefixEnd_873763 448660397114570131944143 := by
  unfold tailWord_873763
  simp only [CollatzResearch.WordTrace]
  refine ⟨31868754733513352684953943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21245836489008901789969295 31868754733513352684953943)
  ·
    refine ⟨47803132100270029027430915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31868754733513352684953943 47803132100270029027430915)
    ·
      refine ⟨71704698150405043541146373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47803132100270029027430915 71704698150405043541146373)
      ·
        refine ⟨13444630903200945663964945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71704698150405043541146373 13444630903200945663964945)
        ·
          refine ⟨10083473177400709247973709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13444630903200945663964945 10083473177400709247973709)
          ·
            refine ⟨3781302441525265967990141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10083473177400709247973709 3781302441525265967990141)
            ·
              refine ⟨1417988415571974737996303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3781302441525265967990141 1417988415571974737996303)
              ·
                refine ⟨2126982623357962106994455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417988415571974737996303 2126982623357962106994455)
                ·
                  refine ⟨3190473935036943160491683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126982623357962106994455 3190473935036943160491683)
                  ·
                    refine ⟨4785710902555414740737525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3190473935036943160491683 4785710902555414740737525)
                    ·
                      refine ⟨448660397114570131944143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4785710902555414740737525 448660397114570131944143)
                      ·
                        rfl

theorem cell23_873763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_873763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873763 prefixEnd_873763 := by exact prefixLift 873763
  have htrace : WordTrace (prefixWord ++ tailWord_873763) baseStart_873763 baseEnd_873763 := by
    simpa [prefixWord, tailWord_873763, baseEnd_873763] using wordTrace_append hprefix tailTrace_873763
  have hstable : (prefixWord ++ tailWord_873763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873763).length < 2 ^ (prefixWord ++ tailWord_873763).sum := by decide
  have hdescent : baseEnd_873763 < baseStart_873763 := by decide
  rcases family_descends (prefixWord ++ tailWord_873763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873780 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_873780 : Nat := 118140960795 + 873780 * 2 ^ 59
def prefixEnd_873780 : Nat := 4983230072969 + 3 ^ 40 * 873780 * 2
def baseEnd_873780 : Nat := 448669126285696565431565

theorem tailTrace_873780 : CollatzResearch.WordTrace tailWord_873780 prefixEnd_873780 448669126285696565431565 := by
  unfold tailWord_873780
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934687387225882294161397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21246249849634509725548529 15934687387225882294161397)
  ·
    refine ⟨1493876942552426465077631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15934687387225882294161397 1493876942552426465077631)
    ·
      refine ⟨2240815413828639697616447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493876942552426465077631 2240815413828639697616447)
      ·
        refine ⟨3361223120742959546424671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240815413828639697616447 3361223120742959546424671)
        ·
          refine ⟨5041834681114439319637007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361223120742959546424671 5041834681114439319637007)
          ·
            refine ⟨7562752021671658979455511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5041834681114439319637007 7562752021671658979455511)
            ·
              refine ⟨11344128032507488469183267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562752021671658979455511 11344128032507488469183267)
              ·
                refine ⟨17016192048761232703774901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11344128032507488469183267 17016192048761232703774901)
                ·
                  refine ⟨1595268004571365565978897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17016192048761232703774901 1595268004571365565978897)
                  ·
                    refine ⟨1196451003428524174484173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1595268004571365565978897 1196451003428524174484173)
                    ·
                      refine ⟨448669126285696565431565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196451003428524174484173 448669126285696565431565)
                      ·
                        rfl

theorem cell23_873780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_873780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873780 prefixEnd_873780 := by exact prefixLift 873780
  have htrace : WordTrace (prefixWord ++ tailWord_873780) baseStart_873780 baseEnd_873780 := by
    simpa [prefixWord, tailWord_873780, baseEnd_873780] using wordTrace_append hprefix tailTrace_873780
  have hstable : (prefixWord ++ tailWord_873780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873780).length < 2 ^ (prefixWord ++ tailWord_873780).sum := by decide
  have hdescent : baseEnd_873780 < baseStart_873780 := by decide
  rcases family_descends (prefixWord ++ tailWord_873780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873790 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_873790 : Nat := 118140960795 + 873790 * 2 ^ 59
def prefixEnd_873790 : Nat := 4983230072969 + 3 ^ 40 * 873790 * 2
def baseEnd_873790 : Nat := 448674261092241526306519

theorem tailTrace_873790 : CollatzResearch.WordTrace tailWord_873790 prefixEnd_873790 448674261092241526306519 := by
  unfold tailWord_873790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983717438051942037023353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21246493002943690864124549 3983717438051942037023353)
  ·
    refine ⟨2987788078538956527767515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3983717438051942037023353 2987788078538956527767515)
    ·
      refine ⟨4481682117808434791651273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987788078538956527767515 4481682117808434791651273)
      ·
        refine ⟨3361261588356326093738455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4481682117808434791651273 3361261588356326093738455)
        ·
          refine ⟨5041892382534489140607683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361261588356326093738455 5041892382534489140607683)
          ·
            refine ⟨7562838573801733710911525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5041892382534489140607683 7562838573801733710911525)
            ·
              refine ⟨1418032232587825070795911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7562838573801733710911525 1418032232587825070795911)
              ·
                refine ⟨2127048348881737606193867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418032232587825070795911 2127048348881737606193867)
                ·
                  refine ⟨3190572523322606409290801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127048348881737606193867 3190572523322606409290801)
                  ·
                    refine ⟨2392929392491954806968101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3190572523322606409290801 2392929392491954806968101)
                    ·
                      refine ⟨448674261092241526306519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2392929392491954806968101 448674261092241526306519)
                      ·
                        rfl

theorem cell23_873790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_873790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873790 prefixEnd_873790 := by exact prefixLift 873790
  have htrace : WordTrace (prefixWord ++ tailWord_873790) baseStart_873790 baseEnd_873790 := by
    simpa [prefixWord, tailWord_873790, baseEnd_873790] using wordTrace_append hprefix tailTrace_873790
  have hstable : (prefixWord ++ tailWord_873790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873790).length < 2 ^ (prefixWord ++ tailWord_873790).sum := by decide
  have hdescent : baseEnd_873790 < baseStart_873790 := by decide
  rcases family_descends (prefixWord ++ tailWord_873790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873798 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_873798 : Nat := 118140960795 + 873798 * 2 ^ 59
def prefixEnd_873798 : Nat := 4983230072969 + 3 ^ 40 * 873798 * 2
def baseEnd_873798 : Nat := 448678368937477495006483

theorem tailTrace_873798 : CollatzResearch.WordTrace tailWord_873798 prefixEnd_873798 448678368937477495006483 := by
  unfold tailWord_873798
  simp only [CollatzResearch.WordTrace]
  refine ⟨995938477762079801952439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21246687525591035774985365 995938477762079801952439)
  ·
    refine ⟨1493907716643119702928659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995938477762079801952439 1493907716643119702928659)
    ·
      refine ⟨2240861574964679554392989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493907716643119702928659 2240861574964679554392989)
      ·
        refine ⟨840323090611754832897371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2240861574964679554392989 840323090611754832897371)
        ·
          refine ⟨1260484635917632249346057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840323090611754832897371 1260484635917632249346057)
          ·
            refine ⟨945363476938224187009543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260484635917632249346057 945363476938224187009543)
            ·
              refine ⟨1418045215407336280514315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945363476938224187009543 1418045215407336280514315)
              ·
                refine ⟨2127067823111004420771473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418045215407336280514315 2127067823111004420771473)
                ·
                  refine ⟨1595300867333253315578605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127067823111004420771473 1595300867333253315578605)
                  ·
                    refine ⟨598237825249969993341977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595300867333253315578605 598237825249969993341977)
                    ·
                      refine ⟨448678368937477495006483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598237825249969993341977 448678368937477495006483)
                      ·
                        rfl

theorem cell23_873798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_873798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873798 prefixEnd_873798 := by exact prefixLift 873798
  have htrace : WordTrace (prefixWord ++ tailWord_873798) baseStart_873798 baseEnd_873798 := by
    simpa [prefixWord, tailWord_873798, baseEnd_873798] using wordTrace_append hprefix tailTrace_873798
  have hstable : (prefixWord ++ tailWord_873798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873798).length < 2 ^ (prefixWord ++ tailWord_873798).sum := by decide
  have hdescent : baseEnd_873798 < baseStart_873798 := by decide
  rcases family_descends (prefixWord ++ tailWord_873798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873810 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_873810 : Nat := 118140960795 + 873810 * 2 ^ 59
def prefixEnd_873810 : Nat := 4983230072969 + 3 ^ 40 * 873810 * 2
def baseEnd_873810 : Nat := 448684530705331448056427

theorem tailTrace_873810 : CollatzResearch.WordTrace tailWord_873810 prefixEnd_873810 448684530705331448056427 := by
  unfold tailWord_873810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967617241085769927978721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21246979309562053141276589 7967617241085769927978721)
  ·
    refine ⟨5975712930814327445984041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7967617241085769927978721 5975712930814327445984041)
    ·
      refine ⟨4481784698110745584488031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5975712930814327445984041 4481784698110745584488031)
      ·
        refine ⟨6722677047166118376732047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481784698110745584488031 6722677047166118376732047)
        ·
          refine ⟨10084015570749177565098071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722677047166118376732047 10084015570749177565098071)
          ·
            refine ⟨15126023356123766347647107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10084015570749177565098071 15126023356123766347647107)
            ·
              refine ⟨22689035034185649521470661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15126023356123766347647107 22689035034185649521470661)
              ·
                refine ⟨4254194068909809285275749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22689035034185649521470661 4254194068909809285275749)
                ·
                  refine ⟨797661387920589240989203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4254194068909809285275749 797661387920589240989203)
                  ·
                    refine ⟨1196492081880883861483805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 797661387920589240989203 1196492081880883861483805)
                    ·
                      refine ⟨448684530705331448056427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196492081880883861483805 448684530705331448056427)
                      ·
                        rfl

theorem cell23_873810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_873810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873810 prefixEnd_873810 := by exact prefixLift 873810
  have htrace : WordTrace (prefixWord ++ tailWord_873810) baseStart_873810 baseEnd_873810 := by
    simpa [prefixWord, tailWord_873810, baseEnd_873810] using wordTrace_append hprefix tailTrace_873810
  have hstable : (prefixWord ++ tailWord_873810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873810).length < 2 ^ (prefixWord ++ tailWord_873810).sum := by decide
  have hdescent : baseEnd_873810 < baseStart_873810 := by decide
  rcases family_descends (prefixWord ++ tailWord_873810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873827 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 3]
def baseStart_873827 : Nat := 118140960795 + 873827 * 2 ^ 59
def prefixEnd_873827 : Nat := 4983230072969 + 3 ^ 40 * 873827 * 2
def baseEnd_873827 : Nat := 448693259876457881543849

theorem tailTrace_873827 : CollatzResearch.WordTrace tailWord_873827 prefixEnd_873827 448693259876457881543849 := by
  unfold tailWord_873827
  simp only [CollatzResearch.WordTrace]
  refine ⟨31871089005281491615283735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21247392670187661076855823 31871089005281491615283735)
  ·
    refine ⟨47806633507922237422925603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31871089005281491615283735 47806633507922237422925603)
    ·
      refine ⟨71709950261883356134388405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47806633507922237422925603 71709950261883356134388405)
      ·
        refine ⟨6722807837051564637598913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71709950261883356134388405 6722807837051564637598913)
        ·
          refine ⟨5042105877788673478199185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6722807837051564637598913 5042105877788673478199185)
          ·
            refine ⟨3781579408341505108649389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042105877788673478199185 3781579408341505108649389)
            ·
              refine ⟨1418092278128064415743521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3781579408341505108649389 1418092278128064415743521)
              ·
                refine ⟨1063569208596048311807641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418092278128064415743521 1063569208596048311807641)
                ·
                  refine ⟨797676906447036233855731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063569208596048311807641 797676906447036233855731)
                  ·
                    refine ⟨1196515359670554350783597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 797676906447036233855731 1196515359670554350783597)
                    ·
                      refine ⟨448693259876457881543849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196515359670554350783597 448693259876457881543849)
                      ·
                        rfl

theorem cell23_873827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_873827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873827 prefixEnd_873827 := by exact prefixLift 873827
  have htrace : WordTrace (prefixWord ++ tailWord_873827) baseStart_873827 baseEnd_873827 := by
    simpa [prefixWord, tailWord_873827, baseEnd_873827] using wordTrace_append hprefix tailTrace_873827
  have hstable : (prefixWord ++ tailWord_873827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873827).length < 2 ^ (prefixWord ++ tailWord_873827).sum := by decide
  have hdescent : baseEnd_873827 < baseStart_873827 := by decide
  rcases family_descends (prefixWord ++ tailWord_873827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873853 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_873853 : Nat := 118140960795 + 873853 * 2 ^ 59
def prefixEnd_873853 : Nat := 4983230072969 + 3 ^ 40 * 873853 * 2
def baseEnd_873853 : Nat := 448706610373474779818729

theorem tailTrace_873853 : CollatzResearch.WordTrace tailWord_873853 prefixEnd_873853 448706610373474779818729 := by
  unfold tailWord_873853
  simp only [CollatzResearch.WordTrace]
  refine ⟨31872037303187298055730213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21248024868791532037153475 31872037303187298055730213)
  ·
    refine ⟨5976006994347618385449415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31872037303187298055730213 5976006994347618385449415)
    ·
      refine ⟨8964010491521427578174123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5976006994347618385449415 8964010491521427578174123)
      ·
        refine ⟨13446015737282141367261185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8964010491521427578174123 13446015737282141367261185)
        ·
          refine ⟨10084511802961606025445889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13446015737282141367261185 10084511802961606025445889)
          ·
            refine ⟨7563383852221204519084417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10084511802961606025445889 7563383852221204519084417)
            ·
              refine ⟨5672537889165903389313313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7563383852221204519084417 5672537889165903389313313)
              ·
                refine ⟨4254403416874427541984985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672537889165903389313313 4254403416874427541984985)
                ·
                  refine ⟨3190802562655820656488739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4254403416874427541984985 3190802562655820656488739)
                  ·
                    refine ⟨4786203843983730984733109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3190802562655820656488739 4786203843983730984733109)
                    ·
                      refine ⟨448706610373474779818729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4786203843983730984733109 448706610373474779818729)
                      ·
                        rfl

theorem cell23_873853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_873853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873853 prefixEnd_873853 := by exact prefixLift 873853
  have htrace : WordTrace (prefixWord ++ tailWord_873853) baseStart_873853 baseEnd_873853 := by
    simpa [prefixWord, tailWord_873853, baseEnd_873853] using wordTrace_append hprefix tailTrace_873853
  have hstable : (prefixWord ++ tailWord_873853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873853).length < 2 ^ (prefixWord ++ tailWord_873853).sum := by decide
  have hdescent : baseEnd_873853 < baseStart_873853 := by decide
  rcases family_descends (prefixWord ++ tailWord_873853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873890 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 7]
def baseStart_873890 : Nat := 118140960795 + 873890 * 2 ^ 59
def prefixEnd_873890 : Nat := 4983230072969 + 3 ^ 40 * 873890 * 2
def baseEnd_873890 : Nat := 49858401017521237228451

theorem tailTrace_873890 : CollatzResearch.WordTrace tailWord_873890 prefixEnd_873890 49858401017521237228451 := by
  unfold tailWord_873890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7968346701013313343706781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21248924536035502249884749 7968346701013313343706781)
  ·
    refine ⟨2988130012879992503890043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7968346701013313343706781 2988130012879992503890043)
    ·
      refine ⟨4482195019319988755835065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988130012879992503890043 4482195019319988755835065)
      ·
        refine ⟨3361646264489991566876299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4482195019319988755835065 3361646264489991566876299)
        ·
          refine ⟨5042469396734987350314449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361646264489991566876299 5042469396734987350314449)
          ·
            refine ⟨3781852047551240512735837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042469396734987350314449 3781852047551240512735837)
            ·
              refine ⟨1418194517831715192275939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3781852047551240512735837 1418194517831715192275939)
              ·
                refine ⟨2127291776747572788413909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418194517831715192275939 2127291776747572788413909)
                ·
                  refine ⟨49858401017521237228451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2127291776747572788413909 49858401017521237228451)
                  ·
                    rfl

theorem cell23_873890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_873890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873890 prefixEnd_873890 := by exact prefixLift 873890
  have htrace : WordTrace (prefixWord ++ tailWord_873890) baseStart_873890 baseEnd_873890 := by
    simpa [prefixWord, tailWord_873890, baseEnd_873890] using wordTrace_append hprefix tailTrace_873890
  have hstable : (prefixWord ++ tailWord_873890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873890).length < 2 ^ (prefixWord ++ tailWord_873890).sum := by decide
  have hdescent : baseEnd_873890 < baseStart_873890 := by decide
  rcases family_descends (prefixWord ++ tailWord_873890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873901 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_873901 : Nat := 118140960795 + 873901 * 2 ^ 59
def prefixEnd_873901 : Nat := 4983230072969 + 3 ^ 40 * 873901 * 2
def baseEnd_873901 : Nat := 448731257444890592018509

theorem tailTrace_873901 : CollatzResearch.WordTrace tailWord_873901 prefixEnd_873901 448731257444890592018509 := by
  unfold tailWord_873901
  simp only [CollatzResearch.WordTrace]
  refine ⟨31873788007013402253477557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21249192004675601502318371 31873788007013402253477557)
  ·
    refine ⟨2988167625657506461263521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31873788007013402253477557 2988167625657506461263521)
    ·
      refine ⟨2241125719243129845947641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2988167625657506461263521 2241125719243129845947641)
      ·
        refine ⟨1680844289432347384460731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2241125719243129845947641 1680844289432347384460731)
        ·
          refine ⟨2521266434148521076691097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680844289432347384460731 2521266434148521076691097)
          ·
            refine ⟨1890949825611390807518323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2521266434148521076691097 1890949825611390807518323)
            ·
              refine ⟨2836424738417086211277485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890949825611390807518323 2836424738417086211277485)
              ·
                refine ⟨1063659276906407329229057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2836424738417086211277485 1063659276906407329229057)
                ·
                  refine ⟨797744457679805496921793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063659276906407329229057 797744457679805496921793)
                  ·
                    refine ⟨598308343259854122691345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 797744457679805496921793 598308343259854122691345)
                    ·
                      refine ⟨448731257444890592018509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598308343259854122691345 448731257444890592018509)
                      ·
                        rfl

theorem cell23_873901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_873901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873901 prefixEnd_873901 := by exact prefixLift 873901
  have htrace : WordTrace (prefixWord ++ tailWord_873901) baseStart_873901 baseEnd_873901 := by
    simpa [prefixWord, tailWord_873901, baseEnd_873901] using wordTrace_append hprefix tailTrace_873901
  have hstable : (prefixWord ++ tailWord_873901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873901).length < 2 ^ (prefixWord ++ tailWord_873901).sum := by decide
  have hdescent : baseEnd_873901 < baseStart_873901 := by decide
  rcases family_descends (prefixWord ++ tailWord_873901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873922 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_873922 : Nat := 118140960795 + 873922 * 2 ^ 59
def prefixEnd_873922 : Nat := 4983230072969 + 3 ^ 40 * 873922 * 2
def baseEnd_873922 : Nat := 448742040538635009855913

theorem tailTrace_873922 : CollatzResearch.WordTrace tailWord_873922 prefixEnd_873922 448742040538635009855913 := by
  unfold tailWord_873922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7968638484984330709998005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21249702626624881893328013 7968638484984330709998005)
  ·
    refine ⟨747059857967281004062313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7968638484984330709998005 747059857967281004062313)
    ·
      refine ⟨560294893475460753046735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 747059857967281004062313 560294893475460753046735)
      ·
        refine ⟨840442340213191129570103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560294893475460753046735 840442340213191129570103)
        ·
          refine ⟨1260663510319786694355155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840442340213191129570103 1260663510319786694355155)
          ·
            refine ⟨1890995265479680041532733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260663510319786694355155 1890995265479680041532733)
            ·
              refine ⟨709123224554880015574775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1890995265479680041532733 709123224554880015574775)
              ·
                refine ⟨1063684836832320023362163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709123224554880015574775 1063684836832320023362163)
                ·
                  refine ⟨1595527255248480035043245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063684836832320023362163 1595527255248480035043245)
                  ·
                    refine ⟨598322720718180013141217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595527255248480035043245 598322720718180013141217)
                    ·
                      refine ⟨448742040538635009855913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598322720718180013141217 448742040538635009855913)
                      ·
                        rfl

theorem cell23_873922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_873922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873922 prefixEnd_873922 := by exact prefixLift 873922
  have htrace : WordTrace (prefixWord ++ tailWord_873922) baseStart_873922 baseEnd_873922 := by
    simpa [prefixWord, tailWord_873922, baseEnd_873922] using wordTrace_append hprefix tailTrace_873922
  have hstable : (prefixWord ++ tailWord_873922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873922).length < 2 ^ (prefixWord ++ tailWord_873922).sum := by decide
  have hdescent : baseEnd_873922 < baseStart_873922 := by decide
  rcases family_descends (prefixWord ++ tailWord_873922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873923 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4]
def baseStart_873923 : Nat := 118140960795 + 873923 * 2 ^ 59
def prefixEnd_873923 : Nat := 4983230072969 + 3 ^ 40 * 873923 * 2
def baseEnd_873923 : Nat := 448742554019289505943407

theorem tailTrace_873923 : CollatzResearch.WordTrace tailWord_873923 prefixEnd_873923 448742554019289505943407 := by
  unfold tailWord_873923
  simp only [CollatzResearch.WordTrace]
  refine ⟨31874590412933700010778423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21249726941955800007185615 31874590412933700010778423)
  ·
    refine ⟨47811885619400550016167635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31874590412933700010778423 47811885619400550016167635)
    ·
      refine ⟨71717828429100825024251453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47811885619400550016167635 71717828429100825024251453)
      ·
        refine ⟨26894185660912809384094295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71717828429100825024251453 26894185660912809384094295)
        ·
          refine ⟨40341278491369214076141443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26894185660912809384094295 40341278491369214076141443)
          ·
            refine ⟨60511917737053821114212165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40341278491369214076141443 60511917737053821114212165)
            ·
              refine ⟨11345984575697591458914781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60511917737053821114212165 11345984575697591458914781)
              ·
                refine ⟨4254744215886596797093043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11345984575697591458914781 4254744215886596797093043)
                ·
                  refine ⟨6382116323829895195639565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4254744215886596797093043 6382116323829895195639565)
                  ·
                    refine ⟨2393293621436210698364837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6382116323829895195639565 2393293621436210698364837)
                    ·
                      refine ⟨448742554019289505943407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2393293621436210698364837 448742554019289505943407)
                      ·
                        rfl

theorem cell23_873923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_873923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873923 prefixEnd_873923 := by exact prefixLift 873923
  have htrace : WordTrace (prefixWord ++ tailWord_873923) baseStart_873923 baseEnd_873923 := by
    simpa [prefixWord, tailWord_873923, baseEnd_873923] using wordTrace_append hprefix tailTrace_873923
  have hstable : (prefixWord ++ tailWord_873923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873923).length < 2 ^ (prefixWord ++ tailWord_873923).sum := by decide
  have hdescent : baseEnd_873923 < baseStart_873923 := by decide
  rcases family_descends (prefixWord ++ tailWord_873923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873957 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 1, 6, 2]
def baseStart_873957 : Nat := 118140960795 + 873957 * 2 ^ 59
def prefixEnd_873957 : Nat := 4983230072969 + 3 ^ 40 * 873957 * 2
def baseEnd_873957 : Nat := 448760012361542372918251

theorem tailTrace_873957 : CollatzResearch.WordTrace tailWord_873957 prefixEnd_873957 448760012361542372918251 := by
  unfold tailWord_873957
  simp only [CollatzResearch.WordTrace]
  refine ⟨31875830494810523817516125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21250553663207015878344083 31875830494810523817516125)
  ·
    refine ⟨11953436435553946431568547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31875830494810523817516125 11953436435553946431568547)
    ·
      refine ⟨17930154653330919647352821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11953436435553946431568547 17930154653330919647352821)
      ·
        refine ⟨1680951998749773716939327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17930154653330919647352821 1680951998749773716939327)
        ·
          refine ⟨2521427998124660575408991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680951998749773716939327 2521427998124660575408991)
          ·
            refine ⟨3782141997186990863113487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521427998124660575408991 3782141997186990863113487)
            ·
              refine ⟨5673212995780486294670231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782141997186990863113487 5673212995780486294670231)
              ·
                refine ⟨8509819493670729442005347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673212995780486294670231 8509819493670729442005347)
                ·
                  refine ⟨12764729240506094163008021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8509819493670729442005347 12764729240506094163008021)
                  ·
                    refine ⟨598346683148723163891001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12764729240506094163008021 598346683148723163891001)
                    ·
                      refine ⟨448760012361542372918251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598346683148723163891001 448760012361542372918251)
                      ·
                        rfl

theorem cell23_873957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_873957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873957 prefixEnd_873957 := by exact prefixLift 873957
  have htrace : WordTrace (prefixWord ++ tailWord_873957) baseStart_873957 baseEnd_873957 := by
    simpa [prefixWord, tailWord_873957, baseEnd_873957] using wordTrace_append hprefix tailTrace_873957
  have hstable : (prefixWord ++ tailWord_873957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873957).length < 2 ^ (prefixWord ++ tailWord_873957).sum := by decide
  have hdescent : baseEnd_873957 < baseStart_873957 := by decide
  rcases family_descends (prefixWord ++ tailWord_873957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873960 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_873960 : Nat := 118140960795 + 873960 * 2 ^ 59
def prefixEnd_873960 : Nat := 4983230072969 + 3 ^ 40 * 873960 * 2
def baseEnd_873960 : Nat := 448761552803505861180737

theorem tailTrace_873960 : CollatzResearch.WordTrace tailWord_873960 prefixEnd_873960 448761552803505861180737 := by
  unfold tailWord_873960
  simp only [CollatzResearch.WordTrace]
  refine ⟨15937969956899827664937667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21250626609199770219916889 15937969956899827664937667)
  ·
    refine ⟨23906954935349741497406501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15937969956899827664937667 23906954935349741497406501)
    ·
      refine ⟨4482554050378076530763719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23906954935349741497406501 4482554050378076530763719)
      ·
        refine ⟨6723831075567114796145579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482554050378076530763719 6723831075567114796145579)
        ·
          refine ⟨10085746613350672194218369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723831075567114796145579 10085746613350672194218369)
          ·
            refine ⟨7564309960013004145663777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10085746613350672194218369 7564309960013004145663777)
            ·
              refine ⟨5673232470009753109247833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7564309960013004145663777 5673232470009753109247833)
              ·
                refine ⟨4254924352507314831935875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5673232470009753109247833 4254924352507314831935875)
                ·
                  refine ⟨6382386528760972247903813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4254924352507314831935875 6382386528760972247903813)
                  ·
                    refine ⟨1196697474142682296481965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382386528760972247903813 1196697474142682296481965)
                    ·
                      refine ⟨448761552803505861180737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196697474142682296481965 448761552803505861180737)
                      ·
                        rfl

theorem cell23_873960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_873960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873960 prefixEnd_873960 := by exact prefixLift 873960
  have htrace : WordTrace (prefixWord ++ tailWord_873960) baseStart_873960 baseEnd_873960 := by
    simpa [prefixWord, tailWord_873960, baseEnd_873960] using wordTrace_append hprefix tailTrace_873960
  have hstable : (prefixWord ++ tailWord_873960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873960).length < 2 ^ (prefixWord ++ tailWord_873960).sum := by decide
  have hdescent : baseEnd_873960 < baseStart_873960 := by decide
  rcases family_descends (prefixWord ++ tailWord_873960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873974 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_873974 : Nat := 118140960795 + 873974 * 2 ^ 59
def prefixEnd_873974 : Nat := 4983230072969 + 3 ^ 40 * 873974 * 2
def baseEnd_873974 : Nat := 448768741532668806405673

theorem tailTrace_873974 : CollatzResearch.WordTrace tailWord_873974 prefixEnd_873974 448768741532668806405673 := by
  unfold tailWord_873974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992278158484308482555311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21250967023832623813923317 1992278158484308482555311)
  ·
    refine ⟨2988417237726462723832967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1992278158484308482555311 2988417237726462723832967)
    ·
      refine ⟨4482625856589694085749451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988417237726462723832967 4482625856589694085749451)
      ·
        refine ⟨6723938784884541128624177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482625856589694085749451 6723938784884541128624177)
        ·
          refine ⟨5042954088663405846468133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6723938784884541128624177 5042954088663405846468133)
          ·
            refine ⟨945553891624388596212775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5042954088663405846468133 945553891624388596212775)
            ·
              refine ⟨1418330837436582894319163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945553891624388596212775 1418330837436582894319163)
              ·
                refine ⟨2127496256154874341478745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418330837436582894319163 2127496256154874341478745)
                ·
                  refine ⟨1595622192116155756109059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127496256154874341478745 1595622192116155756109059)
                  ·
                    refine ⟨2393433288174233634163589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1595622192116155756109059 2393433288174233634163589)
                    ·
                      refine ⟨448768741532668806405673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2393433288174233634163589 448768741532668806405673)
                      ·
                        rfl

theorem cell23_873974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_873974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_873974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_873974 prefixEnd_873974 := by exact prefixLift 873974
  have htrace : WordTrace (prefixWord ++ tailWord_873974) baseStart_873974 baseEnd_873974 := by
    simpa [prefixWord, tailWord_873974, baseEnd_873974] using wordTrace_append hprefix tailTrace_873974
  have hstable : (prefixWord ++ tailWord_873974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873974).length < 2 ^ (prefixWord ++ tailWord_873974).sum := by decide
  have hdescent : baseEnd_873974 < baseStart_873974 := by decide
  rcases family_descends (prefixWord ++ tailWord_873974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874017 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_874017 : Nat := 118140960795 + 874017 * 2 ^ 59
def prefixEnd_874017 : Nat := 4983230072969 + 3 ^ 40 * 874017 * 2
def baseEnd_874017 : Nat := 448790821200812138167975

theorem tailTrace_874017 : CollatzResearch.WordTrace tailWord_874017 prefixEnd_874017 448790821200812138167975 := by
  unfold tailWord_874017
  simp only [CollatzResearch.WordTrace]
  refine ⟨31878018874593154064700305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21252012583062102709800203 31878018874593154064700305)
  ·
    refine ⟨23908514155944865548525229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31878018874593154064700305 23908514155944865548525229)
    ·
      refine ⟨8965692808479324580696961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23908514155944865548525229 8965692808479324580696961)
      ·
        refine ⟨6724269606359493435522721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8965692808479324580696961 6724269606359493435522721)
        ·
          refine ⟨5043202204769620076642041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6724269606359493435522721 5043202204769620076642041)
          ·
            refine ⟨3782401653577215057481531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5043202204769620076642041 3782401653577215057481531)
            ·
              refine ⟨5673602480365822586222297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782401653577215057481531 5673602480365822586222297)
              ·
                refine ⟨4255201860274366939666723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5673602480365822586222297 4255201860274366939666723)
                ·
                  refine ⟨6382802790411550409500085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255201860274366939666723 6382802790411550409500085)
                  ·
                    refine ⟨598387761601082850890633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6382802790411550409500085 598387761601082850890633)
                    ·
                      refine ⟨448790821200812138167975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598387761601082850890633 448790821200812138167975)
                      ·
                        rfl

theorem cell23_874017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_874017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874017 prefixEnd_874017 := by exact prefixLift 874017
  have htrace : WordTrace (prefixWord ++ tailWord_874017) baseStart_874017 baseEnd_874017 := by
    simpa [prefixWord, tailWord_874017, baseEnd_874017] using wordTrace_append hprefix tailTrace_874017
  have hstable : (prefixWord ++ tailWord_874017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874017).length < 2 ^ (prefixWord ++ tailWord_874017).sum := by decide
  have hdescent : baseEnd_874017 < baseStart_874017 := by decide
  rcases family_descends (prefixWord ++ tailWord_874017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874041 : List Nat := [1, 2, 1, 5, 1, 2, 3, 3, 1, 1, 3]
def baseStart_874041 : Nat := 118140960795 + 874041 * 2 ^ 59
def prefixEnd_874041 : Nat := 4983230072969 + 3 ^ 40 * 874041 * 2
def baseEnd_874041 : Nat := 448803144736520044267865

theorem tailTrace_874041 : CollatzResearch.WordTrace tailWord_874041 prefixEnd_874041 448803144736520044267865 := by
  unfold tailWord_874041
  simp only [CollatzResearch.WordTrace]
  refine ⟨31878894226506206163573977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21252596151004137442382651 31878894226506206163573977)
  ·
    refine ⟨23909170669879654622680483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31878894226506206163573977 23909170669879654622680483)
    ·
      refine ⟨35863756004819481934020725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23909170669879654622680483 35863756004819481934020725)
      ·
        refine ⟨3362227125451826431314443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35863756004819481934020725 3362227125451826431314443)
        ·
          refine ⟨5043340688177739646971665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362227125451826431314443 5043340688177739646971665)
          ·
            refine ⟨3782505516133304735228749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5043340688177739646971665 3782505516133304735228749)
            ·
              refine ⟨1418439568549989275710781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3782505516133304735228749 1418439568549989275710781)
              ·
                refine ⟨531914838206245978391543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1418439568549989275710781 531914838206245978391543)
                ·
                  refine ⟨797872257309368967587315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531914838206245978391543 797872257309368967587315)
                  ·
                    refine ⟨1196808385964053451380973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 797872257309368967587315 1196808385964053451380973)
                    ·
                      refine ⟨448803144736520044267865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196808385964053451380973 448803144736520044267865)
                      ·
                        rfl

theorem cell23_874041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_874041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874041 prefixEnd_874041 := by exact prefixLift 874041
  have htrace : WordTrace (prefixWord ++ tailWord_874041) baseStart_874041 baseEnd_874041 := by
    simpa [prefixWord, tailWord_874041, baseEnd_874041] using wordTrace_append hprefix tailTrace_874041
  have hstable : (prefixWord ++ tailWord_874041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874041).length < 2 ^ (prefixWord ++ tailWord_874041).sum := by decide
  have hdescent : baseEnd_874041 < baseStart_874041 := by decide
  rcases family_descends (prefixWord ++ tailWord_874041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874047 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 4]
def baseStart_874047 : Nat := 118140960795 + 874047 * 2 ^ 59
def prefixEnd_874047 : Nat := 4983230072969 + 3 ^ 40 * 874047 * 2
def baseEnd_874047 : Nat := 448806225620447020792837

theorem tailTrace_874047 : CollatzResearch.WordTrace tailWord_874047 prefixEnd_874047 448806225620447020792837 := by
  unfold tailWord_874047
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879113064484469188292395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21252742042989646125528263 31879113064484469188292395)
  ·
    refine ⟨47818669596726703782438593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31879113064484469188292395 47818669596726703782438593)
    ·
      refine ⟨35864002197545027836828945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47818669596726703782438593 35864002197545027836828945)
      ·
        refine ⟨26898001648158770877621709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35864002197545027836828945 26898001648158770877621709)
        ·
          refine ⟨10086750618059539079108141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26898001648158770877621709 10086750618059539079108141)
          ·
            refine ⟨3782531481772327154665553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10086750618059539079108141 3782531481772327154665553)
            ·
              refine ⟨2836898611329245365999165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3782531481772327154665553 2836898611329245365999165)
              ·
                refine ⟨1063836979248467012249687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2836898611329245365999165 1063836979248467012249687)
                ·
                  refine ⟨1595755468872700518374531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063836979248467012249687 1595755468872700518374531)
                  ·
                    refine ⟨2393633203309050777561797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1595755468872700518374531 2393633203309050777561797)
                    ·
                      refine ⟨448806225620447020792837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2393633203309050777561797 448806225620447020792837)
                      ·
                        rfl

theorem cell23_874047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_874047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874047 prefixEnd_874047 := by exact prefixLift 874047
  have htrace : WordTrace (prefixWord ++ tailWord_874047) baseStart_874047 baseEnd_874047 := by
    simpa [prefixWord, tailWord_874047, baseEnd_874047] using wordTrace_append hprefix tailTrace_874047
  have hstable : (prefixWord ++ tailWord_874047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874047).length < 2 ^ (prefixWord ++ tailWord_874047).sum := by decide
  have hdescent : baseEnd_874047 < baseStart_874047 := by decide
  rcases family_descends (prefixWord ++ tailWord_874047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874060 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_874060 : Nat := 118140960795 + 874060 * 2 ^ 59
def prefixEnd_874060 : Nat := 4983230072969 + 3 ^ 40 * 874060 * 2
def baseEnd_874060 : Nat := 448812900868955469930277

theorem tailTrace_874060 : CollatzResearch.WordTrace tailWord_874060 prefixEnd_874060 448812900868955469930277 := by
  unfold tailWord_874060
  simp only [CollatzResearch.WordTrace]
  refine ⟨15939793606718686204257817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21253058142291581605677089 15939793606718686204257817)
  ·
    refine ⟨11954845205039014653193363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15939793606718686204257817 11954845205039014653193363)
    ·
      refine ⟨17932267807558521979790045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11954845205039014653193363 17932267807558521979790045)
      ·
        refine ⟨6724600427834445742421267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17932267807558521979790045 6724600427834445742421267)
        ·
          refine ⟨10086900641751668613631901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6724600427834445742421267 10086900641751668613631901)
          ·
            refine ⟨3782587740656875730111963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10086900641751668613631901 3782587740656875730111963)
            ·
              refine ⟨5673881610985313595167945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782587740656875730111963 5673881610985313595167945)
              ·
                refine ⟨4255411208238985196375959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5673881610985313595167945 4255411208238985196375959)
                ·
                  refine ⟨6383116812358477794563939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255411208238985196375959 6383116812358477794563939)
                  ·
                    refine ⟨9574675218537716691845909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6383116812358477794563939 9574675218537716691845909)
                    ·
                      refine ⟨448812900868955469930277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9574675218537716691845909 448812900868955469930277)
                      ·
                        rfl

theorem cell23_874060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_874060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874060 prefixEnd_874060 := by exact prefixLift 874060
  have htrace : WordTrace (prefixWord ++ tailWord_874060) baseStart_874060 baseEnd_874060 := by
    simpa [prefixWord, tailWord_874060, baseEnd_874060] using wordTrace_append hprefix tailTrace_874060
  have hstable : (prefixWord ++ tailWord_874060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874060).length < 2 ^ (prefixWord ++ tailWord_874060).sum := by decide
  have hdescent : baseEnd_874060 < baseStart_874060 := by decide
  rcases family_descends (prefixWord ++ tailWord_874060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874084 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_874084 : Nat := 118140960795 + 874084 * 2 ^ 59
def prefixEnd_874084 : Nat := 4983230072969 + 3 ^ 40 * 874084 * 2
def baseEnd_874084 : Nat := 448825224404663376030167

theorem tailTrace_874084 : CollatzResearch.WordTrace tailWord_874084 prefixEnd_874084 448825224404663376030167 := by
  unfold tailWord_874084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15940231282675212253694653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21253641710233616338259537 15940231282675212253694653)
  ·
    refine ⟨5977586731003204595135495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15940231282675212253694653 5977586731003204595135495)
    ·
      refine ⟨8966380096504806892703243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5977586731003204595135495 8966380096504806892703243)
      ·
        refine ⟨13449570144757210339054865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8966380096504806892703243 13449570144757210339054865)
        ·
          refine ⟨10087177608567907754291149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13449570144757210339054865 10087177608567907754291149)
          ·
            refine ⟨3782691603212965407859181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10087177608567907754291149 3782691603212965407859181)
            ·
              refine ⟨1418509351204862027947193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3782691603212965407859181 1418509351204862027947193)
              ·
                refine ⟨1063882013403646520960395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418509351204862027947193 1063882013403646520960395)
                ·
                  refine ⟨1595823020105469781440593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063882013403646520960395 1595823020105469781440593)
                  ·
                    refine ⟨1196867265079102336080445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1595823020105469781440593 1196867265079102336080445)
                    ·
                      refine ⟨448825224404663376030167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196867265079102336080445 448825224404663376030167)
                      ·
                        rfl

theorem cell23_874084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_874084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874084 prefixEnd_874084 := by exact prefixLift 874084
  have htrace : WordTrace (prefixWord ++ tailWord_874084) baseStart_874084 baseEnd_874084 := by
    simpa [prefixWord, tailWord_874084, baseEnd_874084] using wordTrace_append hprefix tailTrace_874084
  have hstable : (prefixWord ++ tailWord_874084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874084).length < 2 ^ (prefixWord ++ tailWord_874084).sum := by decide
  have hdescent : baseEnd_874084 < baseStart_874084 := by decide
  rcases family_descends (prefixWord ++ tailWord_874084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874094 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_874094 : Nat := 118140960795 + 874094 * 2 ^ 59
def prefixEnd_874094 : Nat := 4983230072969 + 3 ^ 40 * 874094 * 2
def baseEnd_874094 : Nat := 448830359211208336905121

theorem tailTrace_874094 : CollatzResearch.WordTrace tailWord_874094 prefixEnd_874094 448830359211208336905121 := by
  unfold tailWord_874094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985103411914274526906667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21253884863542797476835557 3985103411914274526906667)
  ·
    refine ⟨5977655117871411790360001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3985103411914274526906667 5977655117871411790360001)
    ·
      refine ⟨4483241338403558842770001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5977655117871411790360001 4483241338403558842770001)
      ·
        refine ⟨3362431003802669132077501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4483241338403558842770001 3362431003802669132077501)
        ·
          refine ⟨1260911626426000924529063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3362431003802669132077501 1260911626426000924529063)
          ·
            refine ⟨1891367439639001386793595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260911626426000924529063 1891367439639001386793595)
            ·
              refine ⟨2837051159458502080190393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891367439639001386793595 2837051159458502080190393)
              ·
                refine ⟨2127788369593876560142795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837051159458502080190393 2127788369593876560142795)
                ·
                  refine ⟨3191682554390814840214193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127788369593876560142795 3191682554390814840214193)
                  ·
                    refine ⟨2393761915793111130160645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3191682554390814840214193 2393761915793111130160645)
                    ·
                      refine ⟨448830359211208336905121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2393761915793111130160645 448830359211208336905121)
                      ·
                        rfl

theorem cell23_874094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_874094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874094 prefixEnd_874094 := by exact prefixLift 874094
  have htrace : WordTrace (prefixWord ++ tailWord_874094) baseStart_874094 baseEnd_874094 := by
    simpa [prefixWord, tailWord_874094, baseEnd_874094] using wordTrace_append hprefix tailTrace_874094
  have hstable : (prefixWord ++ tailWord_874094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874094).length < 2 ^ (prefixWord ++ tailWord_874094).sum := by decide
  have hdescent : baseEnd_874094 < baseStart_874094 := by decide
  rcases family_descends (prefixWord ++ tailWord_874094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874097 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_874097 : Nat := 118140960795 + 874097 * 2 ^ 59
def prefixEnd_874097 : Nat := 4983230072969 + 3 ^ 40 * 874097 * 2
def baseEnd_874097 : Nat := 448831899653171825167607

theorem tailTrace_874097 : CollatzResearch.WordTrace tailWord_874097 prefixEnd_874097 448831899653171825167607 := by
  unfold tailWord_874097
  simp only [CollatzResearch.WordTrace]
  refine ⟨31880936714303327727612545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21253957809535551818408363 31880936714303327727612545)
  ·
    refine ⟨23910702535727495795709409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31880936714303327727612545 23910702535727495795709409)
    ·
      refine ⟨17933026901795621846782057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23910702535727495795709409 17933026901795621846782057)
      ·
        refine ⟨13449770176346716385086543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17933026901795621846782057 13449770176346716385086543)
        ·
          refine ⟨20174655264520074577629815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13449770176346716385086543 20174655264520074577629815)
          ·
            refine ⟨30261982896780111866444723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20174655264520074577629815 30261982896780111866444723)
            ·
              refine ⟨45392974345170167799667085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30261982896780111866444723 45392974345170167799667085)
              ·
                refine ⟨17022365379438812924875157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45392974345170167799667085 17022365379438812924875157)
                ·
                  refine ⟨797923377161194355853523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17022365379438812924875157 797923377161194355853523)
                  ·
                    refine ⟨1196885065741791533780285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 797923377161194355853523 1196885065741791533780285)
                    ·
                      refine ⟨448831899653171825167607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196885065741791533780285 448831899653171825167607)
                      ·
                        rfl

theorem cell23_874097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_874097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874097 prefixEnd_874097 := by exact prefixLift 874097
  have htrace : WordTrace (prefixWord ++ tailWord_874097) baseStart_874097 baseEnd_874097 := by
    simpa [prefixWord, tailWord_874097, baseEnd_874097] using wordTrace_append hprefix tailTrace_874097
  have hstable : (prefixWord ++ tailWord_874097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874097).length < 2 ^ (prefixWord ++ tailWord_874097).sum := by decide
  have hdescent : baseEnd_874097 < baseStart_874097 := by decide
  rcases family_descends (prefixWord ++ tailWord_874097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874152 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_874152 : Nat := 118140960795 + 874152 * 2 ^ 59
def prefixEnd_874152 : Nat := 4983230072969 + 3 ^ 40 * 874152 * 2
def baseEnd_874152 : Nat := 448860141089169109979855

theorem tailTrace_874152 : CollatzResearch.WordTrace tailWord_874152 prefixEnd_874152 448860141089169109979855 := by
  unfold tailWord_874152
  simp only [CollatzResearch.WordTrace]
  refine ⟨15941471364552036060432355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21255295152736048080576473 15941471364552036060432355)
  ·
    refine ⟨23912207046828054090648533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15941471364552036060432355 23912207046828054090648533)
    ·
      refine ⟨560442352660032517749575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23912207046828054090648533 560442352660032517749575)
      ·
        refine ⟨840663528990048776624363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560442352660032517749575 840663528990048776624363)
        ·
          refine ⟨1260995293485073164936545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840663528990048776624363 1260995293485073164936545)
          ·
            refine ⟨945746470113804873702409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260995293485073164936545 945746470113804873702409)
            ·
              refine ⟨709309852585353655276807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945746470113804873702409 709309852585353655276807)
              ·
                refine ⟨1063964778878030482915211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709309852585353655276807 1063964778878030482915211)
                ·
                  refine ⟨1595947168317045724372817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063964778878030482915211 1595947168317045724372817)
                  ·
                    refine ⟨1196960376237784293279613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1595947168317045724372817 1196960376237784293279613)
                    ·
                      refine ⟨448860141089169109979855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196960376237784293279613 448860141089169109979855)
                      ·
                        rfl

theorem cell23_874152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_874152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874152 prefixEnd_874152 := by exact prefixLift 874152
  have htrace : WordTrace (prefixWord ++ tailWord_874152) baseStart_874152 baseEnd_874152 := by
    simpa [prefixWord, tailWord_874152, baseEnd_874152] using wordTrace_append hprefix tailTrace_874152
  have hstable : (prefixWord ++ tailWord_874152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874152).length < 2 ^ (prefixWord ++ tailWord_874152).sum := by decide
  have hdescent : baseEnd_874152 < baseStart_874152 := by decide
  rcases family_descends (prefixWord ++ tailWord_874152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874157 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_874157 : Nat := 118140960795 + 874157 * 2 ^ 59
def prefixEnd_874157 : Nat := 4983230072969 + 3 ^ 40 * 874157 * 2
def baseEnd_874157 : Nat := 448862708492441590417331

theorem tailTrace_874157 : CollatzResearch.WordTrace tailWord_874157 prefixEnd_874157 448862708492441590417331 := by
  unfold tailWord_874157
  simp only [CollatzResearch.WordTrace]
  refine ⟨31883125094085957974796725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21255416729390638649864483 31883125094085957974796725)
  ·
    refine ⟨2989042977570558560137193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31883125094085957974796725 2989042977570558560137193)
    ·
      refine ⟨2241782233177918920102895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2989042977570558560137193 2241782233177918920102895)
      ·
        refine ⟨3362673349766878380154343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241782233177918920102895 3362673349766878380154343)
        ·
          refine ⟨5044010024650317570231515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362673349766878380154343 5044010024650317570231515)
          ·
            refine ⟨7566015036975476355347273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044010024650317570231515 7566015036975476355347273)
            ·
              refine ⟨5674511277731607266510455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7566015036975476355347273 5674511277731607266510455)
              ·
                refine ⟨8511766916597410899765683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674511277731607266510455 8511766916597410899765683)
                ·
                  refine ⟨12767650374896116349648525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8511766916597410899765683 12767650374896116349648525)
                  ·
                    refine ⟨4787868890586043631118197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12767650374896116349648525 4787868890586043631118197)
                    ·
                      refine ⟨448862708492441590417331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4787868890586043631118197 448862708492441590417331)
                      ·
                        rfl

theorem cell23_874157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_874157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874157 prefixEnd_874157 := by exact prefixLift 874157
  have htrace : WordTrace (prefixWord ++ tailWord_874157) baseStart_874157 baseEnd_874157 := by
    simpa [prefixWord, tailWord_874157, baseEnd_874157] using wordTrace_append hprefix tailTrace_874157
  have hstable : (prefixWord ++ tailWord_874157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874157).length < 2 ^ (prefixWord ++ tailWord_874157).sum := by decide
  have hdescent : baseEnd_874157 < baseStart_874157 := by decide
  rcases family_descends (prefixWord ++ tailWord_874157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874165 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_874165 : Nat := 118140960795 + 874165 * 2 ^ 59
def prefixEnd_874165 : Nat := 4983230072969 + 3 ^ 40 * 874165 * 2
def baseEnd_874165 : Nat := 448866816337677559117295

theorem tailTrace_874165 : CollatzResearch.WordTrace tailWord_874165 prefixEnd_874165 448866816337677559117295 := by
  unfold tailWord_874165
  simp only [CollatzResearch.WordTrace]
  refine ⟨31883416878056975341087949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21255611252037983560725299 31883416878056975341087949)
  ·
    refine ⟨11956281329271365752907981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31883416878056975341087949 11956281329271365752907981)
    ·
      refine ⟨4483605498476762157340493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11956281329271365752907981 4483605498476762157340493)
      ·
        refine ⟨1681352061928785809002685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4483605498476762157340493 1681352061928785809002685)
        ·
          refine ⟨630507023223294678376007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1681352061928785809002685 630507023223294678376007)
          ·
            refine ⟨945760534834942017564011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630507023223294678376007 945760534834942017564011)
            ·
              refine ⟨1418640802252413026346017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945760534834942017564011 1418640802252413026346017)
              ·
                refine ⟨1063980601689309769759513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418640802252413026346017 1063980601689309769759513)
                ·
                  refine ⟨797985451266982327319635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063980601689309769759513 797985451266982327319635)
                  ·
                    refine ⟨1196978176900473490979453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 797985451266982327319635 1196978176900473490979453)
                    ·
                      refine ⟨448866816337677559117295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1196978176900473490979453 448866816337677559117295)
                      ·
                        rfl

theorem cell23_874165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_874165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874165 prefixEnd_874165 := by exact prefixLift 874165
  have htrace : WordTrace (prefixWord ++ tailWord_874165) baseStart_874165 baseEnd_874165 := by
    simpa [prefixWord, tailWord_874165, baseEnd_874165] using wordTrace_append hprefix tailTrace_874165
  have hstable : (prefixWord ++ tailWord_874165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874165).length < 2 ^ (prefixWord ++ tailWord_874165).sum := by decide
  have hdescent : baseEnd_874165 < baseStart_874165 := by decide
  rcases family_descends (prefixWord ++ tailWord_874165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874167 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_874167 : Nat := 118140960795 + 874167 * 2 ^ 59
def prefixEnd_874167 : Nat := 4983230072969 + 3 ^ 40 * 874167 * 2
def baseEnd_874167 : Nat := 448867843298986551292285

theorem tailTrace_874167 : CollatzResearch.WordTrace tailWord_874167 prefixEnd_874167 448867843298986551292285 := by
  unfold tailWord_874167
  simp only [CollatzResearch.WordTrace]
  refine ⟨31883489824049729682660755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21255659882699819788440503 31883489824049729682660755)
  ·
    refine ⟨47825234736074594523991133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31883489824049729682660755 47825234736074594523991133)
    ·
      refine ⟨17934463026027972946496675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47825234736074594523991133 17934463026027972946496675)
      ·
        refine ⟨26901694539041959419745013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17934463026027972946496675 26901694539041959419745013)
        ·
          refine ⟨2522033863035183695601095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26901694539041959419745013 2522033863035183695601095)
          ·
            refine ⟨3783050794552775543401643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522033863035183695601095 3783050794552775543401643)
            ·
              refine ⟨5674576191829163315102465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3783050794552775543401643 5674576191829163315102465)
              ·
                refine ⟨4255932143871872486326849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674576191829163315102465 4255932143871872486326849)
                ·
                  refine ⟨3191949107903904364745137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4255932143871872486326849 3191949107903904364745137)
                  ·
                    refine ⟨2393961830927928273558853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3191949107903904364745137 2393961830927928273558853)
                    ·
                      refine ⟨448867843298986551292285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2393961830927928273558853 448867843298986551292285)
                      ·
                        rfl

theorem cell23_874167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_874167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874167 prefixEnd_874167 := by exact prefixLift 874167
  have htrace : WordTrace (prefixWord ++ tailWord_874167) baseStart_874167 baseEnd_874167 := by
    simpa [prefixWord, tailWord_874167, baseEnd_874167] using wordTrace_append hprefix tailTrace_874167
  have hstable : (prefixWord ++ tailWord_874167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874167).length < 2 ^ (prefixWord ++ tailWord_874167).sum := by decide
  have hdescent : baseEnd_874167 < baseStart_874167 := by decide
  rcases family_descends (prefixWord ++ tailWord_874167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874182 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_874182 : Nat := 118140960795 + 874182 * 2 ^ 59
def prefixEnd_874182 : Nat := 4983230072969 + 3 ^ 40 * 874182 * 2
def baseEnd_874182 : Nat := 448875545508803992604717

theorem tailTrace_874182 : CollatzResearch.WordTrace tailWord_874182 prefixEnd_874182 448875545508803992604717 := by
  unfold tailWord_874182
  simp only [CollatzResearch.WordTrace]
  refine ⟨996376153718605851389275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21256024612663591496304533 996376153718605851389275)
  ·
    refine ⟨1494564230577908777083913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 996376153718605851389275 1494564230577908777083913)
    ·
      refine ⟨1120923172933431582812935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1494564230577908777083913 1120923172933431582812935)
      ·
        refine ⟨1681384759400147374219403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120923172933431582812935 1681384759400147374219403)
        ·
          refine ⟨2522077139100221061329105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681384759400147374219403 2522077139100221061329105)
          ·
            refine ⟨1891557854325165795996829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2522077139100221061329105 1891557854325165795996829)
            ·
              refine ⟨709334195371937173498811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1891557854325165795996829 709334195371937173498811)
              ·
                refine ⟨1064001293057905760248217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709334195371937173498811 1064001293057905760248217)
                ·
                  refine ⟨798000969793429320186163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1064001293057905760248217 798000969793429320186163)
                  ·
                    refine ⟨1197001454690143980279245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 798000969793429320186163 1197001454690143980279245)
                    ·
                      refine ⟨448875545508803992604717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1197001454690143980279245 448875545508803992604717)
                      ·
                        rfl

theorem cell23_874182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_874182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874182 prefixEnd_874182 := by exact prefixLift 874182
  have htrace : WordTrace (prefixWord ++ tailWord_874182) baseStart_874182 baseEnd_874182 := by
    simpa [prefixWord, tailWord_874182, baseEnd_874182] using wordTrace_append hprefix tailTrace_874182
  have hstable : (prefixWord ++ tailWord_874182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874182).length < 2 ^ (prefixWord ++ tailWord_874182).sum := by decide
  have hdescent : baseEnd_874182 < baseStart_874182 := by decide
  rcases family_descends (prefixWord ++ tailWord_874182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874188 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 1, 4, 2]
def baseStart_874188 : Nat := 118140960795 + 874188 * 2 ^ 59
def prefixEnd_874188 : Nat := 4983230072969 + 3 ^ 40 * 874188 * 2
def baseEnd_874188 : Nat := 448878626392730969129689

theorem tailTrace_874188 : CollatzResearch.WordTrace tailWord_874188 prefixEnd_874188 448878626392730969129689 := by
  unfold tailWord_874188
  simp only [CollatzResearch.WordTrace]
  refine ⟨15942127878486825134587609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21256170504649100179450145 15942127878486825134587609)
  ·
    refine ⟨11956595908865118850940707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15942127878486825134587609 11956595908865118850940707)
    ·
      refine ⟨17934893863297678276411061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11956595908865118850940707 17934893863297678276411061)
      ·
        refine ⟨1681396299684157338413537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17934893863297678276411061 1681396299684157338413537)
        ·
          refine ⟨1261047224763118003810153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1681396299684157338413537 1261047224763118003810153)
          ·
            refine ⟨945785418572338502857615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261047224763118003810153 945785418572338502857615)
            ·
              refine ⟨1418678127858507754286423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945785418572338502857615 1418678127858507754286423)
              ·
                refine ⟨2128017191787761631429635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418678127858507754286423 2128017191787761631429635)
                ·
                  refine ⟨3192025787681642447144453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128017191787761631429635 3192025787681642447144453)
                  ·
                    refine ⟨598504835190307958839585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3192025787681642447144453 598504835190307958839585)
                    ·
                      refine ⟨448878626392730969129689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598504835190307958839585 448878626392730969129689)
                      ·
                        rfl

theorem cell23_874188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_874188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874188 prefixEnd_874188 := by exact prefixLift 874188
  have htrace : WordTrace (prefixWord ++ tailWord_874188) baseStart_874188 baseEnd_874188 := by
    simpa [prefixWord, tailWord_874188, baseEnd_874188] using wordTrace_append hprefix tailTrace_874188
  have hstable : (prefixWord ++ tailWord_874188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874188).length < 2 ^ (prefixWord ++ tailWord_874188).sum := by decide
  have hdescent : baseEnd_874188 < baseStart_874188 := by decide
  rcases family_descends (prefixWord ++ tailWord_874188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874207 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 2, 5]
def baseStart_874207 : Nat := 118140960795 + 874207 * 2 ^ 59
def prefixEnd_874207 : Nat := 4983230072969 + 3 ^ 40 * 874207 * 2
def baseEnd_874207 : Nat := 149629460841722131597367

theorem tailTrace_874207 : CollatzResearch.WordTrace tailWord_874207 prefixEnd_874207 149629460841722131597367 := by
  unfold tailWord_874207
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884948743904816514116875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21256632495936544342744583 31884948743904816514116875)
  ·
    refine ⟨47827423115857224771175313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31884948743904816514116875 47827423115857224771175313)
    ·
      refine ⟨35870567336892918578381485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47827423115857224771175313 35870567336892918578381485)
      ·
        refine ⟨13451462751334844466893057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35870567336892918578381485 13451462751334844466893057)
        ·
          refine ⟨10088597063501133350169793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13451462751334844466893057 10088597063501133350169793)
          ·
            refine ⟨7566447797625850012627345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10088597063501133350169793 7566447797625850012627345)
            ·
              refine ⟨5674835848219387509470509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7566447797625850012627345 5674835848219387509470509)
              ·
                refine ⟨2128063443082270316051441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5674835848219387509470509 2128063443082270316051441)
                ·
                  refine ⟨1596047582311702737038581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2128063443082270316051441 1596047582311702737038581)
                  ·
                    refine ⟨149629460841722131597367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1596047582311702737038581 149629460841722131597367)
                    ·
                      rfl

theorem cell23_874207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_874207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874207 prefixEnd_874207 := by exact prefixLift 874207
  have htrace : WordTrace (prefixWord ++ tailWord_874207) baseStart_874207 baseEnd_874207 := by
    simpa [prefixWord, tailWord_874207, baseEnd_874207] using wordTrace_append hprefix tailTrace_874207
  have hstable : (prefixWord ++ tailWord_874207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874207).length < 2 ^ (prefixWord ++ tailWord_874207).sum := by decide
  have hdescent : baseEnd_874207 < baseStart_874207 := by decide
  rcases family_descends (prefixWord ++ tailWord_874207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874227 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 4]
def baseStart_874227 : Nat := 118140960795 + 874227 * 2 ^ 59
def prefixEnd_874227 : Nat := 4983230072969 + 3 ^ 40 * 874227 * 2
def baseEnd_874227 : Nat := 448898652138256316542009

theorem tailTrace_874227 : CollatzResearch.WordTrace tailWord_874227 prefixEnd_874227 448898652138256316542009 := by
  unfold tailWord_874227
  simp only [CollatzResearch.WordTrace]
  refine ⟨31885678203832359929844935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21257118802554906619896623 31885678203832359929844935)
  ·
    refine ⟨47828517305748539894767403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31885678203832359929844935 47828517305748539894767403)
    ·
      refine ⟨71742775958622809842151105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47828517305748539894767403 71742775958622809842151105)
      ·
        refine ⟨53807081968967107381613329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71742775958622809842151105 53807081968967107381613329)
        ·
          refine ⟨40355311476725330536209997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53807081968967107381613329 40355311476725330536209997)
          ·
            refine ⟨15133241803771998951078749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40355311476725330536209997 15133241803771998951078749)
            ·
              refine ⟨5674965676414499606654531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15133241803771998951078749 5674965676414499606654531)
              ·
                refine ⟨8512448514621749409981797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674965676414499606654531 8512448514621749409981797)
                ·
                  refine ⟨1596084096491578014371587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8512448514621749409981797 1596084096491578014371587)
                  ·
                    refine ⟨2394126144737367021557381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1596084096491578014371587 2394126144737367021557381)
                    ·
                      refine ⟨448898652138256316542009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2394126144737367021557381 448898652138256316542009)
                      ·
                        rfl

theorem cell23_874227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_874227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874227 prefixEnd_874227 := by exact prefixLift 874227
  have htrace : WordTrace (prefixWord ++ tailWord_874227) baseStart_874227 baseEnd_874227 := by
    simpa [prefixWord, tailWord_874227, baseEnd_874227] using wordTrace_append hprefix tailTrace_874227
  have hstable : (prefixWord ++ tailWord_874227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874227).length < 2 ^ (prefixWord ++ tailWord_874227).sum := by decide
  have hdescent : baseEnd_874227 < baseStart_874227 := by decide
  rcases family_descends (prefixWord ++ tailWord_874227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874228 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 7]
def baseStart_874228 : Nat := 118140960795 + 874228 * 2 ^ 59
def prefixEnd_874228 : Nat := 4983230072969 + 3 ^ 40 * 874228 * 2
def baseEnd_874228 : Nat := 49877685068767868069945

theorem tailTrace_874228 : CollatzResearch.WordTrace tailWord_874228 prefixEnd_874228 49877685068767868069945 := by
  unfold tailWord_874228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15942857338414368550315669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21257143117885824733754225 15942857338414368550315669)
  ·
    refine ⟨747321437738173525796047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15942857338414368550315669 747321437738173525796047)
    ·
      refine ⟨1120982156607260288694071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747321437738173525796047 1120982156607260288694071)
      ·
        refine ⟨1681473234910890433041107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120982156607260288694071 1681473234910890433041107)
        ·
          refine ⟨2522209852366335649561661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681473234910890433041107 2522209852366335649561661)
          ·
            refine ⟨945828694637375868585623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2522209852366335649561661 945828694637375868585623)
            ·
              refine ⟨1418743041956063802878435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945828694637375868585623 1418743041956063802878435)
              ·
                refine ⟨2128114562934095704317653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418743041956063802878435 2128114562934095704317653)
                ·
                  refine ⟨49877685068767868069945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2128114562934095704317653 49877685068767868069945)
                  ·
                    rfl

theorem cell23_874228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_874228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874228 prefixEnd_874228 := by exact prefixLift 874228
  have htrace : WordTrace (prefixWord ++ tailWord_874228) baseStart_874228 baseEnd_874228 := by
    simpa [prefixWord, tailWord_874228, baseEnd_874228] using wordTrace_append hprefix tailTrace_874228
  have hstable : (prefixWord ++ tailWord_874228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874228).length < 2 ^ (prefixWord ++ tailWord_874228).sum := by decide
  have hdescent : baseEnd_874228 < baseStart_874228 := by decide
  rcases family_descends (prefixWord ++ tailWord_874228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874254 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_874254 : Nat := 118140960795 + 874254 * 2 ^ 59
def prefixEnd_874254 : Nat := 4983230072969 + 3 ^ 40 * 874254 * 2
def baseEnd_874254 : Nat := 149637505371975903634795

theorem tailTrace_874254 : CollatzResearch.WordTrace tailWord_874254 prefixEnd_874254 149637505371975903634795 := by
  unfold tailWord_874254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985832871841817942634727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21257775316489695694051877 3985832871841817942634727)
  ·
    refine ⟨5978749307762726913952091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3985832871841817942634727 5978749307762726913952091)
    ·
      refine ⟨8968123961644090370928137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5978749307762726913952091 8968123961644090370928137)
      ·
        refine ⟨6726092971233067778196103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8968123961644090370928137 6726092971233067778196103)
        ·
          refine ⟨10089139456849601667294155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726092971233067778196103 10089139456849601667294155)
          ·
            refine ⟨15133709185274402500941233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089139456849601667294155 15133709185274402500941233)
            ·
              refine ⟨11350281888955801875705925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15133709185274402500941233 11350281888955801875705925)
              ·
                refine ⟨2128177854179212851694861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11350281888955801875705925 2128177854179212851694861)
                ·
                  refine ⟨798066695317204819385573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2128177854179212851694861 798066695317204819385573)
                  ·
                    refine ⟨149637505371975903634795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 798066695317204819385573 149637505371975903634795)
                    ·
                      rfl

theorem cell23_874254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_874254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874254 prefixEnd_874254 := by exact prefixLift 874254
  have htrace : WordTrace (prefixWord ++ tailWord_874254) baseStart_874254 baseEnd_874254 := by
    simpa [prefixWord, tailWord_874254, baseEnd_874254] using wordTrace_append hprefix tailTrace_874254
  have hstable : (prefixWord ++ tailWord_874254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874254).length < 2 ^ (prefixWord ++ tailWord_874254).sum := by decide
  have hdescent : baseEnd_874254 < baseStart_874254 := by decide
  rcases family_descends (prefixWord ++ tailWord_874254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874264 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_874264 : Nat := 118140960795 + 874264 * 2 ^ 59
def prefixEnd_874264 : Nat := 4983230072969 + 3 ^ 40 * 874264 * 2
def baseEnd_874264 : Nat := 448917650922472671779339

theorem tailTrace_874264 : CollatzResearch.WordTrace tailWord_874264 prefixEnd_874264 448917650922472671779339 := by
  unfold tailWord_874264
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943513852349157624470923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21258018469798876832627897 15943513852349157624470923)
  ·
    refine ⟨23915270778523736436706385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15943513852349157624470923 23915270778523736436706385)
    ·
      refine ⟨17936453083892802327529789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23915270778523736436706385 17936453083892802327529789)
      ·
        refine ⟨6726169906459800872823671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17936453083892802327529789 6726169906459800872823671)
        ·
          refine ⟨10089254859689701309235507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726169906459800872823671 10089254859689701309235507)
          ·
            refine ⟨15133882289534551963853261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089254859689701309235507 15133882289534551963853261)
            ·
              refine ⟨5675205858575456986444973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15133882289534551963853261 5675205858575456986444973)
              ·
                refine ⟨2128202196965796369916865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5675205858575456986444973 2128202196965796369916865)
                ·
                  refine ⟨1596151647724347277437649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2128202196965796369916865 1596151647724347277437649)
                  ·
                    refine ⟨1197113735793260458078237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596151647724347277437649 1197113735793260458078237)
                    ·
                      refine ⟨448917650922472671779339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1197113735793260458078237 448917650922472671779339)
                      ·
                        rfl

theorem cell23_874264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_874264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874264 prefixEnd_874264 := by exact prefixLift 874264
  have htrace : WordTrace (prefixWord ++ tailWord_874264) baseStart_874264 baseEnd_874264 := by
    simpa [prefixWord, tailWord_874264, baseEnd_874264] using wordTrace_append hprefix tailTrace_874264
  have hstable : (prefixWord ++ tailWord_874264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874264).length < 2 ^ (prefixWord ++ tailWord_874264).sum := by decide
  have hdescent : baseEnd_874264 < baseStart_874264 := by decide
  rcases family_descends (prefixWord ++ tailWord_874264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874271 : List Nat := [1, 1, 2, 4, 2, 1, 2, 5, 1, 4]
def baseStart_874271 : Nat := 118140960795 + 874271 * 2 ^ 59
def prefixEnd_874271 : Nat := 4983230072969 + 3 ^ 40 * 874271 * 2
def baseEnd_874271 : Nat := 149640415095684714797269

theorem tailTrace_874271 : CollatzResearch.WordTrace tailWord_874271 prefixEnd_874271 149640415095684714797269 := by
  unfold tailWord_874271
  simp only [CollatzResearch.WordTrace]
  refine ⟨31887283015672955444446667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21258188677115303629631111 31887283015672955444446667)
  ·
    refine ⟨47830924523509433166670001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31887283015672955444446667 47830924523509433166670001)
    ·
      refine ⟨35873193392632074875002501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47830924523509433166670001 35873193392632074875002501)
      ·
        refine ⟨6726223761118514039062969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35873193392632074875002501 6726223761118514039062969)
        ·
          refine ⟨5044667820838885529297227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6726223761118514039062969 5044667820838885529297227)
          ·
            refine ⟨7567001731258328293945841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044667820838885529297227 7567001731258328293945841)
            ·
              refine ⟨5675251298443746220459381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567001731258328293945841 5675251298443746220459381)
              ·
                refine ⟨532054809229101208168067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5675251298443746220459381 532054809229101208168067)
                ·
                  refine ⟨798082213843651812252101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532054809229101208168067 798082213843651812252101)
                  ·
                    refine ⟨149640415095684714797269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 798082213843651812252101 149640415095684714797269)
                    ·
                      rfl

theorem cell23_874271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 4].length) (baseStart_874271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874271 prefixEnd_874271 := by exact prefixLift 874271
  have htrace : WordTrace (prefixWord ++ tailWord_874271) baseStart_874271 baseEnd_874271 := by
    simpa [prefixWord, tailWord_874271, baseEnd_874271] using wordTrace_append hprefix tailTrace_874271
  have hstable : (prefixWord ++ tailWord_874271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874271).length < 2 ^ (prefixWord ++ tailWord_874271).sum := by decide
  have hdescent : baseEnd_874271 < baseStart_874271 := by decide
  rcases family_descends (prefixWord ++ tailWord_874271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874284 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 6]
def baseStart_874284 : Nat := 118140960795 + 874284 * 2 ^ 59
def prefixEnd_874284 : Nat := 4983230072969 + 3 ^ 40 * 874284 * 2
def baseEnd_874284 : Nat := 49880880059506954836583

theorem tailTrace_874284 : CollatzResearch.WordTrace tailWord_874284 prefixEnd_874284 49880880059506954836583 := by
  unfold tailWord_874284
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943878582312929332334953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21258504776417239109779937 15943878582312929332334953)
  ·
    refine ⟨11957908936734696999251215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15943878582312929332334953 11957908936734696999251215)
    ·
      refine ⟨17936863405102045498876823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11957908936734696999251215 17936863405102045498876823)
      ·
        refine ⟨26905295107653068248315235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17936863405102045498876823 26905295107653068248315235)
        ·
          refine ⟨40357942661479602372472853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26905295107653068248315235 40357942661479602372472853)
          ·
            refine ⟨1891778562256856361209665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40357942661479602372472853 1891778562256856361209665)
            ·
              refine ⟨1418833921692642270907249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891778562256856361209665 1418833921692642270907249)
              ·
                refine ⟨1064125441269481703180437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418833921692642270907249 1064125441269481703180437)
                ·
                  refine ⟨49880880059506954836583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1064125441269481703180437 49880880059506954836583)
                  ·
                    rfl

theorem cell23_874284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_874284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874284 prefixEnd_874284 := by exact prefixLift 874284
  have htrace : WordTrace (prefixWord ++ tailWord_874284) baseStart_874284 baseEnd_874284 := by
    simpa [prefixWord, tailWord_874284, baseEnd_874284] using wordTrace_append hprefix tailTrace_874284
  have hstable : (prefixWord ++ tailWord_874284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874284).length < 2 ^ (prefixWord ++ tailWord_874284).sum := by decide
  have hdescent : baseEnd_874284 < baseStart_874284 := by decide
  rcases family_descends (prefixWord ++ tailWord_874284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874314 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_874314 : Nat := 118140960795 + 874314 * 2 ^ 59
def prefixEnd_874314 : Nat := 4983230072969 + 3 ^ 40 * 874314 * 2
def baseEnd_874314 : Nat := 149647774985065825384703

theorem tailTrace_874314 : CollatzResearch.WordTrace tailWord_874314 prefixEnd_874314 149647774985065825384703 := by
  unfold tailWord_874314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7972212838629293447065499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21259234236344782525507997 7972212838629293447065499)
  ·
    refine ⟨11958319257943940170598249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7972212838629293447065499 11958319257943940170598249)
    ·
      refine ⟨8968739443457955127948687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11958319257943940170598249 8968739443457955127948687)
      ·
        refine ⟨13453109165186932691923031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8968739443457955127948687 13453109165186932691923031)
        ·
          refine ⟨20179663747780399037884547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13453109165186932691923031 20179663747780399037884547)
          ·
            refine ⟨30269495621670598556826821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20179663747780399037884547 30269495621670598556826821)
            ·
              refine ⟨5675530429063237229405029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30269495621670598556826821 5675530429063237229405029)
              ·
                refine ⟨1064161955449356980513443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5675530429063237229405029 1064161955449356980513443)
                ·
                  refine ⟨1596242933174035470770165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064161955449356980513443 1596242933174035470770165)
                  ·
                    refine ⟨149647774985065825384703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1596242933174035470770165 149647774985065825384703)
                    ·
                      rfl

theorem cell23_874314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_874314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874314 prefixEnd_874314 := by exact prefixLift 874314
  have htrace : WordTrace (prefixWord ++ tailWord_874314) baseStart_874314 baseEnd_874314 := by
    simpa [prefixWord, tailWord_874314, baseEnd_874314] using wordTrace_append hprefix tailTrace_874314
  have hstable : (prefixWord ++ tailWord_874314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874314).length < 2 ^ (prefixWord ++ tailWord_874314).sum := by decide
  have hdescent : baseEnd_874314 < baseStart_874314 := by decide
  rcases family_descends (prefixWord ++ tailWord_874314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874321 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 1, 5, 2]
def baseStart_874321 : Nat := 118140960795 + 874321 * 2 ^ 59
def prefixEnd_874321 : Nat := 4983230072969 + 3 ^ 40 * 874321 * 2
def baseEnd_874321 : Nat := 448946919319778948766577

theorem tailTrace_874321 : CollatzResearch.WordTrace tailWord_874321 prefixEnd_874321 448946919319778948766577 := by
  unfold tailWord_874321
  simp only [CollatzResearch.WordTrace]
  refine ⟨31889106665491813983766817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21259404443661209322511211 31889106665491813983766817)
  ·
    refine ⟨23916829999118860487825113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31889106665491813983766817 23916829999118860487825113)
    ·
      refine ⟨17937622499339145365868835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23916829999118860487825113 17937622499339145365868835)
      ·
        refine ⟨26906433749008718048803253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17937622499339145365868835 26906433749008718048803253)
        ·
          refine ⟨2522478163969567317075305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26906433749008718048803253 2522478163969567317075305)
          ·
            refine ⟨1891858622977175487806479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2522478163969567317075305 1891858622977175487806479)
            ·
              refine ⟨2837787934465763231709719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891858622977175487806479 2837787934465763231709719)
              ·
                refine ⟨4256681901698644847564579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2837787934465763231709719 4256681901698644847564579)
                ·
                  refine ⟨6385022852547967271346869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256681901698644847564579 6385022852547967271346869)
                  ·
                    refine ⟨598595892426371931688769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6385022852547967271346869 598595892426371931688769)
                    ·
                      refine ⟨448946919319778948766577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598595892426371931688769 448946919319778948766577)
                      ·
                        rfl

theorem cell23_874321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_874321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874321 prefixEnd_874321 := by exact prefixLift 874321
  have htrace : WordTrace (prefixWord ++ tailWord_874321) baseStart_874321 baseEnd_874321 := by
    simpa [prefixWord, tailWord_874321, baseEnd_874321] using wordTrace_append hprefix tailTrace_874321
  have hstable : (prefixWord ++ tailWord_874321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874321).length < 2 ^ (prefixWord ++ tailWord_874321).sum := by decide
  have hdescent : baseEnd_874321 < baseStart_874321 := by decide
  rcases family_descends (prefixWord ++ tailWord_874321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874347 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6]
def baseStart_874347 : Nat := 118140960795 + 874347 * 2 ^ 59
def prefixEnd_874347 : Nat := 4983230072969 + 3 ^ 40 * 874347 * 2
def baseEnd_874347 : Nat := 448960269816795847041457

theorem tailTrace_874347 : CollatzResearch.WordTrace tailWord_874347 prefixEnd_874347 448960269816795847041457 := by
  unfold tailWord_874347
  simp only [CollatzResearch.WordTrace]
  refine ⟨31890054963397620424213295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21260036642265080282808863 31890054963397620424213295)
  ·
    refine ⟨47835082445096430636319943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31890054963397620424213295 47835082445096430636319943)
    ·
      refine ⟨71752623667644645954479915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47835082445096430636319943 71752623667644645954479915)
      ·
        refine ⟨107628935501466968931719873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71752623667644645954479915 107628935501466968931719873)
        ·
          refine ⟨80721701626100226698789905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107628935501466968931719873 80721701626100226698789905)
          ·
            refine ⟨60541276219575170024092429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80721701626100226698789905 60541276219575170024092429)
            ·
              refine ⟨22702978582340688759034661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60541276219575170024092429 22702978582340688759034661)
              ·
                refine ⟨4256808484188879142318999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22702978582340688759034661 4256808484188879142318999)
                ·
                  refine ⟨6385212726283318713478499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256808484188879142318999 6385212726283318713478499)
                  ·
                    refine ⟨9577819089424978070217749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6385212726283318713478499 9577819089424978070217749)
                    ·
                      refine ⟨448960269816795847041457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9577819089424978070217749 448960269816795847041457)
                      ·
                        rfl

theorem cell23_874347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_874347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874347 prefixEnd_874347 := by exact prefixLift 874347
  have htrace : WordTrace (prefixWord ++ tailWord_874347) baseStart_874347 baseEnd_874347 := by
    simpa [prefixWord, tailWord_874347, baseEnd_874347] using wordTrace_append hprefix tailTrace_874347
  have hstable : (prefixWord ++ tailWord_874347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874347).length < 2 ^ (prefixWord ++ tailWord_874347).sum := by decide
  have hdescent : baseEnd_874347 < baseStart_874347 := by decide
  rcases family_descends (prefixWord ++ tailWord_874347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874371 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 3]
def baseStart_874371 : Nat := 118140960795 + 874371 * 2 ^ 59
def prefixEnd_874371 : Nat := 4983230072969 + 3 ^ 40 * 874371 * 2
def baseEnd_874371 : Nat := 448972593352503753141347

theorem tailTrace_874371 : CollatzResearch.WordTrace tailWord_874371 prefixEnd_874371 448972593352503753141347 := by
  unfold tailWord_874371
  simp only [CollatzResearch.WordTrace]
  refine ⟨31890930315310672523086967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21260620210207115015391311 31890930315310672523086967)
  ·
    refine ⟨47836395472966008784630451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31890930315310672523086967 47836395472966008784630451)
    ·
      refine ⟨71754593209449013176945677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47836395472966008784630451 71754593209449013176945677)
      ·
        refine ⟨26907972453543379941354629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71754593209449013176945677 26907972453543379941354629)
        ·
          refine ⟨5045244835039383739003993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26907972453543379941354629 5045244835039383739003993)
          ·
            refine ⟨3783933626279537804252995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5045244835039383739003993 3783933626279537804252995)
            ·
              refine ⟨5675900439419306706379493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3783933626279537804252995 5675900439419306706379493)
              ·
                refine ⟨1064231332391120007446155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5675900439419306706379493 1064231332391120007446155)
                ·
                  refine ⟨1596346998586680011169233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064231332391120007446155 1596346998586680011169233)
                  ·
                    refine ⟨1197260248940010008376925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596346998586680011169233 1197260248940010008376925)
                    ·
                      refine ⟨448972593352503753141347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1197260248940010008376925 448972593352503753141347)
                      ·
                        rfl

theorem cell23_874371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_874371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874371 prefixEnd_874371 := by exact prefixLift 874371
  have htrace : WordTrace (prefixWord ++ tailWord_874371) baseStart_874371 baseEnd_874371 := by
    simpa [prefixWord, tailWord_874371, baseEnd_874371] using wordTrace_append hprefix tailTrace_874371
  have hstable : (prefixWord ++ tailWord_874371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874371).length < 2 ^ (prefixWord ++ tailWord_874371).sum := by decide
  have hdescent : baseEnd_874371 < baseStart_874371 := by decide
  rcases family_descends (prefixWord ++ tailWord_874371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874385 : List Nat := [1, 2, 2, 1, 1, 1, 7, 3, 1, 2, 2]
def baseStart_874385 : Nat := 118140960795 + 874385 * 2 ^ 59
def prefixEnd_874385 : Nat := 4983230072969 + 3 ^ 40 * 874385 * 2
def baseEnd_874385 : Nat := 448979782081666698366283

theorem tailTrace_874385 : CollatzResearch.WordTrace tailWord_874385 prefixEnd_874385 448979782081666698366283 := by
  unfold tailWord_874385
  simp only [CollatzResearch.WordTrace]
  refine ⟨31891440937259952914096609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21260960624839968609397739 31891440937259952914096609)
  ·
    refine ⟨23918580702944964685572457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31891440937259952914096609 23918580702944964685572457)
    ·
      refine ⟨17938935527208723514179343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23918580702944964685572457 17938935527208723514179343)
      ·
        refine ⟨26908403290813085271269015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17938935527208723514179343 26908403290813085271269015)
        ·
          refine ⟨40362604936219627906903523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26908403290813085271269015 40362604936219627906903523)
          ·
            refine ⟨60543907404329441860355285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40362604936219627906903523 60543907404329441860355285)
            ·
              refine ⟨1418997829788971293602077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60543907404329441860355285 1418997829788971293602077)
              ·
                refine ⟨532124186170864235100779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1418997829788971293602077 532124186170864235100779)
                ·
                  refine ⟨798186279256296352651169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532124186170864235100779 798186279256296352651169)
                  ·
                    refine ⟨598639709442222264488377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 798186279256296352651169 598639709442222264488377)
                    ·
                      refine ⟨448979782081666698366283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598639709442222264488377 448979782081666698366283)
                      ·
                        rfl

theorem cell23_874385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_874385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874385 prefixEnd_874385 := by exact prefixLift 874385
  have htrace : WordTrace (prefixWord ++ tailWord_874385) baseStart_874385 baseEnd_874385 := by
    simpa [prefixWord, tailWord_874385, baseEnd_874385] using wordTrace_append hprefix tailTrace_874385
  have hstable : (prefixWord ++ tailWord_874385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874385).length < 2 ^ (prefixWord ++ tailWord_874385).sum := by decide
  have hdescent : baseEnd_874385 < baseStart_874385 := by decide
  rcases family_descends (prefixWord ++ tailWord_874385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874388 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_874388 : Nat := 118140960795 + 874388 * 2 ^ 59
def prefixEnd_874388 : Nat := 4983230072969 + 3 ^ 40 * 874388 * 2
def baseEnd_874388 : Nat := 448981322523630186628769

theorem tailTrace_874388 : CollatzResearch.WordTrace tailWord_874388 prefixEnd_874388 448981322523630186628769 := by
  unfold tailWord_874388
  simp only [CollatzResearch.WordTrace]
  refine ⟨15945775178124542213227909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21261033570832722950970545 15945775178124542213227909)
  ·
    refine ⟨2989832845898351664980233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15945775178124542213227909 2989832845898351664980233)
    ·
      refine ⟨2242374634423763748735175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2989832845898351664980233 2242374634423763748735175)
      ·
        refine ⟨3363561951635645623102763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242374634423763748735175 3363561951635645623102763)
        ·
          refine ⟨5045342927453468434654145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3363561951635645623102763 5045342927453468434654145)
          ·
            refine ⟨3784007195590101325990609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5045342927453468434654145 3784007195590101325990609)
            ·
              refine ⟨2838005396692575994492957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3784007195590101325990609 2838005396692575994492957)
              ·
                refine ⟨1064252023759715997934859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2838005396692575994492957 1064252023759715997934859)
                ·
                  refine ⟨1596378035639573996902289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064252023759715997934859 1596378035639573996902289)
                  ·
                    refine ⟨1197283526729680497676717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1596378035639573996902289 1197283526729680497676717)
                    ·
                      refine ⟨448981322523630186628769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1197283526729680497676717 448981322523630186628769)
                      ·
                        rfl

theorem cell23_874388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_874388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874388 prefixEnd_874388 := by exact prefixLift 874388
  have htrace : WordTrace (prefixWord ++ tailWord_874388) baseStart_874388 baseEnd_874388 := by
    simpa [prefixWord, tailWord_874388, baseEnd_874388] using wordTrace_append hprefix tailTrace_874388
  have hstable : (prefixWord ++ tailWord_874388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874388).length < 2 ^ (prefixWord ++ tailWord_874388).sum := by decide
  have hdescent : baseEnd_874388 < baseStart_874388 := by decide
  rcases family_descends (prefixWord ++ tailWord_874388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874402 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_874402 : Nat := 118140960795 + 874402 * 2 ^ 59
def prefixEnd_874402 : Nat := 4983230072969 + 3 ^ 40 * 874402 * 2
def baseEnd_874402 : Nat := 448988511252793131853705

theorem tailTrace_874402 : CollatzResearch.WordTrace tailWord_874402 prefixEnd_874402 448988511252793131853705 := by
  unfold tailWord_874402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7973015244549591204366365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21261373985465576544976973 7973015244549591204366365)
  ·
    refine ⟨2989880716706096701637387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7973015244549591204366365 2989880716706096701637387)
    ·
      refine ⟨4484821075059145052456081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989880716706096701637387 4484821075059145052456081)
      ·
        refine ⟨3363615806294358789342061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4484821075059145052456081 3363615806294358789342061)
        ·
          refine ⟨1261355927360384546003273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3363615806294358789342061 1261355927360384546003273)
          ·
            refine ⟨946016945520288409502455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261355927360384546003273 946016945520288409502455)
            ·
              refine ⟨1419025418280432614253683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946016945520288409502455 1419025418280432614253683)
              ·
                refine ⟨2128538127420648921380525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419025418280432614253683 2128538127420648921380525)
                ·
                  refine ⟨798201797782743345517697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2128538127420648921380525 798201797782743345517697)
                  ·
                    refine ⟨598651348337057509138273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 798201797782743345517697 598651348337057509138273)
                    ·
                      refine ⟨448988511252793131853705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598651348337057509138273 448988511252793131853705)
                      ·
                        rfl

theorem cell23_874402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_874402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874402 prefixEnd_874402 := by exact prefixLift 874402
  have htrace : WordTrace (prefixWord ++ tailWord_874402) baseStart_874402 baseEnd_874402 := by
    simpa [prefixWord, tailWord_874402, baseEnd_874402] using wordTrace_append hprefix tailTrace_874402
  have hstable : (prefixWord ++ tailWord_874402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874402).length < 2 ^ (prefixWord ++ tailWord_874402).sum := by decide
  have hdescent : baseEnd_874402 < baseStart_874402 := by decide
  rcases family_descends (prefixWord ++ tailWord_874402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874408 : List Nat := [2, 1, 6, 2, 1, 1, 2, 8]
def baseStart_874408 : Nat := 118140960795 + 874408 * 2 ^ 59
def prefixEnd_874408 : Nat := 4983230072969 + 3 ^ 40 * 874408 * 2
def baseEnd_874408 : Nat := 16629318227285929939951

theorem tailTrace_874408 : CollatzResearch.WordTrace tailWord_874408 prefixEnd_874408 16629318227285929939951 := by
  unfold tailWord_874408
  simp only [CollatzResearch.WordTrace]
  refine ⟨15946139908088313921091939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21261519877451085228122585 15946139908088313921091939)
  ·
    refine ⟨23919209862132470881637909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15946139908088313921091939 23919209862132470881637909)
    ·
      refine ⟨1121212962287459572576777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23919209862132470881637909 1121212962287459572576777)
      ·
        refine ⟨840909721715594679432583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1121212962287459572576777 840909721715594679432583)
        ·
          refine ⟨1261364582573392019148875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840909721715594679432583 1261364582573392019148875)
          ·
            refine ⟨1892046873860088028723313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261364582573392019148875 1892046873860088028723313)
            ·
              refine ⟨1419035155395066021542485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892046873860088028723313 1419035155395066021542485)
              ·
                refine ⟨16629318227285929939951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1419035155395066021542485 16629318227285929939951)
                ·
                  rfl

theorem cell23_874408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 8].length) (baseStart_874408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874408 prefixEnd_874408 := by exact prefixLift 874408
  have htrace : WordTrace (prefixWord ++ tailWord_874408) baseStart_874408 baseEnd_874408 := by
    simpa [prefixWord, tailWord_874408, baseEnd_874408] using wordTrace_append hprefix tailTrace_874408
  have hstable : (prefixWord ++ tailWord_874408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874408).length < 2 ^ (prefixWord ++ tailWord_874408).sum := by decide
  have hdescent : baseEnd_874408 < baseStart_874408 := by decide
  rcases family_descends (prefixWord ++ tailWord_874408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874441 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 1, 4, 2]
def baseStart_874441 : Nat := 118140960795 + 874441 * 2 ^ 59
def prefixEnd_874441 : Nat := 4983230072969 + 3 ^ 40 * 874441 * 2
def baseEnd_874441 : Nat := 449008536998318479266025

theorem tailTrace_874441 : CollatzResearch.WordTrace tailWord_874441 prefixEnd_874441 449008536998318479266025 := by
  unfold tailWord_874441
  simp only [CollatzResearch.WordTrace]
  refine ⟨31893483425057074478135177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21262322283371382985423451 31893483425057074478135177)
  ·
    refine ⟨23920112568792805858601383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31893483425057074478135177 23920112568792805858601383)
    ·
      refine ⟨35880168853189208787902075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23920112568792805858601383 35880168853189208787902075)
      ·
        refine ⟨53820253279783813181853113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35880168853189208787902075 53820253279783813181853113)
        ·
          refine ⟨40365189959837859886389835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53820253279783813181853113 40365189959837859886389835)
          ·
            refine ⟨60547784939756789829584753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40365189959837859886389835 60547784939756789829584753)
            ·
              refine ⟨45410838704817592372188565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60547784939756789829584753 45410838704817592372188565)
              ·
                refine ⟨2128633064288324642446339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45410838704817592372188565 2128633064288324642446339)
                ·
                  refine ⟨3192949596432486963669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128633064288324642446339 3192949596432486963669509)
                  ·
                    refine ⟨598678049331091305688033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3192949596432486963669509 598678049331091305688033)
                    ·
                      refine ⟨449008536998318479266025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598678049331091305688033 449008536998318479266025)
                      ·
                        rfl

theorem cell23_874441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 4, 2].length) (baseStart_874441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874441 prefixEnd_874441 := by exact prefixLift 874441
  have htrace : WordTrace (prefixWord ++ tailWord_874441) baseStart_874441 baseEnd_874441 := by
    simpa [prefixWord, tailWord_874441, baseEnd_874441] using wordTrace_append hprefix tailTrace_874441
  have hstable : (prefixWord ++ tailWord_874441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874441).length < 2 ^ (prefixWord ++ tailWord_874441).sum := by decide
  have hdescent : baseEnd_874441 < baseStart_874441 := by decide
  rcases family_descends (prefixWord ++ tailWord_874441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874481 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 7]
def baseStart_874481 : Nat := 118140960795 + 874481 * 2 ^ 59
def prefixEnd_874481 : Nat := 4983230072969 + 3 ^ 40 * 874481 * 2
def baseEnd_874481 : Nat := 49892119580499813640649

theorem tailTrace_874481 : CollatzResearch.WordTrace tailWord_874481 prefixEnd_874481 49892119580499813640649 := by
  unfold tailWord_874481
  simp only [CollatzResearch.WordTrace]
  refine ⟨31894942344912161309591297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21263294896608107539727531 31894942344912161309591297)
  ·
    refine ⟨23921206758684120982193473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31894942344912161309591297 23921206758684120982193473)
    ·
      refine ⟨17940905069013090736645105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23921206758684120982193473 17940905069013090736645105)
      ·
        refine ⟨13455678801759818052483829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17940905069013090736645105 13455678801759818052483829)
        ·
          refine ⟨1261469887664982942420359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13455678801759818052483829 1261469887664982942420359)
          ·
            refine ⟨1892204831497474413630539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261469887664982942420359 1892204831497474413630539)
            ·
              refine ⟨2838307247246211620445809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892204831497474413630539 2838307247246211620445809)
              ·
                refine ⟨2128730435434658715334357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2838307247246211620445809 2128730435434658715334357)
                ·
                  refine ⟨49892119580499813640649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2128730435434658715334357 49892119580499813640649)
                  ·
                    rfl

theorem cell23_874481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 7].length) (baseStart_874481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874481 prefixEnd_874481 := by exact prefixLift 874481
  have htrace : WordTrace (prefixWord ++ tailWord_874481) baseStart_874481 baseEnd_874481 := by
    simpa [prefixWord, tailWord_874481, baseEnd_874481] using wordTrace_append hprefix tailTrace_874481
  have hstable : (prefixWord ++ tailWord_874481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874481).length < 2 ^ (prefixWord ++ tailWord_874481).sum := by decide
  have hdescent : baseEnd_874481 < baseStart_874481 := by decide
  rcases family_descends (prefixWord ++ tailWord_874481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874551 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_874551 : Nat := 118140960795 + 874551 * 2 ^ 59
def prefixEnd_874551 : Nat := 4983230072969 + 3 ^ 40 * 874551 * 2
def baseEnd_874551 : Nat := 449065019870313048890519

theorem tailTrace_874551 : CollatzResearch.WordTrace tailWord_874551 prefixEnd_874551 449065019870313048890519 := by
  unfold tailWord_874551
  simp only [CollatzResearch.WordTrace]
  refine ⟨31897495454658563264639507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21264996969772375509759671 31897495454658563264639507)
  ·
    refine ⟨47846243181987844896959261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31897495454658563264639507 47846243181987844896959261)
    ·
      refine ⟨17942341193245441836359723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47846243181987844896959261 17942341193245441836359723)
      ·
        refine ⟨26913511789868162754539585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17942341193245441836359723 26913511789868162754539585)
        ·
          refine ⟨20185133842401122065904689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26913511789868162754539585 20185133842401122065904689)
          ·
            refine ⟨15138850381800841549428517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20185133842401122065904689 15138850381800841549428517)
            ·
              refine ⟨2838534446587657790517847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15138850381800841549428517 2838534446587657790517847)
              ·
                refine ⟨4257801669881486685776771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838534446587657790517847 4257801669881486685776771)
                ·
                  refine ⟨6386702504822230028665157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4257801669881486685776771 6386702504822230028665157)
                  ·
                    refine ⟨1197506719654168130374717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6386702504822230028665157 1197506719654168130374717)
                    ·
                      refine ⟨449065019870313048890519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1197506719654168130374717 449065019870313048890519)
                      ·
                        rfl

theorem cell23_874551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_874551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874551 prefixEnd_874551 := by exact prefixLift 874551
  have htrace : WordTrace (prefixWord ++ tailWord_874551) baseStart_874551 baseEnd_874551 := by
    simpa [prefixWord, tailWord_874551, baseEnd_874551] using wordTrace_append hprefix tailTrace_874551
  have hstable : (prefixWord ++ tailWord_874551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874551).length < 2 ^ (prefixWord ++ tailWord_874551).sum := by decide
  have hdescent : baseEnd_874551 < baseStart_874551 := by decide
  rcases family_descends (prefixWord ++ tailWord_874551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874588 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 6]
def baseStart_874588 : Nat := 118140960795 + 874588 * 2 ^ 59
def prefixEnd_874588 : Nat := 4983230072969 + 3 ^ 40 * 874588 * 2
def baseEnd_874588 : Nat := 49898224294947711569761

theorem tailTrace_874588 : CollatzResearch.WordTrace tailWord_874588 prefixEnd_874588 49898224294947711569761 := by
  unfold tailWord_874588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15949422477762259291868209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21265896637016345722490945 15949422477762259291868209)
  ·
    refine ⟨11962066858321694468901157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15949422477762259291868209 11962066858321694468901157)
    ·
      refine ⟨2242887535935317712918967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11962066858321694468901157 2242887535935317712918967)
      ·
        refine ⟨3364331303902976569378451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242887535935317712918967 3364331303902976569378451)
        ·
          refine ⟨5046496955854464854067677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3364331303902976569378451 5046496955854464854067677)
          ·
            refine ⟨1892436358445424320275379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5046496955854464854067677 1892436358445424320275379)
            ·
              refine ⟨2838654537668136480413069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892436358445424320275379 2838654537668136480413069)
              ·
                refine ⟨1064495451625551180154901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2838654537668136480413069 1064495451625551180154901)
                ·
                  refine ⟨49898224294947711569761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1064495451625551180154901 49898224294947711569761)
                  ·
                    rfl

theorem cell23_874588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_874588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874588 prefixEnd_874588 := by exact prefixLift 874588
  have htrace : WordTrace (prefixWord ++ tailWord_874588) baseStart_874588 baseEnd_874588 := by
    simpa [prefixWord, tailWord_874588, baseEnd_874588] using wordTrace_append hprefix tailTrace_874588
  have hstable : (prefixWord ++ tailWord_874588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874588).length < 2 ^ (prefixWord ++ tailWord_874588).sum := by decide
  have hdescent : baseEnd_874588 < baseStart_874588 := by decide
  rcases family_descends (prefixWord ++ tailWord_874588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874601 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 3, 5]
def baseStart_874601 : Nat := 118140960795 + 874601 * 2 ^ 59
def prefixEnd_874601 : Nat := 4983230072969 + 3 ^ 40 * 874601 * 2
def baseEnd_874601 : Nat := 149696897967679284421763

theorem tailTrace_874601 : CollatzResearch.WordTrace tailWord_874601 prefixEnd_874601 149696897967679284421763 := by
  unfold tailWord_874601
  simp only [CollatzResearch.WordTrace]
  refine ⟨31899319104477421803959657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21266212736318281202639771 31899319104477421803959657)
  ·
    refine ⟨23924489328358066352969743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31899319104477421803959657 23924489328358066352969743)
    ·
      refine ⟨35886733992537099529454615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23924489328358066352969743 35886733992537099529454615)
      ·
        refine ⟨53830100988805649294181923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35886733992537099529454615 53830100988805649294181923)
        ·
          refine ⟨80745151483208473941272885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53830100988805649294181923 80745151483208473941272885)
          ·
            refine ⟨7569857951550794431994333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80745151483208473941272885 7569857951550794431994333)
            ·
              refine ⟨2838696731831547911997875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7569857951550794431994333 2838696731831547911997875)
              ·
                refine ⟨4258045097747321867996813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838696731831547911997875 4258045097747321867996813)
                ·
                  refine ⟨1596766911655245700498805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4258045097747321867996813 1596766911655245700498805)
                  ·
                    refine ⟨149696897967679284421763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1596766911655245700498805 149696897967679284421763)
                    ·
                      rfl

theorem cell23_874601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_874601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874601 prefixEnd_874601 := by exact prefixLift 874601
  have htrace : WordTrace (prefixWord ++ tailWord_874601) baseStart_874601 baseEnd_874601 := by
    simpa [prefixWord, tailWord_874601, baseEnd_874601] using wordTrace_append hprefix tailTrace_874601
  have hstable : (prefixWord ++ tailWord_874601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874601).length < 2 ^ (prefixWord ++ tailWord_874601).sum := by decide
  have hdescent : baseEnd_874601 < baseStart_874601 := by decide
  rcases family_descends (prefixWord ++ tailWord_874601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874666 : List Nat := [3, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_874666 : Nat := 118140960795 + 874666 * 2 ^ 59
def prefixEnd_874666 : Nat := 4983230072969 + 3 ^ 40 * 874666 * 2
def baseEnd_874666 : Nat := 449124070145580098952491

theorem tailTrace_874666 : CollatzResearch.WordTrace tailWord_874666 prefixEnd_874666 449124070145580098952491 := by
  unfold tailWord_874666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7975422462310484476268963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21267793232827958603383901 7975422462310484476268963)
  ·
    refine ⟨11963133693465726714403445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7975422462310484476268963 11963133693465726714403445)
    ·
      refine ⟨1121543783762411879475323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11963133693465726714403445 1121543783762411879475323)
      ·
        refine ⟨1682315675643617819212985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121543783762411879475323 1682315675643617819212985)
        ·
          refine ⟨1261736756732713364409739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682315675643617819212985 1261736756732713364409739)
          ·
            refine ⟨1892605135099070046614609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261736756732713364409739 1892605135099070046614609)
            ·
              refine ⟨1419453851324302534960957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892605135099070046614609 1419453851324302534960957)
              ·
                refine ⟨532295194246613450610359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1419453851324302534960957 532295194246613450610359)
                ·
                  refine ⟨798442791369920175915539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532295194246613450610359 798442791369920175915539)
                  ·
                    refine ⟨1197664187054880263873309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 798442791369920175915539 1197664187054880263873309)
                    ·
                      refine ⟨449124070145580098952491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1197664187054880263873309 449124070145580098952491)
                      ·
                        rfl

theorem cell23_874666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_874666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874666 prefixEnd_874666 := by exact prefixLift 874666
  have htrace : WordTrace (prefixWord ++ tailWord_874666) baseStart_874666 baseEnd_874666 := by
    simpa [prefixWord, tailWord_874666, baseEnd_874666] using wordTrace_append hprefix tailTrace_874666
  have hstable : (prefixWord ++ tailWord_874666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874666).length < 2 ^ (prefixWord ++ tailWord_874666).sum := by decide
  have hdescent : baseEnd_874666 < baseStart_874666 := by decide
  rcases family_descends (prefixWord ++ tailWord_874666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874705 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_874705 : Nat := 118140960795 + 874705 * 2 ^ 59
def prefixEnd_874705 : Nat := 4983230072969 + 3 ^ 40 * 874705 * 2
def baseEnd_874705 : Nat := 449144095891105446364811

theorem tailTrace_874705 : CollatzResearch.WordTrace tailWord_874705 prefixEnd_874705 449144095891105446364811 := by
  unfold tailWord_874705
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903112296100647565745569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21268741530733765043830379 31903112296100647565745569)
  ·
    refine ⟨23927334222075485674309177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31903112296100647565745569 23927334222075485674309177)
    ·
      refine ⟨17945500666556614255731883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23927334222075485674309177 17945500666556614255731883)
      ·
        refine ⟨26918250999834921383597825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17945500666556614255731883 26918250999834921383597825)
        ·
          refine ⟨20188688249876191037698369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26918250999834921383597825 20188688249876191037698369)
          ·
            refine ⟨15141516187407143278273777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20188688249876191037698369 15141516187407143278273777)
            ·
              refine ⟨11356137140555357458705333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15141516187407143278273777 11356137140555357458705333)
              ·
                refine ⟨1064637856927064761753625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11356137140555357458705333 1064637856927064761753625)
                ·
                  refine ⟨798478392695298571315219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1064637856927064761753625 798478392695298571315219)
                  ·
                    refine ⟨1197717589042947856972829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 798478392695298571315219 1197717589042947856972829)
                    ·
                      refine ⟨449144095891105446364811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1197717589042947856972829 449144095891105446364811)
                      ·
                        rfl

theorem cell23_874705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_874705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874705 prefixEnd_874705 := by exact prefixLift 874705
  have htrace : WordTrace (prefixWord ++ tailWord_874705) baseStart_874705 baseEnd_874705 := by
    simpa [prefixWord, tailWord_874705, baseEnd_874705] using wordTrace_append hprefix tailTrace_874705
  have hstable : (prefixWord ++ tailWord_874705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874705).length < 2 ^ (prefixWord ++ tailWord_874705).sum := by decide
  have hdescent : baseEnd_874705 < baseStart_874705 := by decide
  rcases family_descends (prefixWord ++ tailWord_874705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874715 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 1, 3, 2]
def baseStart_874715 : Nat := 118140960795 + 874715 * 2 ^ 59
def prefixEnd_874715 : Nat := 4983230072969 + 3 ^ 40 * 874715 * 2
def baseEnd_874715 : Nat := 449149230697650407239765

theorem tailTrace_874715 : CollatzResearch.WordTrace tailWord_874715 prefixEnd_874715 449149230697650407239765 := by
  unfold tailWord_874715
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903477026064419273609599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21268984684042946182406399 31903477026064419273609599)
  ·
    refine ⟨47855215539096628910414399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31903477026064419273609599 47855215539096628910414399)
    ·
      refine ⟨71782823308644943365621599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47855215539096628910414399 71782823308644943365621599)
      ·
        refine ⟨107674234962967415048432399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71782823308644943365621599 107674234962967415048432399)
        ·
          refine ⟨161511352444451122572648599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107674234962967415048432399 161511352444451122572648599)
          ·
            refine ⟨242267028666676683858972899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161511352444451122572648599 242267028666676683858972899)
            ·
              refine ⟨363400543000015025788459349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242267028666676683858972899 363400543000015025788459349)
              ·
                refine ⟨1064650028320356520864627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 363400543000015025788459349 1064650028320356520864627)
                ·
                  refine ⟨1596975042480534781296941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064650028320356520864627 1596975042480534781296941)
                  ·
                    refine ⟨598865640930200542986353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1596975042480534781296941 598865640930200542986353)
                    ·
                      refine ⟨449149230697650407239765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598865640930200542986353 449149230697650407239765)
                      ·
                        rfl

theorem cell23_874715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 3, 2].length) (baseStart_874715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874715 prefixEnd_874715 := by exact prefixLift 874715
  have htrace : WordTrace (prefixWord ++ tailWord_874715) baseStart_874715 baseEnd_874715 := by
    simpa [prefixWord, tailWord_874715, baseEnd_874715] using wordTrace_append hprefix tailTrace_874715
  have hstable : (prefixWord ++ tailWord_874715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874715).length < 2 ^ (prefixWord ++ tailWord_874715).sum := by decide
  have hdescent : baseEnd_874715 < baseStart_874715 := by decide
  rcases family_descends (prefixWord ++ tailWord_874715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874723 : List Nat := [1, 1, 1, 8, 1, 2, 1, 3, 1, 2, 2]
def baseStart_874723 : Nat := 118140960795 + 874723 * 2 ^ 59
def prefixEnd_874723 : Nat := 4983230072969 + 3 ^ 40 * 874723 * 2
def baseEnd_874723 : Nat := 449153338542886375939729

theorem tailTrace_874723 : CollatzResearch.WordTrace tailWord_874723 prefixEnd_874723 449153338542886375939729 := by
  unfold tailWord_874723
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903768810035436639900823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21269179206690291093267215 31903768810035436639900823)
  ·
    refine ⟨47855653215053154959851235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31903768810035436639900823 47855653215053154959851235)
    ·
      refine ⟨71783479822579732439776853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47855653215053154959851235 71783479822579732439776853)
      ·
        refine ⟨841212654170856239528635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 71783479822579732439776853 841212654170856239528635)
        ·
          refine ⟨1261818981256284359292953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841212654170856239528635 1261818981256284359292953)
          ·
            refine ⟨946364235942213269469715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261818981256284359292953 946364235942213269469715)
            ·
              refine ⟨1419546353913319904204573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946364235942213269469715 1419546353913319904204573)
              ·
                refine ⟨532329882717494964076715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1419546353913319904204573 532329882717494964076715)
                ·
                  refine ⟨798494824076242446115073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532329882717494964076715 798494824076242446115073)
                  ·
                    refine ⟨598871118057181834586305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 798494824076242446115073 598871118057181834586305)
                    ·
                      refine ⟨449153338542886375939729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598871118057181834586305 449153338542886375939729)
                      ·
                        rfl

theorem cell23_874723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_874723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874723 prefixEnd_874723 := by exact prefixLift 874723
  have htrace : WordTrace (prefixWord ++ tailWord_874723) baseStart_874723 baseEnd_874723 := by
    simpa [prefixWord, tailWord_874723, baseEnd_874723] using wordTrace_append hprefix tailTrace_874723
  have hstable : (prefixWord ++ tailWord_874723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874723).length < 2 ^ (prefixWord ++ tailWord_874723).sum := by decide
  have hdescent : baseEnd_874723 < baseStart_874723 := by decide
  rcases family_descends (prefixWord ++ tailWord_874723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874756 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_874756 : Nat := 118140960795 + 874756 * 2 ^ 59
def prefixEnd_874756 : Nat := 4983230072969 + 3 ^ 40 * 874756 * 2
def baseEnd_874756 : Nat := 449170283404484746827077

theorem tailTrace_874756 : CollatzResearch.WordTrace tailWord_874756 prefixEnd_874756 449170283404484746827077 := by
  unfold tailWord_874756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952486209457941637926061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21269981612610588850568081 15952486209457941637926061)
  ·
    refine ⟨5982182328546728114222273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15952486209457941637926061 5982182328546728114222273)
    ·
      refine ⟨4486636746410046085666705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5982182328546728114222273 4486636746410046085666705)
      ·
        refine ⟨3364977559807534564250029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486636746410046085666705 3364977559807534564250029)
        ·
          refine ⟨1261866584927825461593761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3364977559807534564250029 1261866584927825461593761)
          ·
            refine ⟨946399938695869096195321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261866584927825461593761 946399938695869096195321)
            ·
              refine ⟨709799954021901822146491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946399938695869096195321 709799954021901822146491)
              ·
                refine ⟨1064699931032852733219737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709799954021901822146491 1064699931032852733219737)
                ·
                  refine ⟨798524948274639549914803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1064699931032852733219737 798524948274639549914803)
                  ·
                    refine ⟨1197787422411959324872205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 798524948274639549914803 1197787422411959324872205)
                    ·
                      refine ⟨449170283404484746827077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1197787422411959324872205 449170283404484746827077)
                      ·
                        rfl

theorem cell23_874756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_874756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874756 prefixEnd_874756 := by exact prefixLift 874756
  have htrace : WordTrace (prefixWord ++ tailWord_874756) baseStart_874756 baseEnd_874756 := by
    simpa [prefixWord, tailWord_874756, baseEnd_874756] using wordTrace_append hprefix tailTrace_874756
  have hstable : (prefixWord ++ tailWord_874756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874756).length < 2 ^ (prefixWord ++ tailWord_874756).sum := by decide
  have hdescent : baseEnd_874756 < baseStart_874756 := by decide
  rcases family_descends (prefixWord ++ tailWord_874756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874771 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8]
def baseStart_874771 : Nat := 118140960795 + 874771 * 2 ^ 59
def prefixEnd_874771 : Nat := 4983230072969 + 3 ^ 40 * 874771 * 2
def baseEnd_874771 : Nat := 449177985614302188139507

theorem tailTrace_874771 : CollatzResearch.WordTrace tailWord_874771 prefixEnd_874771 449177985614302188139507 := by
  unfold tailWord_874771
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905519513861540837648167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21270346342574360558432111 31905519513861540837648167)
  ·
    refine ⟨47858279270792311256472251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31905519513861540837648167 47858279270792311256472251)
    ·
      refine ⟨71787418906188466884708377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47858279270792311256472251 71787418906188466884708377)
      ·
        refine ⟨53840564179641350163531283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71787418906188466884708377 53840564179641350163531283)
        ·
          refine ⟨80760846269462025245296925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53840564179641350163531283 80760846269462025245296925)
          ·
            refine ⟨30285317351048259466986347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80760846269462025245296925 30285317351048259466986347)
            ·
              refine ⟨45427976026572389200479521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30285317351048259466986347 45427976026572389200479521)
              ·
                refine ⟨34070982019929291900359641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45427976026572389200479521 34070982019929291900359641)
                ·
                  refine ⟨25553236514946968925269731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34070982019929291900359641 25553236514946968925269731)
                  ·
                    refine ⟨38329854772420453387904597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25553236514946968925269731 38329854772420453387904597)
                    ·
                      refine ⟨449177985614302188139507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 38329854772420453387904597 449177985614302188139507)
                      ·
                        rfl

theorem cell23_874771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_874771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874771 prefixEnd_874771 := by exact prefixLift 874771
  have htrace : WordTrace (prefixWord ++ tailWord_874771) baseStart_874771 baseEnd_874771 := by
    simpa [prefixWord, tailWord_874771, baseEnd_874771] using wordTrace_append hprefix tailTrace_874771
  have hstable : (prefixWord ++ tailWord_874771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874771).length < 2 ^ (prefixWord ++ tailWord_874771).sum := by decide
  have hdescent : baseEnd_874771 < baseStart_874771 := by decide
  rcases family_descends (prefixWord ++ tailWord_874771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874782 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_874782 : Nat := 118140960795 + 874782 * 2 ^ 59
def prefixEnd_874782 : Nat := 4983230072969 + 3 ^ 40 * 874782 * 2
def baseEnd_874782 : Nat := 449183633901501645101957

theorem tailTrace_874782 : CollatzResearch.WordTrace tailWord_874782 prefixEnd_874782 449183633901501645101957 := by
  unfold tailWord_874782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988240089602711214537325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21270613811214459810865733 3988240089602711214537325)
  ·
    refine ⟨1495590033601016705451497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3988240089602711214537325 1495590033601016705451497)
    ·
      refine ⟨1121692525200762529088623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1495590033601016705451497 1121692525200762529088623)
      ·
        refine ⟨1682538787801143793632935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121692525200762529088623 1682538787801143793632935)
        ·
          refine ⟨2523808181701715690449403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682538787801143793632935 2523808181701715690449403)
          ·
            refine ⟨3785712272552573535674105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523808181701715690449403 3785712272552573535674105)
            ·
              refine ⟨2839284204414430151755579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785712272552573535674105 2839284204414430151755579)
              ·
                refine ⟨4258926306621645227633369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839284204414430151755579 4258926306621645227633369)
                ·
                  refine ⟨3194194729966233920725027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258926306621645227633369 3194194729966233920725027)
                  ·
                    refine ⟨4791292094949350881087541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3194194729966233920725027 4791292094949350881087541)
                    ·
                      refine ⟨449183633901501645101957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4791292094949350881087541 449183633901501645101957)
                      ·
                        rfl

theorem cell23_874782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_874782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874782 prefixEnd_874782 := by exact prefixLift 874782
  have htrace : WordTrace (prefixWord ++ tailWord_874782) baseStart_874782 baseEnd_874782 := by
    simpa [prefixWord, tailWord_874782, baseEnd_874782] using wordTrace_append hprefix tailTrace_874782
  have hstable : (prefixWord ++ tailWord_874782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874782).length < 2 ^ (prefixWord ++ tailWord_874782).sum := by decide
  have hdescent : baseEnd_874782 < baseStart_874782 := by decide
  rcases family_descends (prefixWord ++ tailWord_874782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874802 : List Nat := [3, 2, 1, 1, 5, 1, 1, 4, 5]
def baseStart_874802 : Nat := 118140960795 + 874802 * 2 ^ 59
def prefixEnd_874802 : Nat := 4983230072969 + 3 ^ 40 * 874802 * 2
def baseEnd_874802 : Nat := 49910433723843507427985

theorem tailTrace_874802 : CollatzResearch.WordTrace tailWord_874802 prefixEnd_874802 49910433723843507427985 := by
  unfold tailWord_874802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976662544187308283006665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21271100117832822088017773 7976662544187308283006665)
  ·
    refine ⟨5982496908140481212254999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7976662544187308283006665 5982496908140481212254999)
    ·
      refine ⟨8973745362210721818382499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5982496908140481212254999 8973745362210721818382499)
      ·
        refine ⟨13460618043316082727573749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8973745362210721818382499 13460618043316082727573749)
        ·
          refine ⟨1261932941560882755710039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13460618043316082727573749 1261932941560882755710039)
          ·
            refine ⟨1892899412341324133565059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261932941560882755710039 1892899412341324133565059)
            ·
              refine ⟨2839349118511986200347589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892899412341324133565059 2839349118511986200347589)
              ·
                refine ⟨532377959720997412565173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2839349118511986200347589 532377959720997412565173)
                ·
                  refine ⟨49910433723843507427985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532377959720997412565173 49910433723843507427985)
                  ·
                    rfl

theorem cell23_874802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_874802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874802 prefixEnd_874802 := by exact prefixLift 874802
  have htrace : WordTrace (prefixWord ++ tailWord_874802) baseStart_874802 baseEnd_874802 := by
    simpa [prefixWord, tailWord_874802, baseEnd_874802] using wordTrace_append hprefix tailTrace_874802
  have hstable : (prefixWord ++ tailWord_874802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874802).length < 2 ^ (prefixWord ++ tailWord_874802).sum := by decide
  have hdescent : baseEnd_874802 < baseStart_874802 := by decide
  rcases family_descends (prefixWord ++ tailWord_874802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874805 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_874805 : Nat := 118140960795 + 874805 * 2 ^ 59
def prefixEnd_874805 : Nat := 4983230072969 + 3 ^ 40 * 874805 * 2
def baseEnd_874805 : Nat := 449195443956555055114351

theorem tailTrace_874805 : CollatzResearch.WordTrace tailWord_874805 prefixEnd_874805 449195443956555055114351 := by
  unfold tailWord_874805
  simp only [CollatzResearch.WordTrace]
  refine ⟨31906759595738364644385869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21271173063825576429590579 31906759595738364644385869)
  ·
    refine ⟨11965034848401886741644701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31906759595738364644385869 11965034848401886741644701)
    ·
      refine ⟨4486888068150707528116763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11965034848401886741644701 4486888068150707528116763)
      ·
        refine ⟨6730332102226061292175145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486888068150707528116763 6730332102226061292175145)
        ·
          refine ⟨5047749076669545969131359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6730332102226061292175145 5047749076669545969131359)
          ·
            refine ⟨7571623615004318953697039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047749076669545969131359 7571623615004318953697039)
            ·
              refine ⟨11357435422506478430545559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571623615004318953697039 11357435422506478430545559)
              ·
                refine ⟨17036153133759717645818339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11357435422506478430545559 17036153133759717645818339)
                ·
                  refine ⟨25554229700639576468727509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17036153133759717645818339 25554229700639576468727509)
                  ·
                    refine ⟨598927258608740073485801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25554229700639576468727509 598927258608740073485801)
                    ·
                      refine ⟨449195443956555055114351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 598927258608740073485801 449195443956555055114351)
                      ·
                        rfl

theorem cell23_874805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_874805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874805 prefixEnd_874805 := by exact prefixLift 874805
  have htrace : WordTrace (prefixWord ++ tailWord_874805) baseStart_874805 baseEnd_874805 := by
    simpa [prefixWord, tailWord_874805, baseEnd_874805] using wordTrace_append hprefix tailTrace_874805
  have hstable : (prefixWord ++ tailWord_874805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874805).length < 2 ^ (prefixWord ++ tailWord_874805).sum := by decide
  have hdescent : baseEnd_874805 < baseStart_874805 := by decide
  rcases family_descends (prefixWord ++ tailWord_874805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874808 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_874808 : Nat := 118140960795 + 874808 * 2 ^ 59
def prefixEnd_874808 : Nat := 4983230072969 + 3 ^ 40 * 874808 * 2
def baseEnd_874808 : Nat := 449196984398518543376837

theorem tailTrace_874808 : CollatzResearch.WordTrace tailWord_874808 prefixEnd_874808 449196984398518543376837 := by
  unfold tailWord_874808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15953434507363748078372539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21271246009818330771163385 15953434507363748078372539)
  ·
    refine ⟨23930151761045622117558809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15953434507363748078372539 23930151761045622117558809)
    ·
      refine ⟨17947613820784216588169107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23930151761045622117558809 17947613820784216588169107)
      ·
        refine ⟨26921420731176324882253661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17947613820784216588169107 26921420731176324882253661)
        ·
          refine ⟨10095532774191121830845123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26921420731176324882253661 10095532774191121830845123)
          ·
            refine ⟨15143299161286682746267685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10095532774191121830845123 15143299161286682746267685)
            ·
              refine ⟨2839368592741253014925191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15143299161286682746267685 2839368592741253014925191)
              ·
                refine ⟨4259052889111879522387787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839368592741253014925191 4259052889111879522387787)
                ·
                  refine ⟨6388579333667819283581681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259052889111879522387787 6388579333667819283581681)
                  ·
                    refine ⟨4791434500250864462686261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388579333667819283581681 4791434500250864462686261)
                    ·
                      refine ⟨449196984398518543376837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4791434500250864462686261 449196984398518543376837)
                      ·
                        rfl

theorem cell23_874808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_874808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874808 prefixEnd_874808 := by exact prefixLift 874808
  have htrace : WordTrace (prefixWord ++ tailWord_874808) baseStart_874808 baseEnd_874808 := by
    simpa [prefixWord, tailWord_874808, baseEnd_874808] using wordTrace_append hprefix tailTrace_874808
  have hstable : (prefixWord ++ tailWord_874808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874808).length < 2 ^ (prefixWord ++ tailWord_874808).sum := by decide
  have hdescent : baseEnd_874808 < baseStart_874808 := by decide
  rcases family_descends (prefixWord ++ tailWord_874808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874905 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 1, 5]
def baseStart_874905 : Nat := 118140960795 + 874905 * 2 ^ 59
def prefixEnd_874905 : Nat := 4983230072969 + 3 ^ 40 * 874905 * 2
def baseEnd_874905 : Nat := 149748930674001554621297

theorem tailTrace_874905 : CollatzResearch.WordTrace tailWord_874905 prefixEnd_874905 149748930674001554621297 := by
  unfold tailWord_874905
  simp only [CollatzResearch.WordTrace]
  refine ⟨31910406895376081723026169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21273604596917387815350779 31910406895376081723026169)
  ·
    refine ⟨23932805171532061292269627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31910406895376081723026169 23932805171532061292269627)
    ·
      refine ⟨35899207757298091938404441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23932805171532061292269627 35899207757298091938404441)
      ·
        refine ⟨26924405817973568953803331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35899207757298091938404441 26924405817973568953803331)
        ·
          refine ⟨40386608726960353430704997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26924405817973568953803331 40386608726960353430704997)
          ·
            refine ⟨7572489136305066268257187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40386608726960353430704997 7572489136305066268257187)
            ·
              refine ⟨11358733704457599402385781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572489136305066268257187 11358733704457599402385781)
              ·
                refine ⟨1064881284792899943973667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11358733704457599402385781 1064881284792899943973667)
                ·
                  refine ⟨1597321927189349915960501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064881284792899943973667 1597321927189349915960501)
                  ·
                    refine ⟨149748930674001554621297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1597321927189349915960501 149748930674001554621297)
                    ·
                      rfl

theorem cell23_874905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_874905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874905 prefixEnd_874905 := by exact prefixLift 874905
  have htrace : WordTrace (prefixWord ++ tailWord_874905) baseStart_874905 baseEnd_874905 := by
    simpa [prefixWord, tailWord_874905, baseEnd_874905] using wordTrace_append hprefix tailTrace_874905
  have hstable : (prefixWord ++ tailWord_874905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874905).length < 2 ^ (prefixWord ++ tailWord_874905).sum := by decide
  have hdescent : baseEnd_874905 < baseStart_874905 := by decide
  rcases family_descends (prefixWord ++ tailWord_874905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874912 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 4, 3, 2]
def baseStart_874912 : Nat := 118140960795 + 874912 * 2 ^ 59
def prefixEnd_874912 : Nat := 4983230072969 + 3 ^ 40 * 874912 * 2
def baseEnd_874912 : Nat := 449250386386586136476359

theorem tailTrace_874912 : CollatzResearch.WordTrace tailWord_874912 prefixEnd_874912 449250386386586136476359 := by
  unfold tailWord_874912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955331103175360959265495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21273774804233814612353993 15955331103175360959265495)
  ·
    refine ⟨23932996654763041438898243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15955331103175360959265495 23932996654763041438898243)
    ·
      refine ⟨35899494982144562158347365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23932996654763041438898243 35899494982144562158347365)
      ·
        refine ⟨6731155309152105404690131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35899494982144562158347365 6731155309152105404690131)
        ·
          refine ⟨10096732963728158107035197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6731155309152105404690131 10096732963728158107035197)
          ·
            refine ⟨3786274861398059290138199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10096732963728158107035197 3786274861398059290138199)
            ·
              refine ⟨5679412292097088935207299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786274861398059290138199 5679412292097088935207299)
              ·
                refine ⟨8519118438145633402810949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679412292097088935207299 8519118438145633402810949)
                ·
                  refine ⟨1597334707152306263027053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8519118438145633402810949 1597334707152306263027053)
                  ·
                    refine ⟨599000515182114848635145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597334707152306263027053 599000515182114848635145)
                    ·
                      refine ⟨449250386386586136476359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599000515182114848635145 449250386386586136476359)
                      ·
                        rfl

theorem cell23_874912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_874912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874912 prefixEnd_874912 := by exact prefixLift 874912
  have htrace : WordTrace (prefixWord ++ tailWord_874912) baseStart_874912 baseEnd_874912 := by
    simpa [prefixWord, tailWord_874912, baseEnd_874912] using wordTrace_append hprefix tailTrace_874912
  have hstable : (prefixWord ++ tailWord_874912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874912).length < 2 ^ (prefixWord ++ tailWord_874912).sum := by decide
  have hdescent : baseEnd_874912 < baseStart_874912 := by decide
  rcases family_descends (prefixWord ++ tailWord_874912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874913 : List Nat := [1, 2, 3, 5, 1, 1, 3, 2, 1, 4]
def baseStart_874913 : Nat := 118140960795 + 874913 * 2 ^ 59
def prefixEnd_874913 : Nat := 4983230072969 + 3 ^ 40 * 874913 * 2
def baseEnd_874913 : Nat := 149750299955746877521285

theorem tailTrace_874913 : CollatzResearch.WordTrace tailWord_874913 prefixEnd_874913 149750299955746877521285 := by
  unfold tailWord_874913
  simp only [CollatzResearch.WordTrace]
  refine ⟨31910698679347099089317393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21273799119564732726211595 31910698679347099089317393)
  ·
    refine ⟨23933024009510324316988045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31910698679347099089317393 23933024009510324316988045)
    ·
      refine ⟨8974884003566371618870517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23933024009510324316988045 8974884003566371618870517)
      ·
        refine ⟨841395375334347339269111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8974884003566371618870517 841395375334347339269111)
        ·
          refine ⟨1262093063001521008903667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841395375334347339269111 1262093063001521008903667)
          ·
            refine ⟨1893139594502281513355501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262093063001521008903667 1893139594502281513355501)
            ·
              refine ⟨709927347938355567508313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1893139594502281513355501 709927347938355567508313)
              ·
                refine ⟨532445510953766675631235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709927347938355567508313 532445510953766675631235)
                ·
                  refine ⟨798668266430650013446853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532445510953766675631235 798668266430650013446853)
                  ·
                    refine ⟨149750299955746877521285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 798668266430650013446853 149750299955746877521285)
                    ·
                      rfl

theorem cell23_874913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_874913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874913 prefixEnd_874913 := by exact prefixLift 874913
  have htrace : WordTrace (prefixWord ++ tailWord_874913) baseStart_874913 baseEnd_874913 := by
    simpa [prefixWord, tailWord_874913, baseEnd_874913] using wordTrace_append hprefix tailTrace_874913
  have hstable : (prefixWord ++ tailWord_874913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874913).length < 2 ^ (prefixWord ++ tailWord_874913).sum := by decide
  have hdescent : baseEnd_874913 < baseStart_874913 := by decide
  rcases family_descends (prefixWord ++ tailWord_874913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874919 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_874919 : Nat := 118140960795 + 874919 * 2 ^ 59
def prefixEnd_874919 : Nat := 4983230072969 + 3 ^ 40 * 874919 * 2
def baseEnd_874919 : Nat := 449253980751167609088827

theorem tailTrace_874919 : CollatzResearch.WordTrace tailWord_874919 prefixEnd_874919 449253980751167609088827 := by
  unfold tailWord_874919
  simp only [CollatzResearch.WordTrace]
  refine ⟨31910917517325362114035811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21273945011550241409357207 31910917517325362114035811)
  ·
    refine ⟨47866376275988043171053717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31910917517325362114035811 47866376275988043171053717)
    ·
      refine ⟨2243736387936939523643143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47866376275988043171053717 2243736387936939523643143)
      ·
        refine ⟨3365604581905409285464715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243736387936939523643143 3365604581905409285464715)
        ·
          refine ⟨5048406872858113928197073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365604581905409285464715 5048406872858113928197073)
          ·
            refine ⟨3786305154643585446147805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5048406872858113928197073 3786305154643585446147805)
            ·
              refine ⟨1419864432991344542305427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3786305154643585446147805 1419864432991344542305427)
              ·
                refine ⟨2129796649487016813458141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419864432991344542305427 2129796649487016813458141)
                ·
                  refine ⟨798673743557631305046803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2129796649487016813458141 798673743557631305046803)
                  ·
                    refine ⟨1198010615336446957570205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 798673743557631305046803 1198010615336446957570205)
                    ·
                      refine ⟨449253980751167609088827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198010615336446957570205 449253980751167609088827)
                      ·
                        rfl

theorem cell23_874919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_874919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874919 prefixEnd_874919 := by exact prefixLift 874919
  have htrace : WordTrace (prefixWord ++ tailWord_874919) baseStart_874919 baseEnd_874919 := by
    simpa [prefixWord, tailWord_874919, baseEnd_874919] using wordTrace_append hprefix tailTrace_874919
  have hstable : (prefixWord ++ tailWord_874919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874919).length < 2 ^ (prefixWord ++ tailWord_874919).sum := by decide
  have hdescent : baseEnd_874919 < baseStart_874919 := by decide
  rcases family_descends (prefixWord ++ tailWord_874919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874928 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_874928 : Nat := 118140960795 + 874928 * 2 ^ 59
def prefixEnd_874928 : Nat := 4983230072969 + 3 ^ 40 * 874928 * 2
def baseEnd_874928 : Nat := 449258602077058073876285

theorem tailTrace_874928 : CollatzResearch.WordTrace tailWord_874928 prefixEnd_874928 449258602077058073876285 := by
  unfold tailWord_874928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955622887146378325556719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21274163849528504434075625 15955622887146378325556719)
  ·
    refine ⟨23933434330719567488335079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15955622887146378325556719 23933434330719567488335079)
    ·
      refine ⟨35900151496079351232502619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23933434330719567488335079 35900151496079351232502619)
      ·
        refine ⟨53850227244119026848753929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35900151496079351232502619 53850227244119026848753929)
        ·
          refine ⟨40387670433089270136565447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53850227244119026848753929 40387670433089270136565447)
          ·
            refine ⟨60581505649633905204848171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40387670433089270136565447 60581505649633905204848171)
            ·
              refine ⟨90872258474450857807272257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60581505649633905204848171 90872258474450857807272257)
              ·
                refine ⟨68154193855838143355454193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90872258474450857807272257 68154193855838143355454193)
                ·
                  refine ⟨51115645391878607516590645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68154193855838143355454193 51115645391878607516590645)
                  ·
                    refine ⟨4792091755488619454680373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51115645391878607516590645 4792091755488619454680373)
                    ·
                      refine ⟨449258602077058073876285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4792091755488619454680373 449258602077058073876285)
                      ·
                        rfl

theorem cell23_874928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_874928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874928 prefixEnd_874928 := by exact prefixLift 874928
  have htrace : WordTrace (prefixWord ++ tailWord_874928) baseStart_874928 baseEnd_874928 := by
    simpa [prefixWord, tailWord_874928, baseEnd_874928] using wordTrace_append hprefix tailTrace_874928
  have hstable : (prefixWord ++ tailWord_874928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874928).length < 2 ^ (prefixWord ++ tailWord_874928).sum := by decide
  have hdescent : baseEnd_874928 < baseStart_874928 := by decide
  rcases family_descends (prefixWord ++ tailWord_874928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874942 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_874942 : Nat := 118140960795 + 874942 * 2 ^ 59
def prefixEnd_874942 : Nat := 4983230072969 + 3 ^ 40 * 874942 * 2
def baseEnd_874942 : Nat := 449265790806221019101221

theorem tailTrace_874942 : CollatzResearch.WordTrace tailWord_874942 prefixEnd_874942 449265790806221019101221 := by
  unfold tailWord_874942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988969549530254630265385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21274504264161358028082053 3988969549530254630265385)
  ·
    refine ⟨2991727162147690972699039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3988969549530254630265385 2991727162147690972699039)
    ·
      refine ⟨4487590743221536459048559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991727162147690972699039 4487590743221536459048559)
      ·
        refine ⟨6731386114832304688572839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4487590743221536459048559 6731386114832304688572839)
        ·
          refine ⟨10097079172248457032859259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6731386114832304688572839 10097079172248457032859259)
          ·
            refine ⟨15145618758372685549288889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10097079172248457032859259 15145618758372685549288889)
            ·
              refine ⟨11359214068779514161966667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15145618758372685549288889 11359214068779514161966667)
              ·
                refine ⟨17038821103169271242950001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11359214068779514161966667 17038821103169271242950001)
                ·
                  refine ⟨12779115827376953432212501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17038821103169271242950001 12779115827376953432212501)
                  ·
                    refine ⟨599021054408294692134961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12779115827376953432212501 599021054408294692134961)
                    ·
                      refine ⟨449265790806221019101221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599021054408294692134961 449265790806221019101221)
                      ·
                        rfl

theorem cell23_874942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_874942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874942 prefixEnd_874942 := by exact prefixLift 874942
  have htrace : WordTrace (prefixWord ++ tailWord_874942) baseStart_874942 baseEnd_874942 := by
    simpa [prefixWord, tailWord_874942, baseEnd_874942] using wordTrace_append hprefix tailTrace_874942
  have hstable : (prefixWord ++ tailWord_874942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874942).length < 2 ^ (prefixWord ++ tailWord_874942).sum := by decide
  have hdescent : baseEnd_874942 < baseStart_874942 := by decide
  rcases family_descends (prefixWord ++ tailWord_874942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874976 : List Nat := [2, 1, 1, 3, 1, 1, 5, 4, 1, 2, 2]
def baseStart_874976 : Nat := 118140960795 + 874976 * 2 ^ 59
def prefixEnd_874976 : Nat := 4983230072969 + 3 ^ 40 * 874976 * 2
def baseEnd_874976 : Nat := 449283249148473886076065

theorem tailTrace_874976 : CollatzResearch.WordTrace tailWord_874976 prefixEnd_874976 449283249148473886076065 := by
  unfold tailWord_874976
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956498239059430424430391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21275330985412573899240521 15956498239059430424430391)
  ·
    refine ⟨23934747358589145636645587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956498239059430424430391 23934747358589145636645587)
    ·
      refine ⟨35902121037883718454968381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23934747358589145636645587 35902121037883718454968381)
      ·
        refine ⟨13463295389206394420613143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35902121037883718454968381 13463295389206394420613143)
        ·
          refine ⟨20194943083809591630919715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13463295389206394420613143 20194943083809591630919715)
          ·
            refine ⟨30292414625714387446379573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20194943083809591630919715 30292414625714387446379573)
            ·
              refine ⟨2839913871160723823098085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30292414625714387446379573 2839913871160723823098085)
              ·
                refine ⟨532483850842635716830891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2839913871160723823098085 532483850842635716830891)
                ·
                  refine ⟨798725776263953575246337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532483850842635716830891 798725776263953575246337)
                  ·
                    refine ⟨599044332197965181434753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 798725776263953575246337 599044332197965181434753)
                    ·
                      refine ⟨449283249148473886076065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599044332197965181434753 449283249148473886076065)
                      ·
                        rfl

theorem cell23_874976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_874976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874976 prefixEnd_874976 := by exact prefixLift 874976
  have htrace : WordTrace (prefixWord ++ tailWord_874976) baseStart_874976 baseEnd_874976 := by
    simpa [prefixWord, tailWord_874976, baseEnd_874976] using wordTrace_append hprefix tailTrace_874976
  have hstable : (prefixWord ++ tailWord_874976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874976).length < 2 ^ (prefixWord ++ tailWord_874976).sum := by decide
  have hdescent : baseEnd_874976 < baseStart_874976 := by decide
  rcases family_descends (prefixWord ++ tailWord_874976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874989 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_874989 : Nat := 118140960795 + 874989 * 2 ^ 59
def prefixEnd_874989 : Nat := 4983230072969 + 3 ^ 40 * 874989 * 2
def baseEnd_874989 : Nat := 449289924396982335213505

theorem tailTrace_874989 : CollatzResearch.WordTrace tailWord_874989 prefixEnd_874989 449289924396982335213505 := by
  unfold tailWord_874989
  simp only [CollatzResearch.WordTrace]
  refine ⟨31913470627071764069084021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21275647084714509379389347 31913470627071764069084021)
  ·
    refine ⟨2991887871287977881476627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31913470627071764069084021 2991887871287977881476627)
    ·
      refine ⟨4487831806931966822214941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991887871287977881476627 4487831806931966822214941)
      ·
        refine ⟨1682936927599487558330603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4487831806931966822214941 1682936927599487558330603)
        ·
          refine ⟨2524405391399231337495905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682936927599487558330603 2524405391399231337495905)
          ·
            refine ⟨1893304043549423503121929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2524405391399231337495905 1893304043549423503121929)
            ·
              refine ⟨1419978032662067627341447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893304043549423503121929 1419978032662067627341447)
              ·
                refine ⟨2129967048993101441012171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419978032662067627341447 2129967048993101441012171)
                ·
                  refine ⟨3194950573489652161518257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129967048993101441012171 3194950573489652161518257)
                  ·
                    refine ⟨2396212930117239121138693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3194950573489652161518257 2396212930117239121138693)
                    ·
                      refine ⟨449289924396982335213505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2396212930117239121138693 449289924396982335213505)
                      ·
                        rfl

theorem cell23_874989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_874989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874989 prefixEnd_874989 := by exact prefixLift 874989
  have htrace : WordTrace (prefixWord ++ tailWord_874989) baseStart_874989 baseEnd_874989 := by
    simpa [prefixWord, tailWord_874989, baseEnd_874989] using wordTrace_append hprefix tailTrace_874989
  have hstable : (prefixWord ++ tailWord_874989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874989).length < 2 ^ (prefixWord ++ tailWord_874989).sum := by decide
  have hdescent : baseEnd_874989 < baseStart_874989 := by decide
  rcases family_descends (prefixWord ++ tailWord_874989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
