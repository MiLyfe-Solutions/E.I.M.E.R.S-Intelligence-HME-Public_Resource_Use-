import V185TrunkScan23Chunk0790

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4678088 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_4678088 : Nat := 118140960795 + 4678088 * 2 ^ 59
def prefixEnd_4678088 : Nat := 4983230072969 + 3 ^ 40 * 4678088 * 2
def baseEnd_4678088 : Nat := 2402107688030398192885871

theorem tailTrace_4678088 : CollatzResearch.WordTrace tailWord_4678088 prefixEnd_4678088 2402107688030398192885871 := by
  unfold tailWord_4678088
  simp only [CollatzResearch.WordTrace]
  refine ⟨85311943338046802333773459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113749257784062403111697945 85311943338046802333773459)
  ·
    refine ⟨127967915007070203500660189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85311943338046802333773459 127967915007070203500660189)
    ·
      refine ⟨47987968127651326312747571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127967915007070203500660189 47987968127651326312747571)
      ·
        refine ⟨71981952191476989469121357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47987968127651326312747571 71981952191476989469121357)
        ·
          refine ⟨26993232071803871050920509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71981952191476989469121357 26993232071803871050920509)
          ·
            refine ⟨10122462026926451644095191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26993232071803871050920509 10122462026926451644095191)
            ·
              refine ⟨15183693040389677466142787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10122462026926451644095191 15183693040389677466142787)
              ·
                refine ⟨22775539560584516199214181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15183693040389677466142787 22775539560584516199214181)
                ·
                  refine ⟨4270413667609596787352659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22775539560584516199214181 4270413667609596787352659)
                  ·
                    refine ⟨6405620501414395181028989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270413667609596787352659 6405620501414395181028989)
                    ·
                      refine ⟨2402107688030398192885871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6405620501414395181028989 2402107688030398192885871)
                      ·
                        rfl

theorem cell23_4678088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_4678088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678088 prefixEnd_4678088 := by exact prefixLift 4678088
  have htrace : WordTrace (prefixWord ++ tailWord_4678088) baseStart_4678088 baseEnd_4678088 := by
    simpa [prefixWord, tailWord_4678088, baseEnd_4678088] using wordTrace_append hprefix tailTrace_4678088
  have hstable : (prefixWord ++ tailWord_4678088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678088).length < 2 ^ (prefixWord ++ tailWord_4678088).sum := by decide
  have hdescent : baseEnd_4678088 < baseStart_4678088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678105 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 2, 1, 3]
def baseStart_4678105 : Nat := 118140960795 + 4678105 * 2 ^ 59
def prefixEnd_4678105 : Nat := 4983230072969 + 3 ^ 40 * 4678105 * 2
def baseEnd_4678105 : Nat := 2402116417201524626373293

theorem tailTrace_4678105 : CollatzResearch.WordTrace tailWord_4678105 prefixEnd_4678105 2402116417201524626373293 := by
  unfold tailWord_4678105
  simp only [CollatzResearch.WordTrace]
  refine ⟨170624506717032016570915769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113749671144688011047277179 170624506717032016570915769)
  ·
    refine ⟨127968380037774012428186827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170624506717032016570915769 127968380037774012428186827)
    ·
      refine ⟨191952570056661018642280241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127968380037774012428186827 191952570056661018642280241)
      ·
        refine ⟨143964427542495763981710181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191952570056661018642280241 143964427542495763981710181)
        ·
          refine ⟨26993330164217955746570659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143964427542495763981710181 26993330164217955746570659)
          ·
            refine ⟨40489995246326933619855989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26993330164217955746570659 40489995246326933619855989)
            ·
              refine ⟨3795937054343150026861499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40489995246326933619855989 3795937054343150026861499)
              ·
                refine ⟨5693905581514725040292249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795937054343150026861499 5693905581514725040292249)
                ·
                  refine ⟨4270429186136043780219187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5693905581514725040292249 4270429186136043780219187)
                  ·
                    refine ⟨6405643779204065670328781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270429186136043780219187 6405643779204065670328781)
                    ·
                      refine ⟨2402116417201524626373293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6405643779204065670328781 2402116417201524626373293)
                      ·
                        rfl

theorem cell23_4678105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_4678105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678105 prefixEnd_4678105 := by exact prefixLift 4678105
  have htrace : WordTrace (prefixWord ++ tailWord_4678105) baseStart_4678105 baseEnd_4678105 := by
    simpa [prefixWord, tailWord_4678105, baseEnd_4678105] using wordTrace_append hprefix tailTrace_4678105
  have hstable : (prefixWord ++ tailWord_4678105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678105).length < 2 ^ (prefixWord ++ tailWord_4678105).sum := by decide
  have hdescent : baseEnd_4678105 < baseStart_4678105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678128 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 6, 2, 2]
def baseStart_4678128 : Nat := 118140960795 + 4678128 * 2 ^ 59
def prefixEnd_4678128 : Nat := 4983230072969 + 3 ^ 40 * 4678128 * 2
def baseEnd_4678128 : Nat := 2402128227256578036385687

theorem tailTrace_4678128 : CollatzResearch.WordTrace tailWord_4678128 prefixEnd_4678128 2402128227256578036385687 := by
  unfold tailWord_4678128
  simp only [CollatzResearch.WordTrace]
  refine ⟨85312672797974345749501519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113750230397299127666002025 85312672797974345749501519)
  ·
    refine ⟨127969009196961518624252279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85312672797974345749501519 127969009196961518624252279)
    ·
      refine ⟨191953513795442277936378419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127969009196961518624252279 191953513795442277936378419)
      ·
        refine ⟨287930270693163416904567629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191953513795442277936378419 287930270693163416904567629)
        ·
          refine ⟨107973851509936281339212861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287930270693163416904567629 107973851509936281339212861)
          ·
            refine ⟨40490194316226105502204823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107973851509936281339212861 40490194316226105502204823)
            ·
              refine ⟨60735291474339158253307235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40490194316226105502204823 60735291474339158253307235)
              ·
                refine ⟨91102937211508737379960853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60735291474339158253307235 91102937211508737379960853)
                ·
                  refine ⟨4270450181789472064685665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91102937211508737379960853 4270450181789472064685665)
                  ·
                    refine ⟨3202837636342104048514249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270450181789472064685665 3202837636342104048514249)
                    ·
                      refine ⟨2402128227256578036385687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202837636342104048514249 2402128227256578036385687)
                      ·
                        rfl

theorem cell23_4678128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 2, 2].length) (baseStart_4678128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678128 prefixEnd_4678128 := by exact prefixLift 4678128
  have htrace : WordTrace (prefixWord ++ tailWord_4678128) baseStart_4678128 baseEnd_4678128 := by
    simpa [prefixWord, tailWord_4678128, baseEnd_4678128] using wordTrace_append hprefix tailTrace_4678128
  have hstable : (prefixWord ++ tailWord_4678128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678128).length < 2 ^ (prefixWord ++ tailWord_4678128).sum := by decide
  have hdescent : baseEnd_4678128 < baseStart_4678128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678145 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_4678145 : Nat := 118140960795 + 4678145 * 2 ^ 59
def prefixEnd_4678145 : Nat := 4983230072969 + 3 ^ 40 * 4678145 * 2
def baseEnd_4678145 : Nat := 2402136956427704469873109

theorem tailTrace_4678145 : CollatzResearch.WordTrace tailWord_4678145 prefixEnd_4678145 2402136956427704469873109 := by
  unfold tailWord_4678145
  simp only [CollatzResearch.WordTrace]
  refine ⟨170625965636887103402371889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113750643757924735601581259 170625965636887103402371889)
  ·
    refine ⟨127969474227665327551778917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170625965636887103402371889 127969474227665327551778917)
    ·
      refine ⟨23994276417687248915958547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127969474227665327551778917 23994276417687248915958547)
      ·
        refine ⟨35991414626530873373937821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23994276417687248915958547 35991414626530873373937821)
        ·
          refine ⟨13496780484949077515226683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35991414626530873373937821 13496780484949077515226683)
          ·
            refine ⟨20245170727423616272840025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13496780484949077515226683 20245170727423616272840025)
            ·
              refine ⟨15183878045567712204630019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20245170727423616272840025 15183878045567712204630019)
              ·
                refine ⟨22775817068351568306945029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15183878045567712204630019 22775817068351568306945029)
                ·
                  refine ⟨4270465700315919057552193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22775817068351568306945029 4270465700315919057552193)
                  ·
                    refine ⟨3202849275236939293164145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270465700315919057552193 3202849275236939293164145)
                    ·
                      refine ⟨2402136956427704469873109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202849275236939293164145 2402136956427704469873109)
                      ·
                        rfl

theorem cell23_4678145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_4678145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678145 prefixEnd_4678145 := by exact prefixLift 4678145
  have htrace : WordTrace (prefixWord ++ tailWord_4678145) baseStart_4678145 baseEnd_4678145 := by
    simpa [prefixWord, tailWord_4678145, baseEnd_4678145] using wordTrace_append hprefix tailTrace_4678145
  have hstable : (prefixWord ++ tailWord_4678145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678145).length < 2 ^ (prefixWord ++ tailWord_4678145).sum := by decide
  have hdescent : baseEnd_4678145 < baseStart_4678145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678181 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_4678181 : Nat := 118140960795 + 4678181 * 2 ^ 59
def prefixEnd_4678181 : Nat := 4983230072969 + 3 ^ 40 * 4678181 * 2
def baseEnd_4678181 : Nat := 800718480577088776340981

theorem tailTrace_4678181 : CollatzResearch.WordTrace tailWord_4678181 prefixEnd_4678181 800718480577088776340981 := by
  unfold tailWord_4678181
  simp only [CollatzResearch.WordTrace]
  refine ⟨170627278664756681550682397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113751519109837787700454931 170627278664756681550682397)
  ·
    refine ⟨63985229499283755581505899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170627278664756681550682397 63985229499283755581505899)
    ·
      refine ⟨95977844248925633372258849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63985229499283755581505899 95977844248925633372258849)
      ·
        refine ⟨71983383186694225029194137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95977844248925633372258849 71983383186694225029194137)
        ·
          refine ⟨53987537390020668771895603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71983383186694225029194137 53987537390020668771895603)
          ·
            refine ⟨80981306085031003157843405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53987537390020668771895603 80981306085031003157843405)
            ·
              refine ⟨30367989781886626184191277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80981306085031003157843405 30367989781886626184191277)
              ·
                refine ⟨11387996168207484819071729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30367989781886626184191277 11387996168207484819071729)
                ·
                  refine ⟨8540997126155613614303797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11387996168207484819071729 8540997126155613614303797)
                  ·
                    refine ⟨800718480577088776340981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8540997126155613614303797 800718480577088776340981)
                    ·
                      rfl

theorem cell23_4678181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_4678181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678181 prefixEnd_4678181 := by exact prefixLift 4678181
  have htrace : WordTrace (prefixWord ++ tailWord_4678181) baseStart_4678181 baseEnd_4678181 := by
    simpa [prefixWord, tailWord_4678181, baseEnd_4678181] using wordTrace_append hprefix tailTrace_4678181
  have hstable : (prefixWord ++ tailWord_4678181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678181).length < 2 ^ (prefixWord ++ tailWord_4678181).sum := by decide
  have hdescent : baseEnd_4678181 < baseStart_4678181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678196 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4678196 : Nat := 118140960795 + 4678196 * 2 ^ 59
def prefixEnd_4678196 : Nat := 4983230072969 + 3 ^ 40 * 4678196 * 2
def baseEnd_4678196 : Nat := 2402163143941083770335375

theorem tailTrace_4678196 : CollatzResearch.WordTrace tailWord_4678196 prefixEnd_4678196 2402163143941083770335375 := by
  unfold tailWord_4678196
  simp only [CollatzResearch.WordTrace]
  refine ⟨85313912879851169556239221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113751883839801559408318961 85313912879851169556239221)
  ·
    refine ⟨7998179332486047145897427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85313912879851169556239221 7998179332486047145897427)
    ·
      refine ⟨11997268998729070718846141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7998179332486047145897427 11997268998729070718846141)
      ·
        refine ⟨4498975874523401519567303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11997268998729070718846141 4498975874523401519567303)
        ·
          refine ⟨6748463811785102279350955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4498975874523401519567303 6748463811785102279350955)
          ·
            refine ⟨10122695717677653419026433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748463811785102279350955 10122695717677653419026433)
            ·
              refine ⟨7592021788258240064269825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10122695717677653419026433 7592021788258240064269825)
              ·
                refine ⟨5694016341193680048202369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7592021788258240064269825 5694016341193680048202369)
                ·
                  refine ⟨4270512255895260036151777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5694016341193680048202369 4270512255895260036151777)
                  ·
                    refine ⟨3202884191921445027113833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270512255895260036151777 3202884191921445027113833)
                    ·
                      refine ⟨2402163143941083770335375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202884191921445027113833 2402163143941083770335375)
                      ·
                        rfl

theorem cell23_4678196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4678196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678196 prefixEnd_4678196 := by exact prefixLift 4678196
  have htrace : WordTrace (prefixWord ++ tailWord_4678196) baseStart_4678196 baseEnd_4678196 := by
    simpa [prefixWord, tailWord_4678196, baseEnd_4678196] using wordTrace_append hprefix tailTrace_4678196
  have hstable : (prefixWord ++ tailWord_4678196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678196).length < 2 ^ (prefixWord ++ tailWord_4678196).sum := by decide
  have hdescent : baseEnd_4678196 < baseStart_4678196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678211 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 7, 4]
def baseStart_4678211 : Nat := 118140960795 + 4678211 * 2 ^ 59
def prefixEnd_4678211 : Nat := 4983230072969 + 3 ^ 40 * 4678211 * 2
def baseEnd_4678211 : Nat := 800723615383633737215935

theorem tailTrace_4678211 : CollatzResearch.WordTrace tailWord_4678211 prefixEnd_4678211 800723615383633737215935 := by
  unfold tailWord_4678211
  simp only [CollatzResearch.WordTrace]
  refine ⟨170628372854647996674274487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113752248569765331116182991 170628372854647996674274487)
  ·
    refine ⟨255942559281971995011411731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170628372854647996674274487 255942559281971995011411731)
    ·
      refine ⟨383913838922957992517117597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255942559281971995011411731 383913838922957992517117597)
      ·
        refine ⟨143967689596109247193919099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383913838922957992517117597 143967689596109247193919099)
        ·
          refine ⟨215951534394163870790878649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143967689596109247193919099 215951534394163870790878649)
          ·
            refine ⟨161963650795622903093158987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215951534394163870790878649 161963650795622903093158987)
            ·
              refine ⟨242945476193434354639738481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161963650795622903093158987 242945476193434354639738481)
              ·
                refine ⟨182209107145075765979803861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242945476193434354639738481 182209107145075765979803861)
                ·
                  refine ⟨4270525948712713265151653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182209107145075765979803861 4270525948712713265151653)
                  ·
                    refine ⟨800723615383633737215935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270525948712713265151653 800723615383633737215935)
                    ·
                      rfl

theorem cell23_4678211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 4].length) (baseStart_4678211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678211 prefixEnd_4678211 := by exact prefixLift 4678211
  have htrace : WordTrace (prefixWord ++ tailWord_4678211) baseStart_4678211 baseEnd_4678211 := by
    simpa [prefixWord, tailWord_4678211, baseEnd_4678211] using wordTrace_append hprefix tailTrace_4678211
  have hstable : (prefixWord ++ tailWord_4678211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678211).length < 2 ^ (prefixWord ++ tailWord_4678211).sum := by decide
  have hdescent : baseEnd_4678211 < baseStart_4678211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678218 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_4678218 : Nat := 118140960795 + 4678218 * 2 ^ 59
def prefixEnd_4678218 : Nat := 4983230072969 + 3 ^ 40 * 4678218 * 2
def baseEnd_4678218 : Nat := 2402174440515482684260273

theorem tailTrace_4678218 : CollatzResearch.WordTrace tailWord_4678218 prefixEnd_4678218 2402174440515482684260273 := by
  unfold tailWord_4678218
  simp only [CollatzResearch.WordTrace]
  refine ⟨42657157041405659217444827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113752418777081757913186205 42657157041405659217444827)
  ·
    refine ⟨63985735562108488826167241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42657157041405659217444827 63985735562108488826167241)
    ·
      refine ⟨47989301671581366619625431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63985735562108488826167241 47989301671581366619625431)
      ·
        refine ⟨71983952507372049929438147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47989301671581366619625431 71983952507372049929438147)
        ·
          refine ⟨107975928761058074894157221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71983952507372049929438147 107975928761058074894157221)
          ·
            refine ⟨20245486642698389042654479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107975928761058074894157221 20245486642698389042654479)
            ·
              refine ⟨30368229964047583563981719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20245486642698389042654479 30368229964047583563981719)
              ·
                refine ⟨45552344946071375345972579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30368229964047583563981719 45552344946071375345972579)
                ·
                  refine ⟨68328517419107063018958869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45552344946071375345972579 68328517419107063018958869)
                  ·
                    refine ⟨3202899254020643579013697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68328517419107063018958869 3202899254020643579013697)
                    ·
                      refine ⟨2402174440515482684260273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202899254020643579013697 2402174440515482684260273)
                      ·
                        rfl

theorem cell23_4678218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_4678218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678218 prefixEnd_4678218 := by exact prefixLift 4678218
  have htrace : WordTrace (prefixWord ++ tailWord_4678218) baseStart_4678218 baseEnd_4678218 := by
    simpa [prefixWord, tailWord_4678218, baseEnd_4678218] using wordTrace_append hprefix tailTrace_4678218
  have hstable : (prefixWord ++ tailWord_4678218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678218).length < 2 ^ (prefixWord ++ tailWord_4678218).sum := by decide
  have hdescent : baseEnd_4678218 < baseStart_4678218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678228 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_4678228 : Nat := 118140960795 + 4678228 * 2 ^ 59
def prefixEnd_4678228 : Nat := 4983230072969 + 3 ^ 40 * 4678228 * 2
def baseEnd_4678228 : Nat := 800726525107342548378409

theorem tailTrace_4678228 : CollatzResearch.WordTrace tailWord_4678228 prefixEnd_4678228 800726525107342548378409 := by
  unfold tailWord_4678228
  simp only [CollatzResearch.WordTrace]
  refine ⟨85314496447793204288821669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113752661930390939051762225 85314496447793204288821669)
  ·
    refine ⟨15996468083961225804154063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85314496447793204288821669 15996468083961225804154063)
    ·
      refine ⟨23994702125941838706231095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15996468083961225804154063 23994702125941838706231095)
      ·
        refine ⟨35992053188912758059346643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23994702125941838706231095 35992053188912758059346643)
        ·
          refine ⟨53988079783369137089019965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35992053188912758059346643 53988079783369137089019965)
          ·
            refine ⟨20245529918763426408382487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53988079783369137089019965 20245529918763426408382487)
            ·
              refine ⟨30368294878145139612573731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20245529918763426408382487 30368294878145139612573731)
              ·
                refine ⟨45552442317217709418860597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30368294878145139612573731 45552442317217709418860597)
                ·
                  refine ⟨4270541467239160258018181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45552442317217709418860597 4270541467239160258018181)
                  ·
                    refine ⟨800726525107342548378409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270541467239160258018181 800726525107342548378409)
                    ·
                      rfl

theorem cell23_4678228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_4678228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678228 prefixEnd_4678228 := by exact prefixLift 4678228
  have htrace : WordTrace (prefixWord ++ tailWord_4678228) baseStart_4678228 baseEnd_4678228 := by
    simpa [prefixWord, tailWord_4678228, baseEnd_4678228] using wordTrace_append hprefix tailTrace_4678228
  have hstable : (prefixWord ++ tailWord_4678228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678228).length < 2 ^ (prefixWord ++ tailWord_4678228).sum := by decide
  have hdescent : baseEnd_4678228 < baseStart_4678228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678258 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 8]
def baseStart_4678258 : Nat := 118140960795 + 4678258 * 2 ^ 59
def prefixEnd_4678258 : Nat := 4983230072969 + 3 ^ 40 * 4678258 * 2
def baseEnd_4678258 : Nat := 266910553304629169751121

theorem tailTrace_4678258 : CollatzResearch.WordTrace tailWord_4678258 prefixEnd_4678258 266910553304629169751121 := by
  unfold tailWord_4678258
  simp only [CollatzResearch.WordTrace]
  refine ⟨42657521771369430925308857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113753391390318482467490285 42657521771369430925308857)
  ·
    refine ⟨31993141328527073193981643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42657521771369430925308857 31993141328527073193981643)
    ·
      refine ⟨47989711992790609790972465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31993141328527073193981643 47989711992790609790972465)
      ·
        refine ⟨35992283994592957343229349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47989711992790609790972465 35992283994592957343229349)
        ·
          refine ⟨6748553248986179501855503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35992283994592957343229349 6748553248986179501855503)
          ·
            refine ⟨10122829873479269252783255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748553248986179501855503 10122829873479269252783255)
            ·
              refine ⟨15184244810218903879174883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10122829873479269252783255 15184244810218903879174883)
              ·
                refine ⟨22776367215328355818762325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15184244810218903879174883 22776367215328355818762325)
                ·
                  refine ⟨266910553304629169751121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22776367215328355818762325 266910553304629169751121)
                  ·
                    rfl

theorem cell23_4678258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_4678258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678258 prefixEnd_4678258 := by exact prefixLift 4678258
  have htrace : WordTrace (prefixWord ++ tailWord_4678258) baseStart_4678258 baseEnd_4678258 := by
    simpa [prefixWord, tailWord_4678258, baseEnd_4678258] using wordTrace_append hprefix tailTrace_4678258
  have hstable : (prefixWord ++ tailWord_4678258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678258).length < 2 ^ (prefixWord ++ tailWord_4678258).sum := by decide
  have hdescent : baseEnd_4678258 < baseStart_4678258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678262 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_4678262 : Nat := 118140960795 + 4678262 * 2 ^ 59
def prefixEnd_4678262 : Nat := 4983230072969 + 3 ^ 40 * 4678262 * 2
def baseEnd_4678262 : Nat := 800732344554760170703357

theorem tailTrace_4678262 : CollatzResearch.WordTrace tailWord_4678262 prefixEnd_4678262 800732344554760170703357 := by
  unfold tailWord_4678262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10664389561091452024023815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113753488651642154922920693 10664389561091452024023815)
  ·
    refine ⟨15996584341637178036035723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10664389561091452024023815 15996584341637178036035723)
    ·
      refine ⟨23994876512455767054053585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15996584341637178036035723 23994876512455767054053585)
      ·
        refine ⟨17996157384341825290540189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23994876512455767054053585 17996157384341825290540189)
        ·
          refine ⟨6748559019128184483952571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17996157384341825290540189 6748559019128184483952571)
          ·
            refine ⟨10122838528692276725928857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748559019128184483952571 10122838528692276725928857)
            ·
              refine ⟨7592128896519207544446643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10122838528692276725928857 7592128896519207544446643)
              ·
                refine ⟨11388193344778811316669965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7592128896519207544446643 11388193344778811316669965)
                ·
                  refine ⟨4270572504292054243751237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11388193344778811316669965 4270572504292054243751237)
                  ·
                    refine ⟨800732344554760170703357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270572504292054243751237 800732344554760170703357)
                    ·
                      rfl

theorem cell23_4678262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_4678262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678262 prefixEnd_4678262 := by exact prefixLift 4678262
  have htrace : WordTrace (prefixWord ++ tailWord_4678262) baseStart_4678262 baseEnd_4678262 := by
    simpa [prefixWord, tailWord_4678262, baseEnd_4678262] using wordTrace_append hprefix tailTrace_4678262
  have hstable : (prefixWord ++ tailWord_4678262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678262).length < 2 ^ (prefixWord ++ tailWord_4678262).sum := by decide
  have hdescent : baseEnd_4678262 < baseStart_4678262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678271 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 3, 5]
def baseStart_4678271 : Nat := 118140960795 + 4678271 * 2 ^ 59
def prefixEnd_4678271 : Nat := 4983230072969 + 3 ^ 40 * 4678271 * 2
def baseEnd_4678271 : Nat := 800733884996723658965843

theorem tailTrace_4678271 : CollatzResearch.WordTrace tailWord_4678271 prefixEnd_4678271 800733884996723658965843 := by
  unfold tailWord_4678271
  simp only [CollatzResearch.WordTrace]
  refine ⟨170630561234430626921458667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113753707489620417947639111 170630561234430626921458667)
  ·
    refine ⟨255945841851645940382188001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170630561234430626921458667 255945841851645940382188001)
    ·
      refine ⟨191959381388734455286641001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255945841851645940382188001 191959381388734455286641001)
      ·
        refine ⟨143969536041550841464980751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191959381388734455286641001 143969536041550841464980751)
        ·
          refine ⟨215954304062326262197471127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143969536041550841464980751 215954304062326262197471127)
          ·
            refine ⟨323931456093489393296206691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215954304062326262197471127 323931456093489393296206691)
            ·
              refine ⟨485897184140234089944310037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323931456093489393296206691 485897184140234089944310037)
              ·
                refine ⟨22776430506573472966139533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 485897184140234089944310037 22776430506573472966139533)
                ·
                  refine ⟨8541161439965052362302325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22776430506573472966139533 8541161439965052362302325)
                  ·
                    refine ⟨800733884996723658965843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8541161439965052362302325 800733884996723658965843)
                    ·
                      rfl

theorem cell23_4678271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_4678271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678271 prefixEnd_4678271 := by exact prefixLift 4678271
  have htrace : WordTrace (prefixWord ++ tailWord_4678271) baseStart_4678271 baseEnd_4678271 := by
    simpa [prefixWord, tailWord_4678271, baseEnd_4678271] using wordTrace_append hprefix tailTrace_4678271
  have hstable : (prefixWord ++ tailWord_4678271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678271).length < 2 ^ (prefixWord ++ tailWord_4678271).sum := by decide
  have hdescent : baseEnd_4678271 < baseStart_4678271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678295 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 2, 3, 2]
def baseStart_4678295 : Nat := 118140960795 + 4678295 * 2 ^ 59
def prefixEnd_4678295 : Nat := 4983230072969 + 3 ^ 40 * 4678295 * 2
def baseEnd_4678295 : Nat := 2402213978525878882997419

theorem tailTrace_4678295 : CollatzResearch.WordTrace tailWord_4678295 prefixEnd_4678295 2402213978525878882997419 := by
  unfold tailWord_4678295
  simp only [CollatzResearch.WordTrace]
  refine ⟨170631436586343679020332339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113754291057562452680221559 170631436586343679020332339)
  ·
    refine ⟨255947154879515518530498509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170631436586343679020332339 255947154879515518530498509)
    ·
      refine ⟨95980183079818319448936941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255947154879515518530498509 95980183079818319448936941)
      ·
        refine ⟨35992568654931869793351353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95980183079818319448936941 35992568654931869793351353)
        ·
          refine ⟨26994426491198902345013515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35992568654931869793351353 26994426491198902345013515)
          ·
            refine ⟨40491639736798353517520273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26994426491198902345013515 40491639736798353517520273)
            ·
              refine ⟨30368729802598765138140205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40491639736798353517520273 30368729802598765138140205)
              ·
                refine ⟨11388273675974536926802577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30368729802598765138140205 11388273675974536926802577)
                ·
                  refine ⟨8541205256980902695101933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11388273675974536926802577 8541205256980902695101933)
                  ·
                    refine ⟨3202951971367838510663225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8541205256980902695101933 3202951971367838510663225)
                    ·
                      refine ⟨2402213978525878882997419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202951971367838510663225 2402213978525878882997419)
                      ·
                        rfl

theorem cell23_4678295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_4678295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678295 prefixEnd_4678295 := by exact prefixLift 4678295
  have htrace : WordTrace (prefixWord ++ tailWord_4678295) baseStart_4678295 baseEnd_4678295 := by
    simpa [prefixWord, tailWord_4678295, baseEnd_4678295] using wordTrace_append hprefix tailTrace_4678295
  have hstable : (prefixWord ++ tailWord_4678295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678295).length < 2 ^ (prefixWord ++ tailWord_4678295).sum := by decide
  have hdescent : baseEnd_4678295 < baseStart_4678295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678319 : List Nat := [1, 1, 2, 1, 2, 6, 3, 2, 1, 1, 3]
def baseStart_4678319 : Nat := 118140960795 + 4678319 * 2 ^ 59
def prefixEnd_4678319 : Nat := 4983230072969 + 3 ^ 40 * 4678319 * 2
def baseEnd_4678319 : Nat := 2402226302061586789097309

theorem tailTrace_4678319 : CollatzResearch.WordTrace tailWord_4678319 prefixEnd_4678319 2402226302061586789097309 := by
  unfold tailWord_4678319
  simp only [CollatzResearch.WordTrace]
  refine ⟨170632311938256731119206011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113754874625504487412804007 170632311938256731119206011)
  ·
    refine ⟨255948467907385096678809017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170632311938256731119206011 255948467907385096678809017)
    ·
      refine ⟨191961350930538822509106763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255948467907385096678809017 191961350930538822509106763)
      ·
        refine ⟨287942026395808233763660145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191961350930538822509106763 287942026395808233763660145)
        ·
          refine ⟨215956519796856175322745109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287942026395808233763660145 215956519796856175322745109)
          ·
            refine ⟨10122961865477633218253677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 215956519796856175322745109 10122961865477633218253677)
            ·
              refine ⟨3796110699554112456845129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10122961865477633218253677 3796110699554112456845129)
              ·
                refine ⟨2847083024665584342633847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3796110699554112456845129 2847083024665584342633847)
                ·
                  refine ⟨4270624536998376513950771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847083024665584342633847 4270624536998376513950771)
                  ·
                    refine ⟨6405936805497564770926157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270624536998376513950771 6405936805497564770926157)
                    ·
                      refine ⟨2402226302061586789097309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6405936805497564770926157 2402226302061586789097309)
                      ·
                        rfl

theorem cell23_4678319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 1, 3].length) (baseStart_4678319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678319 prefixEnd_4678319 := by exact prefixLift 4678319
  have htrace : WordTrace (prefixWord ++ tailWord_4678319) baseStart_4678319 baseEnd_4678319 := by
    simpa [prefixWord, tailWord_4678319, baseEnd_4678319] using wordTrace_append hprefix tailTrace_4678319
  have hstable : (prefixWord ++ tailWord_4678319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678319).length < 2 ^ (prefixWord ++ tailWord_4678319).sum := by decide
  have hdescent : baseEnd_4678319 < baseStart_4678319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678326 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_4678326 : Nat := 118140960795 + 4678326 * 2 ^ 59
def prefixEnd_4678326 : Nat := 4983230072969 + 3 ^ 40 * 4678326 * 2
def baseEnd_4678326 : Nat := 266914432936240917967753

theorem tailTrace_4678326 : CollatzResearch.WordTrace tailWord_4678326 prefixEnd_4678326 266914432936240917967753 := by
  unfold tailWord_4678326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10664535453076960707169427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113755044832820914209807221 10664535453076960707169427)
  ·
    refine ⟨15996803179615441060754141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10664535453076960707169427 15996803179615441060754141)
    ·
      refine ⟨5998801192355790397782803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15996803179615441060754141 5998801192355790397782803)
      ·
        refine ⟨8998201788533685596674205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5998801192355790397782803 8998201788533685596674205)
        ·
          refine ⟨3374325670700132098752827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8998201788533685596674205 3374325670700132098752827)
          ·
            refine ⟨5061488506050198148129241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374325670700132098752827 5061488506050198148129241)
            ·
              refine ⟨3796116379537648611096931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5061488506050198148129241 3796116379537648611096931)
              ·
                refine ⟨5694174569306472916645397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796116379537648611096931 5694174569306472916645397)
                ·
                  refine ⟨266914432936240917967753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5694174569306472916645397 266914432936240917967753)
                  ·
                    rfl

theorem cell23_4678326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_4678326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678326 prefixEnd_4678326 := by exact prefixLift 4678326
  have htrace : WordTrace (prefixWord ++ tailWord_4678326) baseStart_4678326 baseEnd_4678326 := by
    simpa [prefixWord, tailWord_4678326, baseEnd_4678326] using wordTrace_append hprefix tailTrace_4678326
  have hstable : (prefixWord ++ tailWord_4678326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678326).length < 2 ^ (prefixWord ++ tailWord_4678326).sum := by decide
  have hdescent : baseEnd_4678326 < baseStart_4678326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678335 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 2, 4]
def baseStart_4678335 : Nat := 118140960795 + 4678335 * 2 ^ 59
def prefixEnd_4678335 : Nat := 4983230072969 + 3 ^ 40 * 4678335 * 2
def baseEnd_4678335 : Nat := 800744839250686242165745

theorem tailTrace_4678335 : CollatzResearch.WordTrace tailWord_4678335 prefixEnd_4678335 800744839250686242165745 := by
  unfold tailWord_4678335
  simp only [CollatzResearch.WordTrace]
  refine ⟨170632895506198765851788459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113755263670799177234525639 170632895506198765851788459)
  ·
    refine ⟨255949343259298148777682689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170632895506198765851788459 255949343259298148777682689)
    ·
      refine ⟨191962007444473611583262017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255949343259298148777682689 191962007444473611583262017)
      ·
        refine ⟨143971505583355208687446513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191962007444473611583262017 143971505583355208687446513)
        ·
          refine ⟨107978629187516406515584885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143971505583355208687446513 107978629187516406515584885)
          ·
            refine ⟨10122996486329663110836083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107978629187516406515584885 10122996486329663110836083)
            ·
              refine ⟨15184494729494494666254125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10122996486329663110836083 15184494729494494666254125)
              ·
                refine ⟨5694185523560435499845297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15184494729494494666254125 5694185523560435499845297)
                ·
                  refine ⟨4270639142670326624883973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5694185523560435499845297 4270639142670326624883973)
                  ·
                    refine ⟨800744839250686242165745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270639142670326624883973 800744839250686242165745)
                    ·
                      rfl

theorem cell23_4678335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_4678335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678335 prefixEnd_4678335 := by exact prefixLift 4678335
  have htrace : WordTrace (prefixWord ++ tailWord_4678335) baseStart_4678335 baseEnd_4678335 := by
    simpa [prefixWord, tailWord_4678335, baseEnd_4678335] using wordTrace_append hprefix tailTrace_4678335
  have hstable : (prefixWord ++ tailWord_4678335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678335).length < 2 ^ (prefixWord ++ tailWord_4678335).sum := by decide
  have hdescent : baseEnd_4678335 < baseStart_4678335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678348 : List Nat := [2, 2, 1, 5, 1, 1, 2, 9]
def baseStart_4678348 : Nat := 118140960795 + 4678348 * 2 ^ 59
def prefixEnd_4678348 : Nat := 4983230072969 + 3 ^ 40 * 4678348 * 2
def baseEnd_4678348 : Nat := 88971896037058043542025

theorem tailTrace_4678348 : CollatzResearch.WordTrace tailWord_4678348 prefixEnd_4678348 88971896037058043542025 := by
  unfold tailWord_4678348
  simp only [CollatzResearch.WordTrace]
  refine ⟨85316684827575834536005849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113755579770101112714674465 85316684827575834536005849)
  ·
    refine ⟨63987513620681875902004387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85316684827575834536005849 63987513620681875902004387)
    ·
      refine ⟨95981270431022813853006581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63987513620681875902004387 95981270431022813853006581)
      ·
        refine ⟨8998244102908388798719367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95981270431022813853006581 8998244102908388798719367)
        ·
          refine ⟨13497366154362583198079051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998244102908388798719367 13497366154362583198079051)
          ·
            refine ⟨20246049231543874797118577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13497366154362583198079051 20246049231543874797118577)
            ·
              refine ⟨15184536923657906097838933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20246049231543874797118577 15184536923657906097838933)
              ·
                refine ⟨88971896037058043542025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15184536923657906097838933 88971896037058043542025)
                ·
                  rfl

theorem cell23_4678348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 9].length) (baseStart_4678348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678348 prefixEnd_4678348 := by exact prefixLift 4678348
  have htrace : WordTrace (prefixWord ++ tailWord_4678348) baseStart_4678348 baseEnd_4678348 := by
    simpa [prefixWord, tailWord_4678348, baseEnd_4678348] using wordTrace_append hprefix tailTrace_4678348
  have hstable : (prefixWord ++ tailWord_4678348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678348).length < 2 ^ (prefixWord ++ tailWord_4678348).sum := by decide
  have hdescent : baseEnd_4678348 < baseStart_4678348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678362 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3]
def baseStart_4678362 : Nat := 118140960795 + 4678362 * 2 ^ 59
def prefixEnd_4678362 : Nat := 4983230072969 + 3 ^ 40 * 4678362 * 2
def baseEnd_4678362 : Nat := 2402248381729730120859611

theorem tailTrace_4678362 : CollatzResearch.WordTrace tailWord_4678362 prefixEnd_4678362 2402248381729730120859611 := by
  unfold tailWord_4678362
  simp only [CollatzResearch.WordTrace]
  refine ⟨42658470069275237365755335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113755920184733966308680893 42658470069275237365755335)
  ·
    refine ⟨63987705103912856048633003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42658470069275237365755335 63987705103912856048633003)
    ·
      refine ⟨95981557655869284072949505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63987705103912856048633003 95981557655869284072949505)
      ·
        refine ⟨71986168241901963054712129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95981557655869284072949505 71986168241901963054712129)
        ·
          refine ⟨53989626181426472291034097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71986168241901963054712129 53989626181426472291034097)
          ·
            refine ⟨40492219636069854218275573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53989626181426472291034097 40492219636069854218275573)
            ·
              refine ⟨3796145590881548832963335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40492219636069854218275573 3796145590881548832963335)
              ·
                refine ⟨5694218386322323249445003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796145590881548832963335 5694218386322323249445003)
                ·
                  refine ⟨8541327579483484874167505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694218386322323249445003 8541327579483484874167505)
                  ·
                    refine ⟨6405995684612613655625629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8541327579483484874167505 6405995684612613655625629)
                    ·
                      refine ⟨2402248381729730120859611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6405995684612613655625629 2402248381729730120859611)
                      ·
                        rfl

theorem cell23_4678362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_4678362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678362 prefixEnd_4678362 := by exact prefixLift 4678362
  have htrace : WordTrace (prefixWord ++ tailWord_4678362) baseStart_4678362 baseEnd_4678362 := by
    simpa [prefixWord, tailWord_4678362, baseEnd_4678362] using wordTrace_append hprefix tailTrace_4678362
  have hstable : (prefixWord ++ tailWord_4678362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678362).length < 2 ^ (prefixWord ++ tailWord_4678362).sum := by decide
  have hdescent : baseEnd_4678362 < baseStart_4678362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678376 : List Nat := [2, 1, 4, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_4678376 : Nat := 118140960795 + 4678376 * 2 ^ 59
def prefixEnd_4678376 : Nat := 4983230072969 + 3 ^ 40 * 4678376 * 2
def baseEnd_4678376 : Nat := 2402255570458893066084547

theorem tailTrace_4678376 : CollatzResearch.WordTrace tailWord_4678376 prefixEnd_4678376 2402255570458893066084547 := by
  unfold tailWord_4678376
  simp only [CollatzResearch.WordTrace]
  refine ⟨85317195449525114927015491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113756260599366819902687321 85317195449525114927015491)
  ·
    refine ⟨127975793174287672390523237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85317195449525114927015491 127975793174287672390523237)
    ·
      refine ⟨23995461220178938573223107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127975793174287672390523237 23995461220178938573223107)
      ·
        refine ⟨35993191830268407859834661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23995461220178938573223107 35993191830268407859834661)
        ·
          refine ⟨6748723468175326473718999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35993191830268407859834661 6748723468175326473718999)
          ·
            refine ⟨10123085202262989710578499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748723468175326473718999 10123085202262989710578499)
            ·
              refine ⟨15184627803394484565867749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10123085202262989710578499 15184627803394484565867749)
              ·
                refine ⟨2847117713136465856100203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15184627803394484565867749 2847117713136465856100203)
                ·
                  refine ⟨4270676569704698784150305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847117713136465856100203 4270676569704698784150305)
                  ·
                    refine ⟨3203007427278524088112729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270676569704698784150305 3203007427278524088112729)
                    ·
                      refine ⟨2402255570458893066084547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3203007427278524088112729 2402255570458893066084547)
                      ·
                        rfl

theorem cell23_4678376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_4678376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678376 prefixEnd_4678376 := by exact prefixLift 4678376
  have htrace : WordTrace (prefixWord ++ tailWord_4678376) baseStart_4678376 baseEnd_4678376 := by
    simpa [prefixWord, tailWord_4678376, baseEnd_4678376] using wordTrace_append hprefix tailTrace_4678376
  have hstable : (prefixWord ++ tailWord_4678376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678376).length < 2 ^ (prefixWord ++ tailWord_4678376).sum := by decide
  have hdescent : baseEnd_4678376 < baseStart_4678376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678385 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 5, 3, 2]
def baseStart_4678385 : Nat := 118140960795 + 4678385 * 2 ^ 59
def prefixEnd_4678385 : Nat := 4983230072969 + 3 ^ 40 * 4678385 * 2
def baseEnd_4678385 : Nat := 2402260191784783530872005

theorem tailTrace_4678385 : CollatzResearch.WordTrace tailWord_4678385 prefixEnd_4678385 2402260191784783530872005 := by
  unfold tailWord_4678385
  simp only [CollatzResearch.WordTrace]
  refine ⟨170634719156017624391108609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113756479437345082927405739 170634719156017624391108609)
  ·
    refine ⟨127976039367013218293331457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170634719156017624391108609 127976039367013218293331457)
    ·
      refine ⟨95982029525259913719998593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127976039367013218293331457 95982029525259913719998593)
      ·
        refine ⟨71986522143944935289998945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95982029525259913719998593 71986522143944935289998945)
        ·
          refine ⟨53989891607958701467499209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71986522143944935289998945 53989891607958701467499209)
          ·
            refine ⟨40492418705969026100624407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53989891607958701467499209 40492418705969026100624407)
            ·
              refine ⟨60738628058953539150936611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40492418705969026100624407 60738628058953539150936611)
              ·
                refine ⟨91107942088430308726404917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60738628058953539150936611 91107942088430308726404917)
                ·
                  refine ⟨8541369570790341443100461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91107942088430308726404917 8541369570790341443100461)
                  ·
                    refine ⟨3203013589046378041162673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8541369570790341443100461 3203013589046378041162673)
                    ·
                      refine ⟨2402260191784783530872005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3203013589046378041162673 2402260191784783530872005)
                      ·
                        rfl

theorem cell23_4678385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_4678385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678385 prefixEnd_4678385 := by exact prefixLift 4678385
  have htrace : WordTrace (prefixWord ++ tailWord_4678385) baseStart_4678385 baseEnd_4678385 := by
    simpa [prefixWord, tailWord_4678385, baseEnd_4678385] using wordTrace_append hprefix tailTrace_4678385
  have hstable : (prefixWord ++ tailWord_4678385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678385).length < 2 ^ (prefixWord ++ tailWord_4678385).sum := by decide
  have hdescent : baseEnd_4678385 < baseStart_4678385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678415 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 1, 4, 2]
def baseStart_4678415 : Nat := 118140960795 + 4678415 * 2 ^ 59
def prefixEnd_4678415 : Nat := 4983230072969 + 3 ^ 40 * 4678415 * 2
def baseEnd_4678415 : Nat := 2402275596204418413496867

theorem tailTrace_4678415 : CollatzResearch.WordTrace tailWord_4678415 prefixEnd_4678415 2402275596204418413496867 := by
  unfold tailWord_4678415
  simp only [CollatzResearch.WordTrace]
  refine ⟨170635813345908939514700699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113757208897272626343133799 170635813345908939514700699)
  ·
    refine ⟨255953720018863409272051049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170635813345908939514700699 255953720018863409272051049)
    ·
      refine ⟨191965290014147556954038287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255953720018863409272051049 191965290014147556954038287)
      ·
        refine ⟨287947935021221335431057431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191965290014147556954038287 287947935021221335431057431)
        ·
          refine ⟨431921902531832003146586147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287947935021221335431057431 431921902531832003146586147)
          ·
            refine ⟨647882853797748004719879221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431921902531832003146586147 647882853797748004719879221)
            ·
              refine ⟨60739017543538875442488677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 647882853797748004719879221 60739017543538875442488677)
              ·
                refine ⟨11388565789413539145466627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60739017543538875442488677 11388565789413539145466627)
                ·
                  refine ⟨17082848684120308718199941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11388565789413539145466627 17082848684120308718199941)
                  ·
                    refine ⟨3203034128272557884662489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17082848684120308718199941 3203034128272557884662489)
                    ·
                      refine ⟨2402275596204418413496867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3203034128272557884662489 2402275596204418413496867)
                      ·
                        rfl

theorem cell23_4678415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4, 2].length) (baseStart_4678415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678415 prefixEnd_4678415 := by exact prefixLift 4678415
  have htrace : WordTrace (prefixWord ++ tailWord_4678415) baseStart_4678415 baseEnd_4678415 := by
    simpa [prefixWord, tailWord_4678415, baseEnd_4678415] using wordTrace_append hprefix tailTrace_4678415
  have hstable : (prefixWord ++ tailWord_4678415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678415).length < 2 ^ (prefixWord ++ tailWord_4678415).sum := by decide
  have hdescent : baseEnd_4678415 < baseStart_4678415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678478 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_4678478 : Nat := 118140960795 + 4678478 * 2 ^ 59
def prefixEnd_4678478 : Nat := 4983230072969 + 3 ^ 40 * 4678478 * 2
def baseEnd_4678478 : Nat := 2402307945485651667009077

theorem tailTrace_4678478 : CollatzResearch.WordTrace tailWord_4678478 prefixEnd_4678478 2402307945485651667009077 := by
  unfold tailWord_4678478
  simp only [CollatzResearch.WordTrace]
  refine ⟨21329763893085087659280511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113758740763120467516162725 21329763893085087659280511)
  ·
    refine ⟨31994645839627631488920767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21329763893085087659280511 31994645839627631488920767)
    ·
      refine ⟨47991968759441447233381151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31994645839627631488920767 47991968759441447233381151)
      ·
        refine ⟨71987953139162170850071727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47991968759441447233381151 71987953139162170850071727)
        ·
          refine ⟨107981929708743256275107591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71987953139162170850071727 107981929708743256275107591)
          ·
            refine ⟨161972894563114884412661387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107981929708743256275107591 161972894563114884412661387)
            ·
              refine ⟨242959341844672326618992081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161972894563114884412661387 242959341844672326618992081)
              ·
                refine ⟨182219506383504244964244061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242959341844672326618992081 182219506383504244964244061)
                ·
                  refine ⟨68332314893814091861591523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182219506383504244964244061 68332314893814091861591523)
                  ·
                    refine ⟨102498472340721137792387285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68332314893814091861591523 102498472340721137792387285)
                    ·
                      refine ⟨2402307945485651667009077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102498472340721137792387285 2402307945485651667009077)
                      ·
                        rfl

theorem cell23_4678478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_4678478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678478 prefixEnd_4678478 := by exact prefixLift 4678478
  have htrace : WordTrace (prefixWord ++ tailWord_4678478) baseStart_4678478 baseEnd_4678478 := by
    simpa [prefixWord, tailWord_4678478, baseEnd_4678478] using wordTrace_append hprefix tailTrace_4678478
  have hstable : (prefixWord ++ tailWord_4678478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678478).length < 2 ^ (prefixWord ++ tailWord_4678478).sum := by decide
  have hdescent : baseEnd_4678478 < baseStart_4678478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678485 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_4678485 : Nat := 118140960795 + 4678485 * 2 ^ 59
def prefixEnd_4678485 : Nat := 4983230072969 + 3 ^ 40 * 4678485 * 2
def baseEnd_4678485 : Nat := 800770513283411046540515

theorem tailTrace_4678485 : CollatzResearch.WordTrace tailWord_4678485 prefixEnd_4678485 800770513283411046540515 := by
  unfold tailWord_4678485
  simp only [CollatzResearch.WordTrace]
  refine ⟨170638366455655341469748909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113758910970436894313165939 170638366455655341469748909)
  ·
    refine ⟨63989387420870753051155841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170638366455655341469748909 63989387420870753051155841)
    ·
      refine ⟨47992040565653064788366881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63989387420870753051155841 47992040565653064788366881)
      ·
        refine ⟨35994030424239798591275161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47992040565653064788366881 35994030424239798591275161)
        ·
          refine ⟨26995522818179848943456371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35994030424239798591275161 26995522818179848943456371)
          ·
            refine ⟨40493284227269773415184557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26995522818179848943456371 40493284227269773415184557)
            ·
              refine ⟨15184981585226165030694209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40493284227269773415184557 15184981585226165030694209)
              ·
                refine ⟨11388736188919623773020657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15184981585226165030694209 11388736188919623773020657)
                ·
                  refine ⟨8541552141689717829765493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11388736188919623773020657 8541552141689717829765493)
                  ·
                    refine ⟨800770513283411046540515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8541552141689717829765493 800770513283411046540515)
                    ·
                      rfl

theorem cell23_4678485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_4678485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678485 prefixEnd_4678485 := by exact prefixLift 4678485
  have htrace : WordTrace (prefixWord ++ tailWord_4678485) baseStart_4678485 baseEnd_4678485 := by
    simpa [prefixWord, tailWord_4678485, baseEnd_4678485] using wordTrace_append hprefix tailTrace_4678485
  have hstable : (prefixWord ++ tailWord_4678485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678485).length < 2 ^ (prefixWord ++ tailWord_4678485).sum := by decide
  have hdescent : baseEnd_4678485 < baseStart_4678485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678515 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 3, 4]
def baseStart_4678515 : Nat := 118140960795 + 4678515 * 2 ^ 59
def prefixEnd_4678515 : Nat := 4983230072969 + 3 ^ 40 * 4678515 * 2
def baseEnd_4678515 : Nat := 800775648089956007415469

theorem tailTrace_4678515 : CollatzResearch.WordTrace tailWord_4678515 prefixEnd_4678515 800775648089956007415469 := by
  unfold tailWord_4678515
  simp only [CollatzResearch.WordTrace]
  refine ⟨170639460645546656593340999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113759640430364437728893999 170639460645546656593340999)
  ·
    refine ⟨255959190968319984890011499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170639460645546656593340999 255959190968319984890011499)
    ·
      refine ⟨383938786452479977335017249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255959190968319984890011499 383938786452479977335017249)
      ·
        refine ⟨287954089839359983001262937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383938786452479977335017249 287954089839359983001262937)
        ·
          refine ⟨215965567379519987250947203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287954089839359983001262937 215965567379519987250947203)
          ·
            refine ⟨323948351069279980876420805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215965567379519987250947203 323948351069279980876420805)
            ·
              refine ⟨60740315825489996414328901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 323948351069279980876420805 60740315825489996414328901)
              ·
                refine ⟨11388809217279374327686669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60740315825489996414328901 11388809217279374327686669)
                ·
                  refine ⟨4270803456479765372882501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11388809217279374327686669 4270803456479765372882501)
                  ·
                    refine ⟨800775648089956007415469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270803456479765372882501 800775648089956007415469)
                    ·
                      rfl

theorem cell23_4678515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 4].length) (baseStart_4678515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678515 prefixEnd_4678515 := by exact prefixLift 4678515
  have htrace : WordTrace (prefixWord ++ tailWord_4678515) baseStart_4678515 baseEnd_4678515 := by
    simpa [prefixWord, tailWord_4678515, baseEnd_4678515] using wordTrace_append hprefix tailTrace_4678515
  have hstable : (prefixWord ++ tailWord_4678515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678515).length < 2 ^ (prefixWord ++ tailWord_4678515).sum := by decide
  have hdescent : baseEnd_4678515 < baseStart_4678515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678525 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_4678525 : Nat := 118140960795 + 4678525 * 2 ^ 59
def prefixEnd_4678525 : Nat := 4983230072969 + 3 ^ 40 * 4678525 * 2
def baseEnd_4678525 : Nat := 2402332079076412983121361

theorem tailTrace_4678525 : CollatzResearch.WordTrace tailWord_4678525 prefixEnd_4678525 2402332079076412983121361 := by
  unfold tailWord_4678525
  simp only [CollatzResearch.WordTrace]
  refine ⟨170639825375510428301205029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113759883583673618867470019 170639825375510428301205029)
  ·
    refine ⟨31994967257908205306475943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170639825375510428301205029 31994967257908205306475943)
    ·
      refine ⟨47992450886862307959713915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31994967257908205306475943 47992450886862307959713915)
      ·
        refine ⟨71988676330293461939570873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47992450886862307959713915 71988676330293461939570873)
        ·
          refine ⟨53991507247720096454678155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71988676330293461939570873 53991507247720096454678155)
          ·
            refine ⟨80987260871580144682017233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53991507247720096454678155 80987260871580144682017233)
            ·
              refine ⟨60740445653685108511512925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80987260871580144682017233 60740445653685108511512925)
              ·
                refine ⟨22777667120131915691817347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60740445653685108511512925 22777667120131915691817347)
                ·
                  refine ⟨34166500680197873537726021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22777667120131915691817347 34166500680197873537726021)
                  ·
                    refine ⟨6406218877537101288323629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34166500680197873537726021 6406218877537101288323629)
                    ·
                      refine ⟨2402332079076412983121361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6406218877537101288323629 2402332079076412983121361)
                      ·
                        rfl

theorem cell23_4678525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_4678525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678525 prefixEnd_4678525 := by exact prefixLift 4678525
  have htrace : WordTrace (prefixWord ++ tailWord_4678525) baseStart_4678525 baseEnd_4678525 := by
    simpa [prefixWord, tailWord_4678525, baseEnd_4678525] using wordTrace_append hprefix tailTrace_4678525
  have hstable : (prefixWord ++ tailWord_4678525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678525).length < 2 ^ (prefixWord ++ tailWord_4678525).sum := by decide
  have hdescent : baseEnd_4678525 < baseStart_4678525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678528 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 8]
def baseStart_4678528 : Nat := 118140960795 + 4678528 * 2 ^ 59
def prefixEnd_4678528 : Nat := 4983230072969 + 3 ^ 40 * 4678528 * 2
def baseEnd_4678528 : Nat := 266925957724264052375983

theorem tailTrace_4678528 : CollatzResearch.WordTrace tailWord_4678528 prefixEnd_4678528 266925957724264052375983 := by
  unfold tailWord_4678528
  simp only [CollatzResearch.WordTrace]
  refine ⟨85319967397249779906782119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113759956529666373209042825 85319967397249779906782119)
  ·
    refine ⟨127979951095874669860173179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85319967397249779906782119 127979951095874669860173179)
    ·
      refine ⟨191969926643812004790259769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127979951095874669860173179 191969926643812004790259769)
      ·
        refine ⟨143977444982859003592694827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191969926643812004790259769 143977444982859003592694827)
        ·
          refine ⟨215966167474288505389042241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143977444982859003592694827 215966167474288505389042241)
          ·
            refine ⟨161974625605716379041781681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215966167474288505389042241 161974625605716379041781681)
            ·
              refine ⟨121480969204287284281336261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161974625605716379041781681 121480969204287284281336261)
              ·
                refine ⟨22777681725803865802750549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121480969204287284281336261 22777681725803865802750549)
                ·
                  refine ⟨266925957724264052375983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22777681725803865802750549 266925957724264052375983)
                  ·
                    rfl

theorem cell23_4678528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_4678528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678528 prefixEnd_4678528 := by exact prefixLift 4678528
  have htrace : WordTrace (prefixWord ++ tailWord_4678528) baseStart_4678528 baseEnd_4678528 := by
    simpa [prefixWord, tailWord_4678528, baseEnd_4678528] using wordTrace_append hprefix tailTrace_4678528
  have hstable : (prefixWord ++ tailWord_4678528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678528).length < 2 ^ (prefixWord ++ tailWord_4678528).sum := by decide
  have hdescent : baseEnd_4678528 < baseStart_4678528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678549 : List Nat := [1, 3, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_4678549 : Nat := 118140960795 + 4678549 * 2 ^ 59
def prefixEnd_4678549 : Nat := 4983230072969 + 3 ^ 40 * 4678549 * 2
def baseEnd_4678549 : Nat := 800781467537373629740417

theorem tailTrace_4678549 : CollatzResearch.WordTrace tailWord_4678549 prefixEnd_4678549 800781467537373629740417 := by
  unfold tailWord_4678549
  simp only [CollatzResearch.WordTrace]
  refine ⟨170640700727423480400078701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113760467151615653600052467 170640700727423480400078701)
  ·
    refine ⟨63990262772783805150029513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170640700727423480400078701 63990262772783805150029513)
    ·
      refine ⟨47992697079587853862522135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63990262772783805150029513 47992697079587853862522135)
      ·
        refine ⟨71989045619381780793783203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47992697079587853862522135 71989045619381780793783203)
        ·
          refine ⟨107983568429072671190674805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71989045619381780793783203 107983568429072671190674805)
          ·
            refine ⟨10123459540225562924125763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107983568429072671190674805 10123459540225562924125763)
            ·
              refine ⟨15185189310338344386188645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10123459540225562924125763 15185189310338344386188645)
              ·
                refine ⟨2847222995688439572410371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15185189310338344386188645 2847222995688439572410371)
                ·
                  refine ⟨4270834493532659358615557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847222995688439572410371 4270834493532659358615557)
                  ·
                    refine ⟨800781467537373629740417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270834493532659358615557 800781467537373629740417)
                    ·
                      rfl

theorem cell23_4678549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_4678549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678549 prefixEnd_4678549 := by exact prefixLift 4678549
  have htrace : WordTrace (prefixWord ++ tailWord_4678549) baseStart_4678549 baseEnd_4678549 := by
    simpa [prefixWord, tailWord_4678549, baseEnd_4678549] using wordTrace_append hprefix tailTrace_4678549
  have hstable : (prefixWord ++ tailWord_4678549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678549).length < 2 ^ (prefixWord ++ tailWord_4678549).sum := by decide
  have hdescent : baseEnd_4678549 < baseStart_4678549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678562 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 6]
def baseStart_4678562 : Nat := 118140960795 + 4678562 * 2 ^ 59
def prefixEnd_4678562 : Nat := 4983230072969 + 3 ^ 40 * 4678562 * 2
def baseEnd_4678562 : Nat := 266927897540069926484299

theorem tailTrace_4678562 : CollatzResearch.WordTrace tailWord_4678562 prefixEnd_4678562 266927897540069926484299 := by
  unfold tailWord_4678562
  simp only [CollatzResearch.WordTrace]
  refine ⟨42660293719094095905075485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113760783250917589080201293 42660293719094095905075485)
  ·
    refine ⟨15997610144660285964403307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42660293719094095905075485 15997610144660285964403307)
    ·
      refine ⟨23996415216990428946604961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15997610144660285964403307 23996415216990428946604961)
      ·
        refine ⟨17997311412742821709953721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23996415216990428946604961 17997311412742821709953721)
        ·
          refine ⟨13497983559557116282465291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17997311412742821709953721 13497983559557116282465291)
          ·
            refine ⟨20246975339335674423697937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13497983559557116282465291 20246975339335674423697937)
            ·
              refine ⟨15185231504501755817773453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20246975339335674423697937 15185231504501755817773453)
              ·
                refine ⟨5694461814188158431665045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15185231504501755817773453 5694461814188158431665045)
                ·
                  refine ⟨266927897540069926484299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5694461814188158431665045 266927897540069926484299)
                  ·
                    rfl

theorem cell23_4678562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_4678562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678562 prefixEnd_4678562 := by exact prefixLift 4678562
  have htrace : WordTrace (prefixWord ++ tailWord_4678562) baseStart_4678562 baseEnd_4678562 := by
    simpa [prefixWord, tailWord_4678562, baseEnd_4678562] using wordTrace_append hprefix tailTrace_4678562
  have hstable : (prefixWord ++ tailWord_4678562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678562).length < 2 ^ (prefixWord ++ tailWord_4678562).sum := by decide
  have hdescent : baseEnd_4678562 < baseStart_4678562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678572 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_4678572 : Nat := 118140960795 + 4678572 * 2 ^ 59
def prefixEnd_4678572 : Nat := 4983230072969 + 3 ^ 40 * 4678572 * 2
def baseEnd_4678572 : Nat := 2402356212667174299233645

theorem tailTrace_4678572 : CollatzResearch.WordTrace tailWord_4678572 prefixEnd_4678572 2402356212667174299233645 := by
  unfold tailWord_4678572
  simp only [CollatzResearch.WordTrace]
  refine ⟨85320769803170077664082985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113761026404226770218777313 85320769803170077664082985)
  ·
    refine ⟨63990577352377558248062239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85320769803170077664082985 63990577352377558248062239)
    ·
      refine ⟨95985866028566337372093359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63990577352377558248062239 95985866028566337372093359)
      ·
        refine ⟨143978799042849506058140039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95985866028566337372093359 143978799042849506058140039)
        ·
          refine ⟨215968198564274259087210059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143978799042849506058140039 215968198564274259087210059)
          ·
            refine ⟨323952297846411388630815089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215968198564274259087210059 323952297846411388630815089)
            ·
              refine ⟨242964223384808541473111317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323952297846411388630815089 242964223384808541473111317)
              ·
                refine ⟨11388947971162900381552093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 242964223384808541473111317 11388947971162900381552093)
                ·
                  refine ⟨4270855489186087643082035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11388947971162900381552093 4270855489186087643082035)
                  ·
                    refine ⟨6406283233779131464623053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270855489186087643082035 6406283233779131464623053)
                    ·
                      refine ⟨2402356212667174299233645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6406283233779131464623053 2402356212667174299233645)
                      ·
                        rfl

theorem cell23_4678572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_4678572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678572 prefixEnd_4678572 := by exact prefixLift 4678572
  have htrace : WordTrace (prefixWord ++ tailWord_4678572) baseStart_4678572 baseEnd_4678572 := by
    simpa [prefixWord, tailWord_4678572, baseEnd_4678572] using wordTrace_append hprefix tailTrace_4678572
  have hstable : (prefixWord ++ tailWord_4678572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678572).length < 2 ^ (prefixWord ++ tailWord_4678572).sum := by decide
  have hdescent : baseEnd_4678572 < baseStart_4678572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678573 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4678573 : Nat := 118140960795 + 4678573 * 2 ^ 59
def prefixEnd_4678573 : Nat := 4983230072969 + 3 ^ 40 * 4678573 * 2
def baseEnd_4678573 : Nat := 2402356726147828795321141

theorem tailTrace_4678573 : CollatzResearch.WordTrace tailWord_4678573 prefixEnd_4678573 2402356726147828795321141 := by
  unfold tailWord_4678573
  simp only [CollatzResearch.WordTrace]
  refine ⟨170641576079336532498952373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113761050719557688332634915 170641576079336532498952373)
  ·
    refine ⟨15997647757437799921776785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170641576079336532498952373 15997647757437799921776785)
    ·
      refine ⟨11998235818078349941332589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15997647757437799921776785 11998235818078349941332589)
      ·
        refine ⟨4499338431779381227999721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11998235818078349941332589 4499338431779381227999721)
        ·
          refine ⟨3374503823834535920999791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4499338431779381227999721 3374503823834535920999791)
          ·
            refine ⟨5061755735751803881499687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374503823834535920999791 5061755735751803881499687)
            ·
              refine ⟨7592633603627705822249531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5061755735751803881499687 7592633603627705822249531)
              ·
                refine ⟨11388950405441558733374297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7592633603627705822249531 11388950405441558733374297)
                ·
                  refine ⟨8541712804081169050030723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11388950405441558733374297 8541712804081169050030723)
                  ·
                    refine ⟨12812569206121753575046085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8541712804081169050030723 12812569206121753575046085)
                    ·
                      refine ⟨2402356726147828795321141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12812569206121753575046085 2402356726147828795321141)
                      ·
                        rfl

theorem cell23_4678573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4678573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678573 prefixEnd_4678573 := by exact prefixLift 4678573
  have htrace : WordTrace (prefixWord ++ tailWord_4678573) baseStart_4678573 baseEnd_4678573 := by
    simpa [prefixWord, tailWord_4678573, baseEnd_4678573] using wordTrace_append hprefix tailTrace_4678573
  have hstable : (prefixWord ++ tailWord_4678573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678573).length < 2 ^ (prefixWord ++ tailWord_4678573).sum := by decide
  have hdescent : baseEnd_4678573 < baseStart_4678573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678592 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 1, 5]
def baseStart_4678592 : Nat := 118140960795 + 4678592 * 2 ^ 59
def prefixEnd_4678592 : Nat := 4983230072969 + 3 ^ 40 * 4678592 * 2
def baseEnd_4678592 : Nat := 800788827426754740327851

theorem tailTrace_4678592 : CollatzResearch.WordTrace tailWord_4678592 prefixEnd_4678592 800788827426754740327851 := by
  unfold tailWord_4678592
  simp only [CollatzResearch.WordTrace]
  refine ⟨85321134533133849371947015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113761512710845132495929353 85321134533133849371947015)
  ·
    refine ⟨127981701799700774057920523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85321134533133849371947015 127981701799700774057920523)
    ·
      refine ⟨191972552699551161086880785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127981701799700774057920523 191972552699551161086880785)
      ·
        refine ⟨143979414524663370815160589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191972552699551161086880785 143979414524663370815160589)
        ·
          refine ⟨53992280446748764055685221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143979414524663370815160589 53992280446748764055685221)
          ·
            refine ⟨10123552583765393260440979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53992280446748764055685221 10123552583765393260440979)
            ·
              refine ⟨15185328875648089890661469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10123552583765393260440979 15185328875648089890661469)
              ·
                refine ⟨5694498328368033708998051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15185328875648089890661469 5694498328368033708998051)
                ·
                  refine ⟨8541747492552050563497077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694498328368033708998051 8541747492552050563497077)
                  ·
                    refine ⟨800788827426754740327851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8541747492552050563497077 800788827426754740327851)
                    ·
                      rfl

theorem cell23_4678592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_4678592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678592 prefixEnd_4678592 := by exact prefixLift 4678592
  have htrace : WordTrace (prefixWord ++ tailWord_4678592) baseStart_4678592 baseEnd_4678592 := by
    simpa [prefixWord, tailWord_4678592, baseEnd_4678592] using wordTrace_append hprefix tailTrace_4678592
  have hstable : (prefixWord ++ tailWord_4678592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678592).length < 2 ^ (prefixWord ++ tailWord_4678592).sum := by decide
  have hdescent : baseEnd_4678592 < baseStart_4678592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678596 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 6]
def baseStart_4678596 : Nat := 118140960795 + 4678596 * 2 ^ 59
def prefixEnd_4678596 : Nat := 4983230072969 + 3 ^ 40 * 4678596 * 2
def baseEnd_4678596 : Nat := 266929837355875800592615

theorem tailTrace_4678596 : CollatzResearch.WordTrace tailWord_4678596 prefixEnd_4678596 266929837355875800592615 := by
  unfold tailWord_4678596
  simp only [CollatzResearch.WordTrace]
  refine ⟨85321207479126603713519821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113761609972168804951359761 85321207479126603713519821)
  ·
    refine ⟨31995452804672476392569933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85321207479126603713519821 31995452804672476392569933)
    ·
      refine ⟨11998294801752178647213725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31995452804672476392569933 11998294801752178647213725)
      ·
        refine ⟨4499360550657066992705147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11998294801752178647213725 4499360550657066992705147)
        ·
          refine ⟨6749040825985600489057721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499360550657066992705147 6749040825985600489057721)
          ·
            refine ⟨5061780619489200366793291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6749040825985600489057721 5061780619489200366793291)
            ·
              refine ⟨7592670929233800550189937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5061780619489200366793291 7592670929233800550189937)
              ·
                refine ⟨5694503196925350412642453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7592670929233800550189937 5694503196925350412642453)
                ·
                  refine ⟨266929837355875800592615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5694503196925350412642453 266929837355875800592615)
                  ·
                    rfl

theorem cell23_4678596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_4678596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678596 prefixEnd_4678596 := by exact prefixLift 4678596
  have htrace : WordTrace (prefixWord ++ tailWord_4678596) baseStart_4678596 baseEnd_4678596 := by
    simpa [prefixWord, tailWord_4678596, baseEnd_4678596] using wordTrace_append hprefix tailTrace_4678596
  have hstable : (prefixWord ++ tailWord_4678596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678596).length < 2 ^ (prefixWord ++ tailWord_4678596).sum := by decide
  have hdescent : baseEnd_4678596 < baseStart_4678596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678606 : List Nat := [4, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_4678606 : Nat := 118140960795 + 4678606 * 2 ^ 59
def prefixEnd_4678606 : Nat := 4983230072969 + 3 ^ 40 * 4678606 * 2
def baseEnd_4678606 : Nat := 2402373671009427166208489

theorem tailTrace_4678606 : CollatzResearch.WordTrace tailWord_4678606 prefixEnd_4678606 2402373671009427166208489 := by
  unfold tailWord_4678606
  simp only [CollatzResearch.WordTrace]
  refine ⟨21330347461027122391862959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113761853125477986089935781 21330347461027122391862959)
  ·
    refine ⟨31995521191540683587794439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21330347461027122391862959 31995521191540683587794439)
    ·
      refine ⟨47993281787311025381691659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31995521191540683587794439 47993281787311025381691659)
      ·
        refine ⟨71989922680966538072537489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47993281787311025381691659 71989922680966538072537489)
        ·
          refine ⟨53992442010724903554403117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71989922680966538072537489 53992442010724903554403117)
          ·
            refine ⟨20247165754021838832901169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53992442010724903554403117 20247165754021838832901169)
            ·
              refine ⟨15185374315516379124675877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20247165754021838832901169 15185374315516379124675877)
              ·
                refine ⟨2847257684159321085876727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15185374315516379124675877 2847257684159321085876727)
                ·
                  refine ⟨4270886526238981628815091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847257684159321085876727 4270886526238981628815091)
                  ·
                    refine ⟨6406329789358472443222637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270886526238981628815091 6406329789358472443222637)
                    ·
                      refine ⟨2402373671009427166208489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6406329789358472443222637 2402373671009427166208489)
                      ·
                        rfl

theorem cell23_4678606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_4678606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678606 prefixEnd_4678606 := by exact prefixLift 4678606
  have htrace : WordTrace (prefixWord ++ tailWord_4678606) baseStart_4678606 baseEnd_4678606 := by
    simpa [prefixWord, tailWord_4678606, baseEnd_4678606] using wordTrace_append hprefix tailTrace_4678606
  have hstable : (prefixWord ++ tailWord_4678606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678606).length < 2 ^ (prefixWord ++ tailWord_4678606).sum := by decide
  have hdescent : baseEnd_4678606 < baseStart_4678606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678615 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_4678615 : Nat := 118140960795 + 4678615 * 2 ^ 59
def prefixEnd_4678615 : Nat := 4983230072969 + 3 ^ 40 * 4678615 * 2
def baseEnd_4678615 : Nat := 2402378292335317630995947

theorem tailTrace_4678615 : CollatzResearch.WordTrace tailWord_4678615 prefixEnd_4678615 2402378292335317630995947 := by
  unfold tailWord_4678615
  simp only [CollatzResearch.WordTrace]
  refine ⟨170643107945184373671981299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113762071963456249114654199 170643107945184373671981299)
  ·
    refine ⟨255964661917776560507971949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170643107945184373671981299 255964661917776560507971949)
    ·
      refine ⟨95986748219166210190489481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255964661917776560507971949 95986748219166210190489481)
      ·
        refine ⟨71990061164374657642867111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95986748219166210190489481 71990061164374657642867111)
        ·
          refine ⟨107985091746561986464300667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71990061164374657642867111 107985091746561986464300667)
          ·
            refine ⟨161977637619842979696451001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107985091746561986464300667 161977637619842979696451001)
            ·
              refine ⟨121483228214882234772338251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161977637619842979696451001 121483228214882234772338251)
              ·
                refine ⟨182224842322323352158507377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121483228214882234772338251 182224842322323352158507377)
                ·
                  refine ⟨136668631741742514118880533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182224842322323352158507377 136668631741742514118880533)
                  ·
                    refine ⟨6406342112894180349322525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136668631741742514118880533 6406342112894180349322525)
                    ·
                      refine ⟨2402378292335317630995947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6406342112894180349322525 2402378292335317630995947)
                      ·
                        rfl

theorem cell23_4678615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_4678615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678615 prefixEnd_4678615 := by exact prefixLift 4678615
  have htrace : WordTrace (prefixWord ++ tailWord_4678615) baseStart_4678615 baseEnd_4678615 := by
    simpa [prefixWord, tailWord_4678615, baseEnd_4678615] using wordTrace_append hprefix tailTrace_4678615
  have hstable : (prefixWord ++ tailWord_4678615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678615).length < 2 ^ (prefixWord ++ tailWord_4678615).sum := by decide
  have hdescent : baseEnd_4678615 < baseStart_4678615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678626 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4678626 : Nat := 118140960795 + 4678626 * 2 ^ 59
def prefixEnd_4678626 : Nat := 4983230072969 + 3 ^ 40 * 4678626 * 2
def baseEnd_4678626 : Nat := 800794646874172362652799

theorem tailTrace_4678626 : CollatzResearch.WordTrace tailWord_4678626 prefixEnd_4678626 800794646874172362652799 := by
  unfold tailWord_4678626
  simp only [CollatzResearch.WordTrace]
  refine ⟨42660877287036130637657933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113762339432096348367087821 42660877287036130637657933)
  ·
    refine ⟨15997828982638548989121725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42660877287036130637657933 15997828982638548989121725)
    ·
      refine ⟨5999185868489455870920647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15997828982638548989121725 5999185868489455870920647)
      ·
        refine ⟨8998778802734183806380971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5999185868489455870920647 8998778802734183806380971)
        ·
          refine ⟨13498168204101275709571457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998778802734183806380971 13498168204101275709571457)
          ·
            refine ⟨10123626153075956782178593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13498168204101275709571457 10123626153075956782178593)
            ·
              refine ⟨7592719614806967586633945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10123626153075956782178593 7592719614806967586633945)
              ·
                refine ⟨5694539711105225689975459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7592719614806967586633945 5694539711105225689975459)
                ·
                  refine ⟨8541809566657838534963189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694539711105225689975459 8541809566657838534963189)
                  ·
                    refine ⟨800794646874172362652799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8541809566657838534963189 800794646874172362652799)
                    ·
                      rfl

theorem cell23_4678626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4678626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678626 prefixEnd_4678626 := by exact prefixLift 4678626
  have htrace : WordTrace (prefixWord ++ tailWord_4678626) baseStart_4678626 baseEnd_4678626 := by
    simpa [prefixWord, tailWord_4678626, baseEnd_4678626] using wordTrace_append hprefix tailTrace_4678626
  have hstable : (prefixWord ++ tailWord_4678626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678626).length < 2 ^ (prefixWord ++ tailWord_4678626).sum := by decide
  have hdescent : baseEnd_4678626 < baseStart_4678626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678632 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_4678632 : Nat := 118140960795 + 4678632 * 2 ^ 59
def prefixEnd_4678632 : Nat := 4983230072969 + 3 ^ 40 * 4678632 * 2
def baseEnd_4678632 : Nat := 2402387021506444064483369

theorem tailTrace_4678632 : CollatzResearch.WordTrace tailWord_4678632 prefixEnd_4678632 2402387021506444064483369 := by
  unfold tailWord_4678632
  simp only [CollatzResearch.WordTrace]
  refine ⟨85321863993061392787675075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113762485324081857050233433 85321863993061392787675075)
  ·
    refine ⟨127982795989592089181512613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85321863993061392787675075 127982795989592089181512613)
    ·
      refine ⟨23996774248048516721533615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127982795989592089181512613 23996774248048516721533615)
      ·
        refine ⟨35995161372072775082300423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23996774248048516721533615 35995161372072775082300423)
        ·
          refine ⟨53992742058109162623450635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35995161372072775082300423 53992742058109162623450635)
          ·
            refine ⟨80989113087163743935175953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53992742058109162623450635 80989113087163743935175953)
            ·
              refine ⟨60741834815372807951381965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80989113087163743935175953 60741834815372807951381965)
              ·
                refine ⟨22778188055764802981768237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60741834815372807951381965 22778188055764802981768237)
                ·
                  refine ⟨8541820520911801118163089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22778188055764802981768237 8541820520911801118163089)
                  ·
                    refine ⟨6406365390683850838622317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8541820520911801118163089 6406365390683850838622317)
                    ·
                      refine ⟨2402387021506444064483369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6406365390683850838622317 2402387021506444064483369)
                      ·
                        rfl

theorem cell23_4678632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_4678632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678632 prefixEnd_4678632 := by exact prefixLift 4678632
  have htrace : WordTrace (prefixWord ++ tailWord_4678632) baseStart_4678632 baseEnd_4678632 := by
    simpa [prefixWord, tailWord_4678632, baseEnd_4678632] using wordTrace_append hprefix tailTrace_4678632
  have hstable : (prefixWord ++ tailWord_4678632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678632).length < 2 ^ (prefixWord ++ tailWord_4678632).sum := by decide
  have hdescent : baseEnd_4678632 < baseStart_4678632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678752 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3]
def baseStart_4678752 : Nat := 118140960795 + 4678752 * 2 ^ 59
def prefixEnd_4678752 : Nat := 4983230072969 + 3 ^ 40 * 4678752 * 2
def baseEnd_4678752 : Nat := 2402448639184983594982817

theorem tailTrace_4678752 : CollatzResearch.WordTrace tailWord_4678752 prefixEnd_4678752 2402448639184983594982817 := by
  unfold tailWord_4678752
  simp only [CollatzResearch.WordTrace]
  refine ⟨85324052372844023034859255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113765403163792030713145673 85324052372844023034859255)
  ·
    refine ⟨127986078559266034552288883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85324052372844023034859255 127986078559266034552288883)
    ·
      refine ⟨191979117838899051828433325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127986078559266034552288883 191979117838899051828433325)
      ·
        refine ⟨71992169189587144435662497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191979117838899051828433325 71992169189587144435662497)
        ·
          refine ⟨53994126892190358326746873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71992169189587144435662497 53994126892190358326746873)
          ·
            refine ⟨40495595169142768745060155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53994126892190358326746873 40495595169142768745060155)
            ·
              refine ⟨60743392753714153117590233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40495595169142768745060155 60743392753714153117590233)
              ·
                refine ⟨45557544565285614838192675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60743392753714153117590233 45557544565285614838192675)
                ·
                  refine ⟨68336316847928422257289013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45557544565285614838192675 68336316847928422257289013)
                  ·
                    refine ⟨6406529704493289586620845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68336316847928422257289013 6406529704493289586620845)
                    ·
                      refine ⟨2402448639184983594982817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6406529704493289586620845 2402448639184983594982817)
                      ·
                        rfl

theorem cell23_4678752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_4678752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678752 prefixEnd_4678752 := by exact prefixLift 4678752
  have htrace : WordTrace (prefixWord ++ tailWord_4678752) baseStart_4678752 baseEnd_4678752 := by
    simpa [prefixWord, tailWord_4678752, baseEnd_4678752] using wordTrace_append hprefix tailTrace_4678752
  have hstable : (prefixWord ++ tailWord_4678752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678752).length < 2 ^ (prefixWord ++ tailWord_4678752).sum := by decide
  have hdescent : baseEnd_4678752 < baseStart_4678752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678759 : List Nat := [1, 1, 5, 1, 1, 3, 1, 5, 5]
def baseStart_4678759 : Nat := 118140960795 + 4678759 * 2 ^ 59
def prefixEnd_4678759 : Nat := 4983230072969 + 3 ^ 40 * 4678759 * 2
def baseEnd_4678759 : Nat := 266939137061062785288365

theorem tailTrace_4678759 : CollatzResearch.WordTrace tailWord_4678759 prefixEnd_4678759 266939137061062785288365 := by
  unfold tailWord_4678759
  simp only [CollatzResearch.WordTrace]
  refine ⟨170648360056662686265223331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113765573371108457510148887 170648360056662686265223331)
  ·
    refine ⟨255972540084994029397834997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170648360056662686265223331 255972540084994029397834997)
    ·
      refine ⟨23997425632968190256047031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255972540084994029397834997 23997425632968190256047031)
      ·
        refine ⟨35996138449452285384070547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23997425632968190256047031 35996138449452285384070547)
        ·
          refine ⟨53994207674178428076105821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35996138449452285384070547 53994207674178428076105821)
          ·
            refine ⟨20247827877816910528539683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53994207674178428076105821 20247827877816910528539683)
            ·
              refine ⟨30371741816725365792809525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20247827877816910528539683 30371741816725365792809525)
              ·
                refine ⟨2847350795318003043075893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30371741816725365792809525 2847350795318003043075893)
                ·
                  refine ⟨266939137061062785288365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2847350795318003043075893 266939137061062785288365)
                  ·
                    rfl

theorem cell23_4678759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 5].length) (baseStart_4678759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678759 prefixEnd_4678759 := by exact prefixLift 4678759
  have htrace : WordTrace (prefixWord ++ tailWord_4678759) baseStart_4678759 baseEnd_4678759 := by
    simpa [prefixWord, tailWord_4678759, baseEnd_4678759] using wordTrace_append hprefix tailTrace_4678759
  have hstable : (prefixWord ++ tailWord_4678759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678759).length < 2 ^ (prefixWord ++ tailWord_4678759).sum := by decide
  have hdescent : baseEnd_4678759 < baseStart_4678759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678826 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4678826 : Nat := 118140960795 + 4678826 * 2 ^ 59
def prefixEnd_4678826 : Nat := 4983230072969 + 3 ^ 40 * 4678826 * 2
def baseEnd_4678826 : Nat := 2402486636753416305457477

theorem tailTrace_4678826 : CollatzResearch.WordTrace tailWord_4678826 prefixEnd_4678826 2402486636753416305457477 := by
  unfold tailWord_4678826
  simp only [CollatzResearch.WordTrace]
  refine ⟨42662700936854989176978083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113767202498279971138608221 42662700936854989176978083)
  ·
    refine ⟨63994051405282483765467125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42662700936854989176978083 63994051405282483765467125)
    ·
      refine ⟨5999442319245232853012543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63994051405282483765467125 5999442319245232853012543)
      ·
        refine ⟨8999163478867849279518815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5999442319245232853012543 8999163478867849279518815)
        ·
          refine ⟨13498745218301773919278223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8999163478867849279518815 13498745218301773919278223)
          ·
            refine ⟨20248117827452660878917335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13498745218301773919278223 20248117827452660878917335)
            ·
              refine ⟨30372176741178991318376003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20248117827452660878917335 30372176741178991318376003)
              ·
                refine ⟨45558265111768486977564005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30372176741178991318376003 45558265111768486977564005)
                ·
                  refine ⟨8542174708456591308293251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45558265111768486977564005 8542174708456591308293251)
                  ·
                    refine ⟨12813262062684886962439877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8542174708456591308293251 12813262062684886962439877)
                    ·
                      refine ⟨2402486636753416305457477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12813262062684886962439877 2402486636753416305457477)
                      ·
                        rfl

theorem cell23_4678826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4678826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678826 prefixEnd_4678826 := by exact prefixLift 4678826
  have htrace : WordTrace (prefixWord ++ tailWord_4678826) baseStart_4678826 baseEnd_4678826 := by
    simpa [prefixWord, tailWord_4678826, baseEnd_4678826] using wordTrace_append hprefix tailTrace_4678826
  have hstable : (prefixWord ++ tailWord_4678826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678826).length < 2 ^ (prefixWord ++ tailWord_4678826).sum := by decide
  have hdescent : baseEnd_4678826 < baseStart_4678826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678879 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 1, 5]
def baseStart_4678879 : Nat := 118140960795 + 4678879 * 2 ^ 59
def prefixEnd_4678879 : Nat := 4983230072969 + 3 ^ 40 * 4678879 * 2
def baseEnd_4678879 : Nat := 800837950409368199364911

theorem tailTrace_4678879 : CollatzResearch.WordTrace tailWord_4678879 prefixEnd_4678879 800837950409368199364911 := by
  unfold tailWord_4678879
  simp only [CollatzResearch.WordTrace]
  refine ⟨170652736816227946759591691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113768491210818631173061127 170652736816227946759591691)
  ·
    refine ⟨255979105224341920139387537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170652736816227946759591691 255979105224341920139387537)
    ·
      refine ⟨191984328918256440104540653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255979105224341920139387537 191984328918256440104540653)
      ·
        refine ⟨71994123344346165039202745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191984328918256440104540653 71994123344346165039202745)
        ·
          refine ⟨53995592508259623779402059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71994123344346165039202745 53995592508259623779402059)
          ·
            refine ⟨80993388762389435669103089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53995592508259623779402059 80993388762389435669103089)
            ·
              refine ⟨60745041571792076751827317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80993388762389435669103089 60745041571792076751827317)
              ·
                refine ⟨5694847647355507195483811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60745041571792076751827317 5694847647355507195483811)
                ·
                  refine ⟨8542271471033260793225717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694847647355507195483811 8542271471033260793225717)
                  ·
                    refine ⟨800837950409368199364911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8542271471033260793225717 800837950409368199364911)
                    ·
                      rfl

theorem cell23_4678879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_4678879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678879 prefixEnd_4678879 := by exact prefixLift 4678879
  have htrace : WordTrace (prefixWord ++ tailWord_4678879) baseStart_4678879 baseEnd_4678879 := by
    simpa [prefixWord, tailWord_4678879, baseEnd_4678879] using wordTrace_append hprefix tailTrace_4678879
  have hstable : (prefixWord ++ tailWord_4678879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678879).length < 2 ^ (prefixWord ++ tailWord_4678879).sum := by decide
  have hdescent : baseEnd_4678879 < baseStart_4678879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678887 : List Nat := [1, 1, 5, 3, 2, 2, 2, 2, 1, 4]
def baseStart_4678887 : Nat := 118140960795 + 4678887 * 2 ^ 59
def prefixEnd_4678887 : Nat := 4983230072969 + 3 ^ 40 * 4678887 * 2
def baseEnd_4678887 : Nat := 800839319691113522264899

theorem tailTrace_4678887 : CollatzResearch.WordTrace tailWord_4678887 prefixEnd_4678887 800839319691113522264899 := by
  unfold tailWord_4678887
  simp only [CollatzResearch.WordTrace]
  refine ⟨170653028600198964125882915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113768685733465976083921943 170653028600198964125882915)
  ·
    refine ⟨255979542900298446188824373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170653028600198964125882915 255979542900298446188824373)
    ·
      refine ⟨23998082146902979330202285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255979542900298446188824373 23998082146902979330202285)
      ·
        refine ⟨8999280805088617248825857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23998082146902979330202285 8999280805088617248825857)
        ·
          refine ⟨6749460603816462936619393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8999280805088617248825857 6749460603816462936619393)
          ·
            refine ⟨5062095452862347202464545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6749460603816462936619393 5062095452862347202464545)
            ·
              refine ⟨3796571589646760401848409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5062095452862347202464545 3796571589646760401848409)
              ·
                refine ⟨2847428692235070301386307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3796571589646760401848409 2847428692235070301386307)
                ·
                  refine ⟨4271143038352605452079461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847428692235070301386307 4271143038352605452079461)
                  ·
                    refine ⟨800839319691113522264899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4271143038352605452079461 800839319691113522264899)
                    ·
                      rfl

theorem cell23_4678887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_4678887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678887 prefixEnd_4678887 := by exact prefixLift 4678887
  have htrace : WordTrace (prefixWord ++ tailWord_4678887) baseStart_4678887 baseEnd_4678887 := by
    simpa [prefixWord, tailWord_4678887, baseEnd_4678887] using wordTrace_append hprefix tailTrace_4678887
  have hstable : (prefixWord ++ tailWord_4678887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678887).length < 2 ^ (prefixWord ++ tailWord_4678887).sum := by decide
  have hdescent : baseEnd_4678887 < baseStart_4678887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678899 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 4]
def baseStart_4678899 : Nat := 118140960795 + 4678899 * 2 ^ 59
def prefixEnd_4678899 : Nat := 4983230072969 + 3 ^ 40 * 4678899 * 2
def baseEnd_4678899 : Nat := 2402524120841194519844641

theorem tailTrace_4678899 : CollatzResearch.WordTrace tailWord_4678899 prefixEnd_4678899 2402524120841194519844641 := by
  unfold tailWord_4678899
  simp only [CollatzResearch.WordTrace]
  refine ⟨170653466276155490175319751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113768977517436993450213167 170653466276155490175319751)
  ·
    refine ⟨255980199414233235262979627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170653466276155490175319751 255980199414233235262979627)
    ·
      refine ⟨383970299121349852894469441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255980199414233235262979627 383970299121349852894469441)
      ·
        refine ⟨287977724341012389670852081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383970299121349852894469441 287977724341012389670852081)
        ·
          refine ⟨215983293255759292253139061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287977724341012389670852081 215983293255759292253139061)
          ·
            refine ⟨20248433742727433648731787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215983293255759292253139061 20248433742727433648731787)
            ·
              refine ⟨30372650614091150473097681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20248433742727433648731787 30372650614091150473097681)
              ·
                refine ⟨22779487960568362854823261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30372650614091150473097681 22779487960568362854823261)
                ·
                  refine ⟨8542307985213136070558723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22779487960568362854823261 8542307985213136070558723)
                  ·
                    refine ⟨12813461977819704105838085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8542307985213136070558723 12813461977819704105838085)
                    ·
                      refine ⟨2402524120841194519844641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12813461977819704105838085 2402524120841194519844641)
                      ·
                        rfl

theorem cell23_4678899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_4678899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678899 prefixEnd_4678899 := by exact prefixLift 4678899
  have htrace : WordTrace (prefixWord ++ tailWord_4678899) baseStart_4678899 baseEnd_4678899 := by
    simpa [prefixWord, tailWord_4678899, baseEnd_4678899] using wordTrace_append hprefix tailTrace_4678899
  have hstable : (prefixWord ++ tailWord_4678899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678899).length < 2 ^ (prefixWord ++ tailWord_4678899).sum := by decide
  have hdescent : baseEnd_4678899 < baseStart_4678899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678909 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_4678909 : Nat := 118140960795 + 4678909 * 2 ^ 59
def prefixEnd_4678909 : Nat := 4983230072969 + 3 ^ 40 * 4678909 * 2
def baseEnd_4678909 : Nat := 800843085215913160239865

theorem tailTrace_4678909 : CollatzResearch.WordTrace tailWord_4678909 prefixEnd_4678909 800843085215913160239865 := by
  unfold tailWord_4678909
  simp only [CollatzResearch.WordTrace]
  refine ⟨170653831006119261883183781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113769220670746174588789187 170653831006119261883183781)
  ·
    refine ⟨31997593313647361603096959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170653831006119261883183781 31997593313647361603096959)
    ·
      refine ⟨47996389970471042404645439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31997593313647361603096959 47996389970471042404645439)
      ·
        refine ⟨71994584955706563606968159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47996389970471042404645439 71994584955706563606968159)
        ·
          refine ⟨107991877433559845410452239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71994584955706563606968159 107991877433559845410452239)
          ·
            refine ⟨161987816150339768115678359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107991877433559845410452239 161987816150339768115678359)
            ·
              refine ⟨242981724225509652173517539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161987816150339768115678359 242981724225509652173517539)
              ·
                refine ⟨364472586338264478260276309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242981724225509652173517539 364472586338264478260276309)
                ·
                  refine ⟨4271163121151536854612613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 364472586338264478260276309 4271163121151536854612613)
                  ·
                    refine ⟨800843085215913160239865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4271163121151536854612613 800843085215913160239865)
                    ·
                      rfl

theorem cell23_4678909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_4678909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678909 prefixEnd_4678909 := by exact prefixLift 4678909
  have htrace : WordTrace (prefixWord ++ tailWord_4678909) baseStart_4678909 baseEnd_4678909 := by
    simpa [prefixWord, tailWord_4678909, baseEnd_4678909] using wordTrace_append hprefix tailTrace_4678909
  have hstable : (prefixWord ++ tailWord_4678909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678909).length < 2 ^ (prefixWord ++ tailWord_4678909).sum := by decide
  have hdescent : baseEnd_4678909 < baseStart_4678909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678916 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4678916 : Nat := 118140960795 + 4678916 * 2 ^ 59
def prefixEnd_4678916 : Nat := 4983230072969 + 3 ^ 40 * 4678916 * 2
def baseEnd_4678916 : Nat := 2402532850012320953332063

theorem tailTrace_4678916 : CollatzResearch.WordTrace tailWord_4678916 prefixEnd_4678916 2402532850012320953332063 := by
  unfold tailWord_4678916
  simp only [CollatzResearch.WordTrace]
  refine ⟨85327043158546951039344301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113769390878062601385792401 85327043158546951039344301)
  ·
    refine ⟨31997641184455106639754113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85327043158546951039344301 31997641184455106639754113)
    ·
      refine ⟨23998230888341329979815585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31997641184455106639754113 23998230888341329979815585)
      ·
        refine ⟨17998673166255997484861689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23998230888341329979815585 17998673166255997484861689)
        ·
          refine ⟨13499004874691998113646267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17998673166255997484861689 13499004874691998113646267)
          ·
            refine ⟨20248507312037997170469401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13499004874691998113646267 20248507312037997170469401)
            ·
              refine ⟨15186380484028497877852051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20248507312037997170469401 15186380484028497877852051)
              ·
                refine ⟨22779570726042746816778077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15186380484028497877852051 22779570726042746816778077)
                ·
                  refine ⟨8542339022266030056291779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22779570726042746816778077 8542339022266030056291779)
                  ·
                    refine ⟨12813508533399045084437669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8542339022266030056291779 12813508533399045084437669)
                    ·
                      refine ⟨2402532850012320953332063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12813508533399045084437669 2402532850012320953332063)
                      ·
                        rfl

theorem cell23_4678916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4678916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678916 prefixEnd_4678916 := by exact prefixLift 4678916
  have htrace : WordTrace (prefixWord ++ tailWord_4678916) baseStart_4678916 baseEnd_4678916 := by
    simpa [prefixWord, tailWord_4678916, baseEnd_4678916] using wordTrace_append hprefix tailTrace_4678916
  have hstable : (prefixWord ++ tailWord_4678916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678916).length < 2 ^ (prefixWord ++ tailWord_4678916).sum := by decide
  have hdescent : baseEnd_4678916 < baseStart_4678916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678920 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_4678920 : Nat := 118140960795 + 4678920 * 2 ^ 59
def prefixEnd_4678920 : Nat := 4983230072969 + 3 ^ 40 * 4678920 * 2
def baseEnd_4678920 : Nat := 2402534903934938937682045

theorem tailTrace_4678920 : CollatzResearch.WordTrace tailWord_4678920 prefixEnd_4678920 2402534903934938937682045 := by
  unfold tailWord_4678920
  simp only [CollatzResearch.WordTrace]
  refine ⟨85327116104539705380917107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113769488139386273841222809 85327116104539705380917107)
  ·
    refine ⟨127990674156809558071375661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85327116104539705380917107 127990674156809558071375661)
    ·
      refine ⟨47996502808803584276765873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127990674156809558071375661 47996502808803584276765873)
      ·
        refine ⟨35997377106602688207574405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47996502808803584276765873 35997377106602688207574405)
        ·
          refine ⟨6749508207488004038920201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35997377106602688207574405 6749508207488004038920201)
          ·
            refine ⟨5062131155616003029190151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6749508207488004038920201 5062131155616003029190151)
            ·
              refine ⟨7593196733424004543785227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5062131155616003029190151 7593196733424004543785227)
              ·
                refine ⟨11389795100136006815677841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7593196733424004543785227 11389795100136006815677841)
                ·
                  refine ⟨8542346325102005111758381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11389795100136006815677841 8542346325102005111758381)
                  ·
                    refine ⟨3203379871913251916909393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8542346325102005111758381 3203379871913251916909393)
                    ·
                      refine ⟨2402534903934938937682045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3203379871913251916909393 2402534903934938937682045)
                      ·
                        rfl

theorem cell23_4678920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_4678920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678920 prefixEnd_4678920 := by exact prefixLift 4678920
  have htrace : WordTrace (prefixWord ++ tailWord_4678920) baseStart_4678920 baseEnd_4678920 := by
    simpa [prefixWord, tailWord_4678920, baseEnd_4678920] using wordTrace_append hprefix tailTrace_4678920
  have hstable : (prefixWord ++ tailWord_4678920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678920).length < 2 ^ (prefixWord ++ tailWord_4678920).sum := by decide
  have hdescent : baseEnd_4678920 < baseStart_4678920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678929 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_4678929 : Nat := 118140960795 + 4678929 * 2 ^ 59
def prefixEnd_4678929 : Nat := 4983230072969 + 3 ^ 40 * 4678929 * 2
def baseEnd_4678929 : Nat := 2402539525260829402469503

theorem tailTrace_4678929 : CollatzResearch.WordTrace tailWord_4678929 prefixEnd_4678929 2402539525260829402469503 := by
  unfold tailWord_4678929
  simp only [CollatzResearch.WordTrace]
  refine ⟨170654560466046805298911841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113769706977364536865941227 170654560466046805298911841)
  ·
    refine ⟨127990920349535103974183881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170654560466046805298911841 127990920349535103974183881)
    ·
      refine ⟨95993190262151327980637911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127990920349535103974183881 95993190262151327980637911)
      ·
        refine ⟨143989785393226991970956867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95993190262151327980637911 143989785393226991970956867)
        ·
          refine ⟨215984678089840487956435301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143989785393226991970956867 215984678089840487956435301)
          ·
            refine ⟨40497127141845091491831619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215984678089840487956435301 40497127141845091491831619)
            ·
              refine ⟨60745690712767637237747429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40497127141845091491831619 60745690712767637237747429)
              ·
                refine ⟨11389817008643931982077643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60745690712767637237747429 11389817008643931982077643)
                ·
                  refine ⟨17084725512965897973116465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11389817008643931982077643 17084725512965897973116465)
                  ·
                    refine ⟨12813544134724423479837349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17084725512965897973116465 12813544134724423479837349)
                    ·
                      refine ⟨2402539525260829402469503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12813544134724423479837349 2402539525260829402469503)
                      ·
                        rfl

theorem cell23_4678929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_4678929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678929 prefixEnd_4678929 := by exact prefixLift 4678929
  have htrace : WordTrace (prefixWord ++ tailWord_4678929) baseStart_4678929 baseEnd_4678929 := by
    simpa [prefixWord, tailWord_4678929, baseEnd_4678929] using wordTrace_append hprefix tailTrace_4678929
  have hstable : (prefixWord ++ tailWord_4678929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678929).length < 2 ^ (prefixWord ++ tailWord_4678929).sum := by decide
  have hdescent : baseEnd_4678929 < baseStart_4678929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678930 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4678930 : Nat := 118140960795 + 4678930 * 2 ^ 59
def prefixEnd_4678930 : Nat := 4983230072969 + 3 ^ 40 * 4678930 * 2
def baseEnd_4678930 : Nat := 800846679580494632852333

theorem tailTrace_4678930 : CollatzResearch.WordTrace tailWord_4678930 prefixEnd_4678930 800846679580494632852333 := by
  unfold tailWord_4678930
  simp only [CollatzResearch.WordTrace]
  refine ⟨42663649234760795617424561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113769731292695454979798829 42663649234760795617424561)
  ·
    refine ⟨31997736926070596713068421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42663649234760795617424561 31997736926070596713068421)
    ·
      refine ⟨5999575673638236883700329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31997736926070596713068421 5999575673638236883700329)
      ·
        refine ⟨4499681755228677662775247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5999575673638236883700329 4499681755228677662775247)
        ·
          refine ⟨6749522632843016494162871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499681755228677662775247 6749522632843016494162871)
          ·
            refine ⟨10124283949264524741244307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6749522632843016494162871 10124283949264524741244307)
            ·
              refine ⟨15186425923896787111866461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10124283949264524741244307 15186425923896787111866461)
              ·
                refine ⟨5694909721461295166949923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15186425923896787111866461 5694909721461295166949923)
                ·
                  refine ⟨8542364582191942750424885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694909721461295166949923 8542364582191942750424885)
                  ·
                    refine ⟨800846679580494632852333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8542364582191942750424885 800846679580494632852333)
                    ·
                      rfl

theorem cell23_4678930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4678930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678930 prefixEnd_4678930 := by exact prefixLift 4678930
  have htrace : WordTrace (prefixWord ++ tailWord_4678930) baseStart_4678930 baseEnd_4678930 := by
    simpa [prefixWord, tailWord_4678930, baseEnd_4678930] using wordTrace_append hprefix tailTrace_4678930
  have hstable : (prefixWord ++ tailWord_4678930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678930).length < 2 ^ (prefixWord ++ tailWord_4678930).sum := by decide
  have hdescent : baseEnd_4678930 < baseStart_4678930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678993 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 1, 3, 2]
def baseStart_4678993 : Nat := 118140960795 + 4678993 * 2 ^ 59
def prefixEnd_4678993 : Nat := 4983230072969 + 3 ^ 40 * 4678993 * 2
def baseEnd_4678993 : Nat := 2402572388022717152069209

theorem tailTrace_4678993 : CollatzResearch.WordTrace tailWord_4678993 prefixEnd_4678993 2402572388022717152069209 := by
  unfold tailWord_4678993
  simp only [CollatzResearch.WordTrace]
  refine ⟨170656894737814944229241633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113771263158543296152827755 170656894737814944229241633)
  ·
    refine ⟨127992671053361208171931225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170656894737814944229241633 127992671053361208171931225)
    ·
      refine ⟨95994503290020906128948419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127992671053361208171931225 95994503290020906128948419)
      ·
        refine ⟨143991754935031359193422629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95994503290020906128948419 143991754935031359193422629)
        ·
          refine ⟨26998454050318379848766743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143991754935031359193422629 26998454050318379848766743)
          ·
            refine ⟨40497681075477569773150115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26998454050318379848766743 40497681075477569773150115)
            ·
              refine ⟨60746521613216354659725173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40497681075477569773150115 60746521613216354659725173)
              ·
                refine ⟨5694986401239033249349235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60746521613216354659725173 5694986401239033249349235)
                ·
                  refine ⟨8542479601858549874023853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694986401239033249349235 8542479601858549874023853)
                  ·
                    refine ⟨3203429850696956202758945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8542479601858549874023853 3203429850696956202758945)
                    ·
                      refine ⟨2402572388022717152069209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3203429850696956202758945 2402572388022717152069209)
                      ·
                        rfl

theorem cell23_4678993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_4678993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678993 prefixEnd_4678993 := by exact prefixLift 4678993
  have htrace : WordTrace (prefixWord ++ tailWord_4678993) baseStart_4678993 baseEnd_4678993 := by
    simpa [prefixWord, tailWord_4678993, baseEnd_4678993] using wordTrace_append hprefix tailTrace_4678993
  have hstable : (prefixWord ++ tailWord_4678993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678993).length < 2 ^ (prefixWord ++ tailWord_4678993).sum := by decide
  have hdescent : baseEnd_4678993 < baseStart_4678993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679070 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4679070 : Nat := 118140960795 + 4679070 * 2 ^ 59
def prefixEnd_4679070 : Nat := 4983230072969 + 3 ^ 40 * 4679070 * 2
def baseEnd_4679070 : Nat := 2402611926033113350806355

theorem tailTrace_4679070 : CollatzResearch.WordTrace tailWord_4679070 prefixEnd_4679070 2402611926033113350806355 := by
  unfold tailWord_4679070
  simp only [CollatzResearch.WordTrace]
  refine ⟨21332462894816998297474333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113773135439023990919863109 21332462894816998297474333)
  ·
    refine ⟨7999673585556374361552875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21332462894816998297474333 7999673585556374361552875)
    ·
      refine ⟨11999510378334561542329313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7999673585556374361552875 11999510378334561542329313)
      ·
        refine ⟨8999632783750921156746985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11999510378334561542329313 8999632783750921156746985)
        ·
          refine ⟨6749724587813190867560239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8999632783750921156746985 6749724587813190867560239)
          ·
            refine ⟨10124586881719786301340359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6749724587813190867560239 10124586881719786301340359)
            ·
              refine ⟨15186880322579679452010539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10124586881719786301340359 15186880322579679452010539)
              ·
                refine ⟨22780320483869519178015809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15186880322579679452010539 22780320483869519178015809)
                ·
                  refine ⟨17085240362902139383511857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22780320483869519178015809 17085240362902139383511857)
                  ·
                    refine ⟨12813930272176604537633893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17085240362902139383511857 12813930272176604537633893)
                    ·
                      refine ⟨2402611926033113350806355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12813930272176604537633893 2402611926033113350806355)
                      ·
                        rfl

theorem cell23_4679070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4679070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679070 prefixEnd_4679070 := by exact prefixLift 4679070
  have htrace : WordTrace (prefixWord ++ tailWord_4679070) baseStart_4679070 baseEnd_4679070 := by
    simpa [prefixWord, tailWord_4679070, baseEnd_4679070] using wordTrace_append hprefix tailTrace_4679070
  have hstable : (prefixWord ++ tailWord_4679070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679070).length < 2 ^ (prefixWord ++ tailWord_4679070).sum := by decide
  have hdescent : baseEnd_4679070 < baseStart_4679070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679093 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_4679093 : Nat := 118140960795 + 4679093 * 2 ^ 59
def prefixEnd_4679093 : Nat := 4983230072969 + 3 ^ 40 * 4679093 * 2
def baseEnd_4679093 : Nat := 800874578696055586939583

theorem tailTrace_4679093 : CollatzResearch.WordTrace tailWord_4679093 prefixEnd_4679093 800874578696055586939583 := by
  unfold tailWord_4679093
  simp only [CollatzResearch.WordTrace]
  refine ⟨170660542037452661307881933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113773694691635107538587955 170660542037452661307881933)
  ·
    refine ⟨63997703264044747990455725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170660542037452661307881933 63997703264044747990455725)
    ·
      refine ⟨23999138724016780496420897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63997703264044747990455725 23999138724016780496420897)
      ·
        refine ⟨17999354043012585372315673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23999138724016780496420897 17999354043012585372315673)
        ·
          refine ⟨13499515532259439029236755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17999354043012585372315673 13499515532259439029236755)
          ·
            refine ⟨20249273298389158543855133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13499515532259439029236755 20249273298389158543855133)
            ·
              refine ⟨7593477486895934453945675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20249273298389158543855133 7593477486895934453945675)
              ·
                refine ⟨11390216230343901680918513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7593477486895934453945675 11390216230343901680918513)
                ·
                  refine ⟨8542662172757926260688885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11390216230343901680918513 8542662172757926260688885)
                  ·
                    refine ⟨800874578696055586939583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8542662172757926260688885 800874578696055586939583)
                    ·
                      rfl

theorem cell23_4679093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_4679093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679093 prefixEnd_4679093 := by exact prefixLift 4679093
  have htrace : WordTrace (prefixWord ++ tailWord_4679093) baseStart_4679093 baseEnd_4679093 := by
    simpa [prefixWord, tailWord_4679093, baseEnd_4679093] using wordTrace_append hprefix tailTrace_4679093
  have hstable : (prefixWord ++ tailWord_4679093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679093).length < 2 ^ (prefixWord ++ tailWord_4679093).sum := by decide
  have hdescent : baseEnd_4679093 < baseStart_4679093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679133 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4679133 : Nat := 118140960795 + 4679133 * 2 ^ 59
def prefixEnd_4679133 : Nat := 4983230072969 + 3 ^ 40 * 4679133 * 2
def baseEnd_4679133 : Nat := 2402644275314346604318565

theorem tailTrace_4679133 : CollatzResearch.WordTrace tailWord_4679133 prefixEnd_4679133 2402644275314346604318565 := by
  unfold tailWord_4679133
  simp only [CollatzResearch.WordTrace]
  refine ⟨170662000957307748139338053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113774667304871832092892035 170662000957307748139338053)
  ·
    refine ⟨31999125179495202776125885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170662000957307748139338053 31999125179495202776125885)
    ·
      refine ⟨11999671942310701041047207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31999125179495202776125885 11999671942310701041047207)
      ·
        refine ⟨17999507913466051561570811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11999671942310701041047207 17999507913466051561570811)
        ·
          refine ⟨26999261870199077342356217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17999507913466051561570811 26999261870199077342356217)
          ·
            refine ⟨20249446402649308006767163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26999261870199077342356217 20249446402649308006767163)
            ·
              refine ⟨30374169603973962010150745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20249446402649308006767163 30374169603973962010150745)
              ·
                refine ⟨22780627202980471507613059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30374169603973962010150745 22780627202980471507613059)
                ·
                  refine ⟨34170940804470707261419589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22780627202980471507613059 34170940804470707261419589)
                  ·
                    refine ⟨6407051400838257611516173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34170940804470707261419589 6407051400838257611516173)
                    ·
                      refine ⟨2402644275314346604318565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407051400838257611516173 2402644275314346604318565)
                      ·
                        rfl

theorem cell23_4679133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4679133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679133 prefixEnd_4679133 := by exact prefixLift 4679133
  have htrace : WordTrace (prefixWord ++ tailWord_4679133) baseStart_4679133 baseEnd_4679133 := by
    simpa [prefixWord, tailWord_4679133, baseEnd_4679133] using wordTrace_append hprefix tailTrace_4679133
  have hstable : (prefixWord ++ tailWord_4679133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679133).length < 2 ^ (prefixWord ++ tailWord_4679133).sum := by decide
  have hdescent : baseEnd_4679133 < baseStart_4679133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679200 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 1, 5]
def baseStart_4679200 : Nat := 118140960795 + 4679200 * 2 ^ 59
def prefixEnd_4679200 : Nat := 4983230072969 + 3 ^ 40 * 4679200 * 2
def baseEnd_4679200 : Nat := 800892892839399280726919

theorem tailTrace_4679200 : CollatzResearch.WordTrace tailWord_4679200 prefixEnd_4679200 800892892839399280726919 := by
  unfold tailWord_4679200
  simp only [CollatzResearch.WordTrace]
  refine ⟨85332222324032509291013527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113776296432043345721351369 85332222324032509291013527)
  ·
    refine ⟨127998333486048763936520291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85332222324032509291013527 127998333486048763936520291)
    ·
      refine ⟨191997500229073145904780437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127998333486048763936520291 191997500229073145904780437)
      ·
        refine ⟨8999882823237803714286583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 191997500229073145904780437 8999882823237803714286583)
        ·
          refine ⟨13499824234856705571429875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8999882823237803714286583 13499824234856705571429875)
          ·
            refine ⟨20249736352285058357144813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13499824234856705571429875 20249736352285058357144813)
            ·
              refine ⟨7593651132106896883929305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20249736352285058357144813 7593651132106896883929305)
              ·
                refine ⟨5695238349080172662946979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7593651132106896883929305 5695238349080172662946979)
                ·
                  refine ⟨8542857523620258994420469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5695238349080172662946979 8542857523620258994420469)
                  ·
                    refine ⟨800892892839399280726919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8542857523620258994420469 800892892839399280726919)
                    ·
                      rfl

theorem cell23_4679200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_4679200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679200 prefixEnd_4679200 := by exact prefixLift 4679200
  have htrace : WordTrace (prefixWord ++ tailWord_4679200) baseStart_4679200 baseEnd_4679200 := by
    simpa [prefixWord, tailWord_4679200, baseEnd_4679200] using wordTrace_append hprefix tailTrace_4679200
  have hstable : (prefixWord ++ tailWord_4679200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679200).length < 2 ^ (prefixWord ++ tailWord_4679200).sum := by decide
  have hdescent : baseEnd_4679200 < baseStart_4679200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679223 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_4679223 : Nat := 118140960795 + 4679223 * 2 ^ 59
def prefixEnd_4679223 : Nat := 4983230072969 + 3 ^ 40 * 4679223 * 2
def baseEnd_4679223 : Nat := 2402690488573251252193151

theorem tailTrace_4679223 : CollatzResearch.WordTrace tailWord_4679223 prefixEnd_4679223 2402690488573251252193151 := by
  unfold tailWord_4679223
  simp only [CollatzResearch.WordTrace]
  refine ⟨170665283526981693510114323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113776855684654462340076215 170665283526981693510114323)
  ·
    refine ⟨255997925290472540265171485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170665283526981693510114323 255997925290472540265171485)
    ·
      refine ⟨95999221983927202599439307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255997925290472540265171485 95999221983927202599439307)
      ·
        refine ⟨143998832975890803899158961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95999221983927202599439307 143998832975890803899158961)
        ·
          refine ⟨107999124731918102924369221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143998832975890803899158961 107999124731918102924369221)
          ·
            refine ⟨20249835887234644298319229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107999124731918102924369221 20249835887234644298319229)
            ·
              refine ⟨7593688457712991611869711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20249835887234644298319229 7593688457712991611869711)
              ·
                refine ⟨11390532686569487417804567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7593688457712991611869711 11390532686569487417804567)
                ·
                  refine ⟨17085799029854231126706851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11390532686569487417804567 17085799029854231126706851)
                  ·
                    refine ⟨25628698544781346690060277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17085799029854231126706851 25628698544781346690060277)
                    ·
                      refine ⟨2402690488573251252193151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25628698544781346690060277 2402690488573251252193151)
                      ·
                        rfl

theorem cell23_4679223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_4679223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679223 prefixEnd_4679223 := by exact prefixLift 4679223
  have htrace : WordTrace (prefixWord ++ tailWord_4679223) baseStart_4679223 baseEnd_4679223 := by
    simpa [prefixWord, tailWord_4679223, baseEnd_4679223] using wordTrace_append hprefix tailTrace_4679223
  have hstable : (prefixWord ++ tailWord_4679223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679223).length < 2 ^ (prefixWord ++ tailWord_4679223).sum := by decide
  have hdescent : baseEnd_4679223 < baseStart_4679223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679233 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4679233 : Nat := 118140960795 + 4679233 * 2 ^ 59
def prefixEnd_4679233 : Nat := 4983230072969 + 3 ^ 40 * 4679233 * 2
def baseEnd_4679233 : Nat := 2402695623379796213068105

theorem tailTrace_4679233 : CollatzResearch.WordTrace tailWord_4679233 prefixEnd_4679233 2402695623379796213068105 := by
  unfold tailWord_4679233
  simp only [CollatzResearch.WordTrace]
  refine ⟨170665648256945465217978353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113777098837963643478652235 170665648256945465217978353)
  ·
    refine ⟨127999236192709098913483765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170665648256945465217978353 127999236192709098913483765)
    ·
      refine ⟨11999928393066478023139103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127999236192709098913483765 11999928393066478023139103)
      ·
        refine ⟨17999892589599717034708655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11999928393066478023139103 17999892589599717034708655)
        ·
          refine ⟨26999838884399575552062983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17999892589599717034708655 26999838884399575552062983)
          ·
            refine ⟨40499758326599363328094475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26999838884399575552062983 40499758326599363328094475)
            ·
              refine ⟨60749637489899044992141713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40499758326599363328094475 60749637489899044992141713)
              ·
                refine ⟨45562228117424283744106285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60749637489899044992141713 45562228117424283744106285)
                ·
                  refine ⟨17085835544034106404039857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45562228117424283744106285 17085835544034106404039857)
                  ·
                    refine ⟨12814376658025579803029893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17085835544034106404039857 12814376658025579803029893)
                    ·
                      refine ⟨2402695623379796213068105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12814376658025579803029893 2402695623379796213068105)
                      ·
                        rfl

theorem cell23_4679233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4679233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679233 prefixEnd_4679233 := by exact prefixLift 4679233
  have htrace : WordTrace (prefixWord ++ tailWord_4679233) baseStart_4679233 baseEnd_4679233 := by
    simpa [prefixWord, tailWord_4679233, baseEnd_4679233] using wordTrace_append hprefix tailTrace_4679233
  have hstable : (prefixWord ++ tailWord_4679233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679233).length < 2 ^ (prefixWord ++ tailWord_4679233).sum := by decide
  have hdescent : baseEnd_4679233 < baseStart_4679233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679250 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_4679250 : Nat := 118140960795 + 4679250 * 2 ^ 59
def prefixEnd_4679250 : Nat := 4983230072969 + 3 ^ 40 * 4679250 * 2
def baseEnd_4679250 : Nat := 2402704352550922646555527

theorem tailTrace_4679250 : CollatzResearch.WordTrace tailWord_4679250 prefixEnd_4679250 2402704352550922646555527 := by
  unfold tailWord_4679250
  simp only [CollatzResearch.WordTrace]
  refine ⟨42666567074470969280336801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113777512198589251414231469 42666567074470969280336801)
  ·
    refine ⟨31999925305853226960252601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42666567074470969280336801 31999925305853226960252601)
    ·
      refine ⟨23999943979389920220189451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31999925305853226960252601 23999943979389920220189451)
      ·
        refine ⟨35999915969084880330284177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23999943979389920220189451 35999915969084880330284177)
        ·
          refine ⟨26999936976813660247713133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35999915969084880330284177 26999936976813660247713133)
          ·
            refine ⟨10124976366305122592892425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26999936976813660247713133 10124976366305122592892425)
            ·
              refine ⟨7593732274728841944669319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10124976366305122592892425 7593732274728841944669319)
              ·
                refine ⟨11390598412093262917003979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7593732274728841944669319 11390598412093262917003979)
                ·
                  refine ⟨17085897618139894375505969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11390598412093262917003979 17085897618139894375505969)
                  ·
                    refine ⟨12814423213604920781629477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17085897618139894375505969 12814423213604920781629477)
                    ·
                      refine ⟨2402704352550922646555527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12814423213604920781629477 2402704352550922646555527)
                      ·
                        rfl

theorem cell23_4679250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_4679250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679250 prefixEnd_4679250 := by exact prefixLift 4679250
  have htrace : WordTrace (prefixWord ++ tailWord_4679250) baseStart_4679250 baseEnd_4679250 := by
    simpa [prefixWord, tailWord_4679250, baseEnd_4679250] using wordTrace_append hprefix tailTrace_4679250
  have hstable : (prefixWord ++ tailWord_4679250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679250).length < 2 ^ (prefixWord ++ tailWord_4679250).sum := by decide
  have hdescent : baseEnd_4679250 < baseStart_4679250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679256 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 4, 7]
def baseStart_4679256 : Nat := 118140960795 + 4679256 * 2 ^ 59
def prefixEnd_4679256 : Nat := 4983230072969 + 3 ^ 40 * 4679256 * 2
def baseEnd_4679256 : Nat := 800902477811616541026833

theorem tailTrace_4679256 : CollatzResearch.WordTrace tailWord_4679256 prefixEnd_4679256 800902477811616541026833 := by
  unfold tailWord_4679256
  simp only [CollatzResearch.WordTrace]
  refine ⟨85333243567931070073032811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113777658090574760097377081 85333243567931070073032811)
  ·
    refine ⟨127999865351896605109549217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85333243567931070073032811 127999865351896605109549217)
    ·
      refine ⟨95999899013922453832161913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127999865351896605109549217 95999899013922453832161913)
      ·
        refine ⟨71999924260441840374121435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95999899013922453832161913 71999924260441840374121435)
        ·
          refine ⟨107999886390662760561182153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71999924260441840374121435 107999886390662760561182153)
          ·
            refine ⟨80999914792997070420886615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107999886390662760561182153 80999914792997070420886615)
            ·
              refine ⟨121499872189495605631329923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80999914792997070420886615 121499872189495605631329923)
              ·
                refine ⟨182249808284243408446994885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121499872189495605631329923 182249808284243408446994885)
                ·
                  refine ⟨34171839053295639083811541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182249808284243408446994885 34171839053295639083811541)
                  ·
                    refine ⟨800902477811616541026833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34171839053295639083811541 800902477811616541026833)
                    ·
                      rfl

theorem cell23_4679256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_4679256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679256 prefixEnd_4679256 := by exact prefixLift 4679256
  have htrace : WordTrace (prefixWord ++ tailWord_4679256) baseStart_4679256 baseEnd_4679256 := by
    simpa [prefixWord, tailWord_4679256, baseEnd_4679256] using wordTrace_append hprefix tailTrace_4679256
  have hstable : (prefixWord ++ tailWord_4679256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679256).length < 2 ^ (prefixWord ++ tailWord_4679256).sum := by decide
  have hdescent : baseEnd_4679256 < baseStart_4679256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679260 : List Nat := [2, 2, 4, 1, 2, 2, 3, 7]
def baseStart_4679260 : Nat := 118140960795 + 4679260 * 2 ^ 59
def prefixEnd_4679260 : Nat := 4983230072969 + 3 ^ 40 * 4679260 * 2
def baseEnd_4679260 : Nat := 88989240272498800275203

theorem tailTrace_4679260 : CollatzResearch.WordTrace tailWord_4679260 prefixEnd_4679260 88989240272498800275203 := by
  unfold tailWord_4679260
  simp only [CollatzResearch.WordTrace]
  refine ⟨85333316513923824414605617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113777755351898432552807489 85333316513923824414605617)
  ·
    refine ⟨63999987385442868310954213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85333316513923824414605617 63999987385442868310954213)
    ·
      refine ⟨11999997634770537808303915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63999987385442868310954213 11999997634770537808303915)
      ·
        refine ⟨17999996452155806712455873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11999997634770537808303915 17999996452155806712455873)
        ·
          refine ⟨13499997339116855034341905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17999996452155806712455873 13499997339116855034341905)
          ·
            refine ⟨10124998004337641275756429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13499997339116855034341905 10124998004337641275756429)
            ·
              refine ⟨3796874251626615478408661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10124998004337641275756429 3796874251626615478408661)
              ·
                refine ⟨88989240272498800275203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3796874251626615478408661 88989240272498800275203)
                ·
                  rfl

theorem cell23_4679260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 7].length) (baseStart_4679260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679260 prefixEnd_4679260 := by exact prefixLift 4679260
  have htrace : WordTrace (prefixWord ++ tailWord_4679260) baseStart_4679260 baseEnd_4679260 := by
    simpa [prefixWord, tailWord_4679260, baseEnd_4679260] using wordTrace_append hprefix tailTrace_4679260
  have hstable : (prefixWord ++ tailWord_4679260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679260).length < 2 ^ (prefixWord ++ tailWord_4679260).sum := by decide
  have hdescent : baseEnd_4679260 < baseStart_4679260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679274 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_4679274 : Nat := 118140960795 + 4679274 * 2 ^ 59
def prefixEnd_4679274 : Nat := 4983230072969 + 3 ^ 40 * 4679274 * 2
def baseEnd_4679274 : Nat := 2402716676086630552655417

theorem tailTrace_4679274 : CollatzResearch.WordTrace tailWord_4679274 prefixEnd_4679274 2402716676086630552655417 := by
  unfold tailWord_4679274
  simp only [CollatzResearch.WordTrace]
  refine ⟨42666785912449232305055219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113778095766531286146813917 42666785912449232305055219)
  ·
    refine ⟨64000178868673848457582829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42666785912449232305055219 64000178868673848457582829)
    ·
      refine ⟨24000067075752693171593561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64000178868673848457582829 24000067075752693171593561)
      ·
        refine ⟨18000050306814519878695171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24000067075752693171593561 18000050306814519878695171)
        ·
          refine ⟨27000075460221779818042757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18000050306814519878695171 27000075460221779818042757)
          ·
            refine ⟨5062514148791583715883017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27000075460221779818042757 5062514148791583715883017)
            ·
              refine ⟨3796885611593687786912263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5062514148791583715883017 3796885611593687786912263)
              ·
                refine ⟨5695328417390531680368395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796885611593687786912263 5695328417390531680368395)
                ·
                  refine ⟨8542992626085797520552593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5695328417390531680368395 8542992626085797520552593)
                  ·
                    refine ⟨6407244469564348140414445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8542992626085797520552593 6407244469564348140414445)
                    ·
                      refine ⟨2402716676086630552655417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407244469564348140414445 2402716676086630552655417)
                      ·
                        rfl

theorem cell23_4679274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_4679274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679274 prefixEnd_4679274 := by exact prefixLift 4679274
  have htrace : WordTrace (prefixWord ++ tailWord_4679274) baseStart_4679274 baseEnd_4679274 := by
    simpa [prefixWord, tailWord_4679274, baseEnd_4679274] using wordTrace_append hprefix tailTrace_4679274
  have hstable : (prefixWord ++ tailWord_4679274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679274).length < 2 ^ (prefixWord ++ tailWord_4679274).sum := by decide
  have hdescent : baseEnd_4679274 < baseStart_4679274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679303 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 2, 6]
def baseStart_4679303 : Nat := 118140960795 + 4679303 * 2 ^ 59
def prefixEnd_4679303 : Nat := 4983230072969 + 3 ^ 40 * 4679303 * 2
def baseEnd_4679303 : Nat := 800910522341870313064261

theorem tailTrace_4679303 : CollatzResearch.WordTrace tailWord_4679303 prefixEnd_4679303 800910522341870313064261 := by
  unfold tailWord_4679303
  simp only [CollatzResearch.WordTrace]
  refine ⟨170668201366691867173026563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113778800911127911448684375 170668201366691867173026563)
  ·
    refine ⟨256002302050037800759539845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170668201366691867173026563 256002302050037800759539845)
    ·
      refine ⟨48000431634382087642413721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256002302050037800759539845 48000431634382087642413721)
      ·
        refine ⟨36000323725786565731810291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48000431634382087642413721 36000323725786565731810291)
        ·
          refine ⟨54000485588679848597715437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36000323725786565731810291 54000485588679848597715437)
          ·
            refine ⟨20250182095754943224143289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54000485588679848597715437 20250182095754943224143289)
            ·
              refine ⟨15187636571816207418107467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20250182095754943224143289 15187636571816207418107467)
              ·
                refine ⟨22781454857724311127161201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15187636571816207418107467 22781454857724311127161201)
                ·
                  refine ⟨17086091143293233345370901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22781454857724311127161201 17086091143293233345370901)
                  ·
                    refine ⟨800910522341870313064261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17086091143293233345370901 800910522341870313064261)
                    ·
                      rfl

theorem cell23_4679303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_4679303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679303 prefixEnd_4679303 := by exact prefixLift 4679303
  have htrace : WordTrace (prefixWord ++ tailWord_4679303) baseStart_4679303 baseEnd_4679303 := by
    simpa [prefixWord, tailWord_4679303, baseEnd_4679303] using wordTrace_append hprefix tailTrace_4679303
  have hstable : (prefixWord ++ tailWord_4679303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679303).length < 2 ^ (prefixWord ++ tailWord_4679303).sum := by decide
  have hdescent : baseEnd_4679303 < baseStart_4679303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679304 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4679304 : Nat := 118140960795 + 4679304 * 2 ^ 59
def prefixEnd_4679304 : Nat := 4983230072969 + 3 ^ 40 * 4679304 * 2
def baseEnd_4679304 : Nat := 2402732080506265435280279

theorem tailTrace_4679304 : CollatzResearch.WordTrace tailWord_4679304 prefixEnd_4679304 2402732080506265435280279 := by
  unfold tailWord_4679304
  simp only [CollatzResearch.WordTrace]
  refine ⟨85334118919844122171906483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113778825226458829562541977 85334118919844122171906483)
  ·
    refine ⟨128001178379766183257859725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85334118919844122171906483 128001178379766183257859725)
    ·
      refine ⟨48000441892412318721697397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128001178379766183257859725 48000441892412318721697397)
      ·
        refine ⟨4500041427413654880159131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48000441892412318721697397 4500041427413654880159131)
        ·
          refine ⟨6750062141120482320238697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500041427413654880159131 6750062141120482320238697)
          ·
            refine ⟨5062546605840361740179023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6750062141120482320238697 5062546605840361740179023)
            ·
              refine ⟨7593819908760542610268535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5062546605840361740179023 7593819908760542610268535)
              ·
                refine ⟨11390729863140813915402803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7593819908760542610268535 11390729863140813915402803)
                ·
                  refine ⟨17086094794711220873104205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11390729863140813915402803 17086094794711220873104205)
                  ·
                    refine ⟨6407285548016707827414077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17086094794711220873104205 6407285548016707827414077)
                    ·
                      refine ⟨2402732080506265435280279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407285548016707827414077 2402732080506265435280279)
                      ·
                        rfl

theorem cell23_4679304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4679304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679304 prefixEnd_4679304 := by exact prefixLift 4679304
  have htrace : WordTrace (prefixWord ++ tailWord_4679304) baseStart_4679304 baseEnd_4679304 := by
    simpa [prefixWord, tailWord_4679304, baseEnd_4679304] using wordTrace_append hprefix tailTrace_4679304
  have hstable : (prefixWord ++ tailWord_4679304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679304).length < 2 ^ (prefixWord ++ tailWord_4679304).sum := by decide
  have hdescent : baseEnd_4679304 < baseStart_4679304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679420 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_4679420 : Nat := 118140960795 + 4679420 * 2 ^ 59
def prefixEnd_4679420 : Nat := 4983230072969 + 3 ^ 40 * 4679420 * 2
def baseEnd_4679420 : Nat := 2402791644262186981429745

theorem tailTrace_4679420 : CollatzResearch.WordTrace tailWord_4679420 prefixEnd_4679420 2402791644262186981429745 := by
  unfold tailWord_4679420
  simp only [CollatzResearch.WordTrace]
  refine ⟨85336234353633998077517857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113781645804845330770023809 85336234353633998077517857)
  ·
    refine ⟨64002175765225498558138393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85336234353633998077517857 64002175765225498558138393)
    ·
      refine ⟨48001631823919123918603795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64002175765225498558138393 48001631823919123918603795)
      ·
        refine ⟨72002447735878685877905693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48001631823919123918603795 72002447735878685877905693)
        ·
          refine ⟨27000917900954507204214635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72002447735878685877905693 27000917900954507204214635)
          ·
            refine ⟨40501376851431760806321953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27000917900954507204214635 40501376851431760806321953)
            ·
              refine ⟨30376032638573820604741465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40501376851431760806321953 30376032638573820604741465)
              ·
                refine ⟨22782024478930365453556099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30376032638573820604741465 22782024478930365453556099)
                ·
                  refine ⟨34173036718395548180334149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22782024478930365453556099 34173036718395548180334149)
                  ·
                    refine ⟨6407444384699165283812653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34173036718395548180334149 6407444384699165283812653)
                    ·
                      refine ⟨2402791644262186981429745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407444384699165283812653 2402791644262186981429745)
                      ·
                        rfl

theorem cell23_4679420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_4679420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679420 prefixEnd_4679420 := by exact prefixLift 4679420
  have htrace : WordTrace (prefixWord ++ tailWord_4679420) baseStart_4679420 baseEnd_4679420 := by
    simpa [prefixWord, tailWord_4679420, baseEnd_4679420] using wordTrace_append hprefix tailTrace_4679420
  have hstable : (prefixWord ++ tailWord_4679420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679420).length < 2 ^ (prefixWord ++ tailWord_4679420).sum := by decide
  have hdescent : baseEnd_4679420 < baseStart_4679420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679457 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 6]
def baseStart_4679457 : Nat := 118140960795 + 4679457 * 2 ^ 59
def prefixEnd_4679457 : Nat := 4983230072969 + 3 ^ 40 * 4679457 * 2
def baseEnd_4679457 : Nat := 266978960338489259629675

theorem tailTrace_4679457 : CollatzResearch.WordTrace tailWord_4679457 prefixEnd_4679457 266978960338489259629675 := by
  unfold tailWord_4679457
  simp only [CollatzResearch.WordTrace]
  refine ⟨170673818208133951474132625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113782545472089300982755083 170673818208133951474132625)
  ·
    refine ⟨128005363656100463605599469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170673818208133951474132625 128005363656100463605599469)
    ·
      refine ⟨48002011371037673852099801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128005363656100463605599469 48002011371037673852099801)
      ·
        refine ⟨36001508528278255389074851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48002011371037673852099801 36001508528278255389074851)
        ·
          refine ⟨54002262792417383083612277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36001508528278255389074851 54002262792417383083612277)
          ·
            refine ⟨5062712136789129664088651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54002262792417383083612277 5062712136789129664088651)
            ·
              refine ⟨7594068205183694496132977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5062712136789129664088651 7594068205183694496132977)
              ·
                refine ⟨5695551153887770872099733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7594068205183694496132977 5695551153887770872099733)
                ·
                  refine ⟨266978960338489259629675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5695551153887770872099733 266978960338489259629675)
                  ·
                    rfl

theorem cell23_4679457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 6].length) (baseStart_4679457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679457 prefixEnd_4679457 := by exact prefixLift 4679457
  have htrace : WordTrace (prefixWord ++ tailWord_4679457) baseStart_4679457 baseEnd_4679457 := by
    simpa [prefixWord, tailWord_4679457, baseEnd_4679457] using wordTrace_append hprefix tailTrace_4679457
  have hstable : (prefixWord ++ tailWord_4679457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679457).length < 2 ^ (prefixWord ++ tailWord_4679457).sum := by decide
  have hdescent : baseEnd_4679457 < baseStart_4679457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679460 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4679460 : Nat := 118140960795 + 4679460 * 2 ^ 59
def prefixEnd_4679460 : Nat := 4983230072969 + 3 ^ 40 * 4679460 * 2
def baseEnd_4679460 : Nat := 2402812183488366824929561

theorem tailTrace_4679460 : CollatzResearch.WordTrace tailWord_4679460 prefixEnd_4679460 2402812183488366824929561 := by
  unfold tailWord_4679460
  simp only [CollatzResearch.WordTrace]
  refine ⟨85336963813561541493245917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113782618418082055324327889 85336963813561541493245917)
  ·
    refine ⟨32001361430085578059967219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85336963813561541493245917 32001361430085578059967219)
    ·
      refine ⟨48002042145128367089950829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32001361430085578059967219 48002042145128367089950829)
      ·
        refine ⟨18000765804423137658731561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48002042145128367089950829 18000765804423137658731561)
        ·
          refine ⟨13500574353317353244048671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18000765804423137658731561 13500574353317353244048671)
          ·
            refine ⟨20250861529976029866073007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13500574353317353244048671 20250861529976029866073007)
            ·
              refine ⟨30376292294964044799109511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20250861529976029866073007 30376292294964044799109511)
              ·
                refine ⟨45564438442446067198664267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30376292294964044799109511 45564438442446067198664267)
                ·
                  refine ⟨68346657663669100797996401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45564438442446067198664267 68346657663669100797996401)
                  ·
                    refine ⟨51259993247751825598497301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68346657663669100797996401 51259993247751825598497301)
                    ·
                      refine ⟨2402812183488366824929561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51259993247751825598497301 2402812183488366824929561)
                      ·
                        rfl

theorem cell23_4679460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4679460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679460 prefixEnd_4679460 := by exact prefixLift 4679460
  have htrace : WordTrace (prefixWord ++ tailWord_4679460) baseStart_4679460 baseEnd_4679460 := by
    simpa [prefixWord, tailWord_4679460, baseEnd_4679460] using wordTrace_append hprefix tailTrace_4679460
  have hstable : (prefixWord ++ tailWord_4679460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679460).length < 2 ^ (prefixWord ++ tailWord_4679460).sum := by decide
  have hdescent : baseEnd_4679460 < baseStart_4679460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679520 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_4679520 : Nat := 118140960795 + 4679520 * 2 ^ 59
def prefixEnd_4679520 : Nat := 4983230072969 + 3 ^ 40 * 4679520 * 2
def baseEnd_4679520 : Nat := 2402842992327636590179285

theorem tailTrace_4679520 : CollatzResearch.WordTrace tailWord_4679520 prefixEnd_4679520 2402842992327636590179285 := by
  unfold tailWord_4679520
  simp only [CollatzResearch.WordTrace]
  refine ⟨85338058003452856616838007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113784077337937142155784009 85338058003452856616838007)
  ·
    refine ⟨128007087005179284925257011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85338058003452856616838007 128007087005179284925257011)
    ·
      refine ⟨192010630507768927387885517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128007087005179284925257011 192010630507768927387885517)
      ·
        refine ⟨72003986440413347770457069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192010630507768927387885517 72003986440413347770457069)
        ·
          refine ⟨27001494915155005413921401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72003986440413347770457069 27001494915155005413921401)
          ·
            refine ⟨20251121186366254060441051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27001494915155005413921401 20251121186366254060441051)
            ·
              refine ⟨30376681779549381090661577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20251121186366254060441051 30376681779549381090661577)
              ·
                refine ⟨22782511334662035817996183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30376681779549381090661577 22782511334662035817996183)
                ·
                  refine ⟨34173767001993053726994275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22782511334662035817996183 34173767001993053726994275)
                  ·
                    refine ⟨51260650502989580590491413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34173767001993053726994275 51260650502989580590491413)
                    ·
                      refine ⟨2402842992327636590179285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51260650502989580590491413 2402842992327636590179285)
                      ·
                        rfl

theorem cell23_4679520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_4679520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679520 prefixEnd_4679520 := by exact prefixLift 4679520
  have htrace : WordTrace (prefixWord ++ tailWord_4679520) baseStart_4679520 baseEnd_4679520 := by
    simpa [prefixWord, tailWord_4679520, baseEnd_4679520] using wordTrace_append hprefix tailTrace_4679520
  have hstable : (prefixWord ++ tailWord_4679520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679520).length < 2 ^ (prefixWord ++ tailWord_4679520).sum := by decide
  have hdescent : baseEnd_4679520 < baseStart_4679520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679527 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_4679527 : Nat := 118140960795 + 4679527 * 2 ^ 59
def prefixEnd_4679527 : Nat := 4983230072969 + 3 ^ 40 * 4679527 * 2
def baseEnd_4679527 : Nat := 2402846586692218062791753

theorem tailTrace_4679527 : CollatzResearch.WordTrace tailWord_4679527 prefixEnd_4679527 2402846586692218062791753 := by
  unfold tailWord_4679527
  simp only [CollatzResearch.WordTrace]
  refine ⟨170676371317880353429180835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113784247545253568952787223 170676371317880353429180835)
  ·
    refine ⟨256014556976820530143771253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170676371317880353429180835 256014556976820530143771253)
    ·
      refine ⟨24001364716576924700978555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256014556976820530143771253 24001364716576924700978555)
      ·
        refine ⟨36002047074865387051467833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24001364716576924700978555 36002047074865387051467833)
        ·
          refine ⟨27001535306149040288600875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36002047074865387051467833 27001535306149040288600875)
          ·
            refine ⟨40502302959223560432901313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27001535306149040288600875 40502302959223560432901313)
            ·
              refine ⟨30376727219417670324675985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40502302959223560432901313 30376727219417670324675985)
              ·
                refine ⟨22782545414563252743506989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30376727219417670324675985 22782545414563252743506989)
                ·
                  refine ⟨8543454530461219778815121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22782545414563252743506989 8543454530461219778815121)
                  ·
                    refine ⟨6407590897845914834111341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8543454530461219778815121 6407590897845914834111341)
                    ·
                      refine ⟨2402846586692218062791753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407590897845914834111341 2402846586692218062791753)
                      ·
                        rfl

theorem cell23_4679527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_4679527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679527 prefixEnd_4679527 := by exact prefixLift 4679527
  have htrace : WordTrace (prefixWord ++ tailWord_4679527) baseStart_4679527 baseEnd_4679527 := by
    simpa [prefixWord, tailWord_4679527, baseEnd_4679527] using wordTrace_append hprefix tailTrace_4679527
  have hstable : (prefixWord ++ tailWord_4679527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679527).length < 2 ^ (prefixWord ++ tailWord_4679527).sum := by decide
  have hdescent : baseEnd_4679527 < baseStart_4679527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679557 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_4679557 : Nat := 118140960795 + 4679557 * 2 ^ 59
def prefixEnd_4679557 : Nat := 4983230072969 + 3 ^ 40 * 4679557 * 2
def baseEnd_4679557 : Nat := 2402861991111852945416615

theorem tailTrace_4679557 : CollatzResearch.WordTrace tailWord_4679557 prefixEnd_4679557 2402861991111852945416615 := by
  unfold tailWord_4679557
  simp only [CollatzResearch.WordTrace]
  refine ⟨170677465507771668552772925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113784977005181112368515283 170677465507771668552772925)
  ·
    refine ⟨64004049565414375707289847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170677465507771668552772925 64004049565414375707289847)
    ·
      refine ⟨96006074348121563560934771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64004049565414375707289847 96006074348121563560934771)
      ·
        refine ⟨144009111522182345341402157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96006074348121563560934771 144009111522182345341402157)
        ·
          refine ⟨54003416820818379503025809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144009111522182345341402157 54003416820818379503025809)
          ·
            refine ⟨40502562615613784627269357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54003416820818379503025809 40502562615613784627269357)
            ·
              refine ⟨15188460980855169235226009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40502562615613784627269357 15188460980855169235226009)
              ·
                refine ⟨11391345735641376926419507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15188460980855169235226009 11391345735641376926419507)
                ·
                  refine ⟨17087018603462065389629261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11391345735641376926419507 17087018603462065389629261)
                  ·
                    refine ⟨6407631976298274521110973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17087018603462065389629261 6407631976298274521110973)
                    ·
                      refine ⟨2402861991111852945416615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407631976298274521110973 2402861991111852945416615)
                      ·
                        rfl

theorem cell23_4679557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_4679557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679557 prefixEnd_4679557 := by exact prefixLift 4679557
  have htrace : WordTrace (prefixWord ++ tailWord_4679557) baseStart_4679557 baseEnd_4679557 := by
    simpa [prefixWord, tailWord_4679557, baseEnd_4679557] using wordTrace_append hprefix tailTrace_4679557
  have hstable : (prefixWord ++ tailWord_4679557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679557).length < 2 ^ (prefixWord ++ tailWord_4679557).sum := by decide
  have hdescent : baseEnd_4679557 < baseStart_4679557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679575 : List Nat := [1, 1, 3, 3, 1, 5, 2, 2, 1, 2, 2]
def baseStart_4679575 : Nat := 118140960795 + 4679575 * 2 ^ 59
def prefixEnd_4679575 : Nat := 4983230072969 + 3 ^ 40 * 4679575 * 2
def baseEnd_4679575 : Nat := 2402871233763633874991533

theorem tailTrace_4679575 : CollatzResearch.WordTrace tailWord_4679575 prefixEnd_4679575 2402871233763633874991533 := by
  unfold tailWord_4679575
  simp only [CollatzResearch.WordTrace]
  refine ⟨170678122021706457626928179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113785414681137638417952119 170678122021706457626928179)
  ·
    refine ⟨256017183032559686440392269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170678122021706457626928179 256017183032559686440392269)
    ·
      refine ⟨96006443637209882415147101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256017183032559686440392269 96006443637209882415147101)
      ·
        refine ⟨36002416363953705905680163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96006443637209882415147101 36002416363953705905680163)
        ·
          refine ⟨54003624545930558858520245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36002416363953705905680163 54003624545930558858520245)
          ·
            refine ⟨5062839801180989892986273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54003624545930558858520245 5062839801180989892986273)
            ·
              refine ⟨3797129850885742419739705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5062839801180989892986273 3797129850885742419739705)
              ·
                refine ⟨2847847388164306814804779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3797129850885742419739705 2847847388164306814804779)
                ·
                  refine ⟨4271771082246460222207169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847847388164306814804779 4271771082246460222207169)
                  ·
                    refine ⟨3203828311684845166655377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4271771082246460222207169 3203828311684845166655377)
                    ·
                      refine ⟨2402871233763633874991533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3203828311684845166655377 2402871233763633874991533)
                      ·
                        rfl

theorem cell23_4679575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_4679575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679575 prefixEnd_4679575 := by exact prefixLift 4679575
  have htrace : WordTrace (prefixWord ++ tailWord_4679575) baseStart_4679575 baseEnd_4679575 := by
    simpa [prefixWord, tailWord_4679575, baseEnd_4679575] using wordTrace_append hprefix tailTrace_4679575
  have hstable : (prefixWord ++ tailWord_4679575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679575).length < 2 ^ (prefixWord ++ tailWord_4679575).sum := by decide
  have hdescent : baseEnd_4679575 < baseStart_4679575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679591 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4679591 : Nat := 118140960795 + 4679591 * 2 ^ 59
def prefixEnd_4679591 : Nat := 4983230072969 + 3 ^ 40 * 4679591 * 2
def baseEnd_4679591 : Nat := 2402879449454105812391459

theorem tailTrace_4679591 : CollatzResearch.WordTrace tailWord_4679591 prefixEnd_4679591 2402879449454105812391459 := by
  unfold tailWord_4679591
  simp only [CollatzResearch.WordTrace]
  refine ⟨170678705589648492359510627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113785803726432328239673751 170678705589648492359510627)
  ·
    refine ⟨256018058384472738539265941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170678705589648492359510627 256018058384472738539265941)
    ·
      refine ⟨12000846486772159619028091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 256018058384472738539265941 12000846486772159619028091)
      ·
        refine ⟨18001269730158239428542137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12000846486772159619028091 18001269730158239428542137)
        ·
          refine ⟨13500952297618679571406603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18001269730158239428542137 13500952297618679571406603)
          ·
            refine ⟨20251428446428019357109905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13500952297618679571406603 20251428446428019357109905)
            ·
              refine ⟨15188571334821014517832429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20251428446428019357109905 15188571334821014517832429)
              ·
                refine ⟨5695714250557880444187161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15188571334821014517832429 5695714250557880444187161)
                ·
                  refine ⟨4271785687918410333140371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5695714250557880444187161 4271785687918410333140371)
                  ·
                    refine ⟨6407678531877615499710557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4271785687918410333140371 6407678531877615499710557)
                    ·
                      refine ⟨2402879449454105812391459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407678531877615499710557 2402879449454105812391459)
                      ·
                        rfl

theorem cell23_4679591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4679591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679591 prefixEnd_4679591 := by exact prefixLift 4679591
  have htrace : WordTrace (prefixWord ++ tailWord_4679591) baseStart_4679591 baseEnd_4679591 := by
    simpa [prefixWord, tailWord_4679591, baseEnd_4679591] using wordTrace_append hprefix tailTrace_4679591
  have hstable : (prefixWord ++ tailWord_4679591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679591).length < 2 ^ (prefixWord ++ tailWord_4679591).sum := by decide
  have hdescent : baseEnd_4679591 < baseStart_4679591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679598 : List Nat := [4, 1, 5, 1, 1, 1, 3, 7]
def baseStart_4679598 : Nat := 118140960795 + 4679598 * 2 ^ 59
def prefixEnd_4679598 : Nat := 4983230072969 + 3 ^ 40 * 4679598 * 2
def baseEnd_4679598 : Nat := 88995668289581010555701

theorem tailTrace_4679598 : CollatzResearch.WordTrace tailWord_4679598 prefixEnd_4679598 88995668289581010555701 := by
  unfold tailWord_4679598
  simp only [CollatzResearch.WordTrace]
  refine ⟨21334870112577891569376931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113785973933748755036676965 21334870112577891569376931)
  ·
    refine ⟨32002305168866837354065397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21334870112577891569376931 32002305168866837354065397)
    ·
      refine ⟨3000216109581266001943631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32002305168866837354065397 3000216109581266001943631)
      ·
        refine ⟨4500324164371899002915447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000216109581266001943631 4500324164371899002915447)
        ·
          refine ⟨6750486246557848504373171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500324164371899002915447 6750486246557848504373171)
          ·
            refine ⟨10125729369836772756559757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6750486246557848504373171 10125729369836772756559757)
            ·
              refine ⟨3797148513688789783709909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10125729369836772756559757 3797148513688789783709909)
              ·
                refine ⟨88995668289581010555701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3797148513688789783709909 88995668289581010555701)
                ·
                  rfl

theorem cell23_4679598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_4679598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679598 prefixEnd_4679598 := by exact prefixLift 4679598
  have htrace : WordTrace (prefixWord ++ tailWord_4679598) baseStart_4679598 baseEnd_4679598 := by
    simpa [prefixWord, tailWord_4679598, baseEnd_4679598] using wordTrace_append hprefix tailTrace_4679598
  have hstable : (prefixWord ++ tailWord_4679598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679598).length < 2 ^ (prefixWord ++ tailWord_4679598).sum := by decide
  have hdescent : baseEnd_4679598 < baseStart_4679598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679637 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 7]
def baseStart_4679637 : Nat := 118140960795 + 4679637 * 2 ^ 59
def prefixEnd_4679637 : Nat := 4983230072969 + 3 ^ 40 * 4679637 * 2
def baseEnd_4679637 : Nat := 266989229951579181379583

theorem tailTrace_4679637 : CollatzResearch.WordTrace tailWord_4679637 prefixEnd_4679637 266989229951579181379583 := by
  unfold tailWord_4679637
  simp only [CollatzResearch.WordTrace]
  refine ⟨170680383347481842215685165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113786922231654561477123443 170680383347481842215685165)
  ·
    refine ⟨64005143755305690830881937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170680383347481842215685165 64005143755305690830881937)
    ·
      refine ⟨48003857816479268123161453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64005143755305690830881937 48003857816479268123161453)
      ·
        refine ⟨18001446681179725546185545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48003857816479268123161453 18001446681179725546185545)
        ·
          refine ⟨13501085010884794159639159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18001446681179725546185545 13501085010884794159639159)
          ·
            refine ⟨20251627516327191239458739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13501085010884794159639159 20251627516327191239458739)
            ·
              refine ⟨30377441274490786859188109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20251627516327191239458739 30377441274490786859188109)
              ·
                refine ⟨11391540477934045072195541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30377441274490786859188109 11391540477934045072195541)
                ·
                  refine ⟨266989229951579181379583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11391540477934045072195541 266989229951579181379583)
                  ·
                    rfl

theorem cell23_4679637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_4679637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679637 prefixEnd_4679637 := by exact prefixLift 4679637
  have htrace : WordTrace (prefixWord ++ tailWord_4679637) baseStart_4679637 baseEnd_4679637 := by
    simpa [prefixWord, tailWord_4679637, baseEnd_4679637] using wordTrace_append hprefix tailTrace_4679637
  have hstable : (prefixWord ++ tailWord_4679637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679637).length < 2 ^ (prefixWord ++ tailWord_4679637).sum := by decide
  have hdescent : baseEnd_4679637 < baseStart_4679637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679704 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 1, 6, 2]
def baseStart_4679704 : Nat := 118140960795 + 4679704 * 2 ^ 59
def prefixEnd_4679704 : Nat := 4983230072969 + 3 ^ 40 * 4679704 * 2
def baseEnd_4679704 : Nat := 2402937472768063870278439

theorem tailTrace_4679704 : CollatzResearch.WordTrace tailWord_4679704 prefixEnd_4679704 2402937472768063870278439 := by
  unfold tailWord_4679704
  simp only [CollatzResearch.WordTrace]
  refine ⟨85341413519119556329187083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113788551358826075105582777 85341413519119556329187083)
  ·
    refine ⟨128012120278679334493780625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85341413519119556329187083 128012120278679334493780625)
    ·
      refine ⟨96009090209009500870335469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128012120278679334493780625 96009090209009500870335469)
      ·
        refine ⟨36003408828378562826375801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96009090209009500870335469 36003408828378562826375801)
        ·
          refine ⟨27002556621283922119781851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36003408828378562826375801 27002556621283922119781851)
          ·
            refine ⟨40503834931925883179672777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27002556621283922119781851 40503834931925883179672777)
            ·
              refine ⟨30377876198944412384754583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40503834931925883179672777 30377876198944412384754583)
              ·
                refine ⟨45566814298416618577131875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30377876198944412384754583 45566814298416618577131875)
                ·
                  refine ⟨68350221447624927865697813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45566814298416618577131875 68350221447624927865697813)
                  ·
                    refine ⟨3203916630357418493704585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68350221447624927865697813 3203916630357418493704585)
                    ·
                      refine ⟨2402937472768063870278439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3203916630357418493704585 2402937472768063870278439)
                      ·
                        rfl

theorem cell23_4679704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_4679704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679704 prefixEnd_4679704 := by exact prefixLift 4679704
  have htrace : WordTrace (prefixWord ++ tailWord_4679704) baseStart_4679704 baseEnd_4679704 := by
    simpa [prefixWord, tailWord_4679704, baseEnd_4679704] using wordTrace_append hprefix tailTrace_4679704
  have hstable : (prefixWord ++ tailWord_4679704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679704).length < 2 ^ (prefixWord ++ tailWord_4679704).sum := by decide
  have hdescent : baseEnd_4679704 < baseStart_4679704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679707 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 3]
def baseStart_4679707 : Nat := 118140960795 + 4679707 * 2 ^ 59
def prefixEnd_4679707 : Nat := 4983230072969 + 3 ^ 40 * 4679707 * 2
def baseEnd_4679707 : Nat := 2402939013210027358540925

theorem tailTrace_4679707 : CollatzResearch.WordTrace tailWord_4679707 prefixEnd_4679707 2402939013210027358540925 := by
  unfold tailWord_4679707
  simp only [CollatzResearch.WordTrace]
  refine ⟨170682936457228244170733375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113788624304818829447155583 170682936457228244170733375)
  ·
    refine ⟨256024404685842366256100063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170682936457228244170733375 256024404685842366256100063)
    ·
      refine ⟨384036607028763549384150095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256024404685842366256100063 384036607028763549384150095)
      ·
        refine ⟨576054910543145324076225143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384036607028763549384150095 576054910543145324076225143)
        ·
          refine ⟨864082365814717986114337715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576054910543145324076225143 864082365814717986114337715)
          ·
            refine ⟨1296123548722076979171506573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864082365814717986114337715 1296123548722076979171506573)
            ·
              refine ⟨486046330770778867189314965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1296123548722076979171506573 486046330770778867189314965)
              ·
                refine ⟨22783421754880259399499139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 486046330770778867189314965 22783421754880259399499139)
                ·
                  refine ⟨34175132632320389099248709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22783421754880259399499139 34175132632320389099248709)
                  ·
                    refine ⟨6407837368560072956109133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34175132632320389099248709 6407837368560072956109133)
                    ·
                      refine ⟨2402939013210027358540925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407837368560072956109133 2402939013210027358540925)
                      ·
                        rfl

theorem cell23_4679707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 3].length) (baseStart_4679707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679707 prefixEnd_4679707 := by exact prefixLift 4679707
  have htrace : WordTrace (prefixWord ++ tailWord_4679707) baseStart_4679707 baseEnd_4679707 := by
    simpa [prefixWord, tailWord_4679707, baseEnd_4679707] using wordTrace_append hprefix tailTrace_4679707
  have hstable : (prefixWord ++ tailWord_4679707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679707).length < 2 ^ (prefixWord ++ tailWord_4679707).sum := by decide
  have hdescent : baseEnd_4679707 < baseStart_4679707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679714 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_4679714 : Nat := 118140960795 + 4679714 * 2 ^ 59
def prefixEnd_4679714 : Nat := 4983230072969 + 3 ^ 40 * 4679714 * 2
def baseEnd_4679714 : Nat := 800980869191536277051131

theorem tailTrace_4679714 : CollatzResearch.WordTrace tailWord_4679714 prefixEnd_4679714 800980869191536277051131 := by
  unfold tailWord_4679714
  simp only [CollatzResearch.WordTrace]
  refine ⟨42670797942050721091559549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113788794512135256244158797 42670797942050721091559549)
  ·
    refine ⟨16001549228269020409334831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42670797942050721091559549 16001549228269020409334831)
    ·
      refine ⟨24002323842403530614002247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16001549228269020409334831 24002323842403530614002247)
      ·
        refine ⟨36003485763605295921003371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24002323842403530614002247 36003485763605295921003371)
        ·
          refine ⟨54005228645407943881505057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36003485763605295921003371 54005228645407943881505057)
          ·
            refine ⟨40503921484055957911128793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54005228645407943881505057 40503921484055957911128793)
            ·
              refine ⟨30377941113041968433346595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40503921484055957911128793 30377941113041968433346595)
              ·
                refine ⟨45566911669562952650019893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30377941113041968433346595 45566911669562952650019893)
                ·
                  refine ⟨4271897969021526810939365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45566911669562952650019893 4271897969021526810939365)
                  ·
                    refine ⟨800980869191536277051131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4271897969021526810939365 800980869191536277051131)
                    ·
                      rfl

theorem cell23_4679714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_4679714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679714 prefixEnd_4679714 := by exact prefixLift 4679714
  have htrace : WordTrace (prefixWord ++ tailWord_4679714) baseStart_4679714 baseEnd_4679714 := by
    simpa [prefixWord, tailWord_4679714, baseEnd_4679714] using wordTrace_append hprefix tailTrace_4679714
  have hstable : (prefixWord ++ tailWord_4679714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679714).length < 2 ^ (prefixWord ++ tailWord_4679714).sum := by decide
  have hdescent : baseEnd_4679714 < baseStart_4679714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679734 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4679734 : Nat := 118140960795 + 4679734 * 2 ^ 59
def prefixEnd_4679734 : Nat := 4983230072969 + 3 ^ 40 * 4679734 * 2
def baseEnd_4679734 : Nat := 2402952877187698752903301

theorem tailTrace_4679734 : CollatzResearch.WordTrace tailWord_4679734 prefixEnd_4679734 2402952877187698752903301 := by
  unfold tailWord_4679734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10667745076758151736372891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113789280818753618521310837 10667745076758151736372891)
  ·
    refine ⟨16001617615137227604559337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10667745076758151736372891 16001617615137227604559337)
    ·
      refine ⟨12001213211352920703419503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16001617615137227604559337 12001213211352920703419503)
      ·
        refine ⟨18001819817029381055129255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12001213211352920703419503 18001819817029381055129255)
        ·
          refine ⟨27002729725544071582693883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18001819817029381055129255 27002729725544071582693883)
          ·
            refine ⟨40504094588316107374040825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27002729725544071582693883 40504094588316107374040825)
            ·
              refine ⟨30378070941237080530530619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40504094588316107374040825 30378070941237080530530619)
              ·
                refine ⟨45567106411855620795795929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30378070941237080530530619 45567106411855620795795929)
                ·
                  refine ⟨34175329808891715596846947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45567106411855620795795929 34175329808891715596846947)
                  ·
                    refine ⟨51262994713337573395270421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34175329808891715596846947 51262994713337573395270421)
                    ·
                      refine ⟨2402952877187698752903301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51262994713337573395270421 2402952877187698752903301)
                      ·
                        rfl

theorem cell23_4679734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4679734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679734 prefixEnd_4679734 := by exact prefixLift 4679734
  have htrace : WordTrace (prefixWord ++ tailWord_4679734) baseStart_4679734 baseEnd_4679734 := by
    simpa [prefixWord, tailWord_4679734, baseEnd_4679734] using wordTrace_append hprefix tailTrace_4679734
  have hstable : (prefixWord ++ tailWord_4679734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679734).length < 2 ^ (prefixWord ++ tailWord_4679734).sum := by decide
  have hdescent : baseEnd_4679734 < baseStart_4679734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679744 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 6]
def baseStart_4679744 : Nat := 118140960795 + 4679744 * 2 ^ 59
def prefixEnd_4679744 : Nat := 4983230072969 + 3 ^ 40 * 4679744 * 2
def baseEnd_4679744 : Nat := 266995334666027079308695

theorem tailTrace_4679744 : CollatzResearch.WordTrace tailWord_4679744 prefixEnd_4679744 266995334666027079308695 := by
  unfold tailWord_4679744
  simp only [CollatzResearch.WordTrace]
  refine ⟨85342142979047099744915143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113789523972062799659886857 85342142979047099744915143)
  ·
    refine ⟨128013214468570649617372715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85342142979047099744915143 128013214468570649617372715)
    ·
      refine ⟨192019821702855974426059073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128013214468570649617372715 192019821702855974426059073)
      ·
        refine ⟨144014866277141980819544305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192019821702855974426059073 144014866277141980819544305)
        ·
          refine ⟨108011149707856485614658229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144014866277141980819544305 108011149707856485614658229)
          ·
            refine ⟨10126045285111545526374209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108011149707856485614658229 10126045285111545526374209)
            ·
              refine ⟨7594533963833659144780657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10126045285111545526374209 7594533963833659144780657)
              ·
                refine ⟨5695900472875244358585493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7594533963833659144780657 5695900472875244358585493)
                ·
                  refine ⟨266995334666027079308695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5695900472875244358585493 266995334666027079308695)
                  ·
                    rfl

theorem cell23_4679744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 6].length) (baseStart_4679744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679744 prefixEnd_4679744 := by exact prefixLift 4679744
  have htrace : WordTrace (prefixWord ++ tailWord_4679744) baseStart_4679744 baseEnd_4679744 := by
    simpa [prefixWord, tailWord_4679744, baseEnd_4679744] using wordTrace_append hprefix tailTrace_4679744
  have hstable : (prefixWord ++ tailWord_4679744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679744).length < 2 ^ (prefixWord ++ tailWord_4679744).sum := by decide
  have hdescent : baseEnd_4679744 < baseStart_4679744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679781 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 1, 5, 2]
def baseStart_4679781 : Nat := 118140960795 + 4679781 * 2 ^ 59
def prefixEnd_4679781 : Nat := 4983230072969 + 3 ^ 40 * 4679781 * 2
def baseEnd_4679781 : Nat := 2402977010778460069015585

theorem tailTrace_4679781 : CollatzResearch.WordTrace tailWord_4679781 prefixEnd_4679781 2402977010778460069015585 := by
  unfold tailWord_4679781
  simp only [CollatzResearch.WordTrace]
  refine ⟨170685635458960154808927197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113790423639306769872618131 170685635458960154808927197)
  ·
    refine ⟨64007113297110058053347699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170685635458960154808927197 64007113297110058053347699)
    ·
      refine ⟨96010669945665087080021549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64007113297110058053347699 96010669945665087080021549)
      ·
        refine ⟨36004001229624407655008081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96010669945665087080021549 36004001229624407655008081)
        ·
          refine ⟨27003000922218305741256061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36004001229624407655008081 27003000922218305741256061)
          ·
            refine ⟨10126125345831864652971023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27003000922218305741256061 10126125345831864652971023)
            ·
              refine ⟨15189188018747796979456535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10126125345831864652971023 15189188018747796979456535)
              ·
                refine ⟨22783782028121695469184803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15189188018747796979456535 22783782028121695469184803)
                ·
                  refine ⟨34175673042182543203777205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22783782028121695469184803 34175673042182543203777205)
                  ·
                    refine ⟨3203969347704613425354113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34175673042182543203777205 3203969347704613425354113)
                    ·
                      refine ⟨2402977010778460069015585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3203969347704613425354113 2402977010778460069015585)
                      ·
                        rfl

theorem cell23_4679781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_4679781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679781 prefixEnd_4679781 := by exact prefixLift 4679781
  have htrace : WordTrace (prefixWord ++ tailWord_4679781) baseStart_4679781 baseEnd_4679781 := by
    simpa [prefixWord, tailWord_4679781, baseEnd_4679781] using wordTrace_append hprefix tailTrace_4679781
  have hstable : (prefixWord ++ tailWord_4679781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679781).length < 2 ^ (prefixWord ++ tailWord_4679781).sum := by decide
  have hdescent : baseEnd_4679781 < baseStart_4679781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679788 : List Nat := [2, 2, 1, 1, 3, 3, 1, 5, 1, 1, 3]
def baseStart_4679788 : Nat := 118140960795 + 4679788 * 2 ^ 59
def prefixEnd_4679788 : Nat := 4983230072969 + 3 ^ 40 * 4679788 * 2
def baseEnd_4679788 : Nat := 2402980605143041541628053

theorem tailTrace_4679788 : CollatzResearch.WordTrace tailWord_4679788 prefixEnd_4679788 2402980605143041541628053 := by
  unfold tailWord_4679788
  simp only [CollatzResearch.WordTrace]
  refine ⟨85342945384967397502216009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113790593846623196669621345 85342945384967397502216009)
  ·
    refine ⟨64007209038725548126662007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85342945384967397502216009 64007209038725548126662007)
    ·
      refine ⟨96010813558088322189993011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64007209038725548126662007 96010813558088322189993011)
      ·
        refine ⟨144016220337132483284989517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96010813558088322189993011 144016220337132483284989517)
        ·
          refine ⟨54006082626424681231871069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144016220337132483284989517 54006082626424681231871069)
          ·
            refine ⟨20252280984909255461951651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54006082626424681231871069 20252280984909255461951651)
            ·
              refine ⟨30378421477363883192927477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20252280984909255461951651 30378421477363883192927477)
              ·
                refine ⟨2847977013502864049336951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30378421477363883192927477 2847977013502864049336951)
                ·
                  refine ⟨4271965520254296074005427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847977013502864049336951 4271965520254296074005427)
                  ·
                    refine ⟨6407948280381444111008141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4271965520254296074005427 6407948280381444111008141)
                    ·
                      refine ⟨2402980605143041541628053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6407948280381444111008141 2402980605143041541628053)
                      ·
                        rfl

theorem cell23_4679788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_4679788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679788 prefixEnd_4679788 := by exact prefixLift 4679788
  have htrace : WordTrace (prefixWord ++ tailWord_4679788) baseStart_4679788 baseEnd_4679788 := by
    simpa [prefixWord, tailWord_4679788, baseEnd_4679788] using wordTrace_append hprefix tailTrace_4679788
  have hstable : (prefixWord ++ tailWord_4679788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679788).length < 2 ^ (prefixWord ++ tailWord_4679788).sum := by decide
  have hdescent : baseEnd_4679788 < baseStart_4679788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679791 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 1, 5]
def baseStart_4679791 : Nat := 118140960795 + 4679791 * 2 ^ 59
def prefixEnd_4679791 : Nat := 4983230072969 + 3 ^ 40 * 4679791 * 2
def baseEnd_4679791 : Nat := 800994048528335009963513

theorem tailTrace_4679791 : CollatzResearch.WordTrace tailWord_4679791 prefixEnd_4679791 800994048528335009963513 := by
  unfold tailWord_4679791
  simp only [CollatzResearch.WordTrace]
  refine ⟨170686000188923926516791227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113790666792615951011194151 170686000188923926516791227)
  ·
    refine ⟨256029000283385889775186841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170686000188923926516791227 256029000283385889775186841)
    ·
      refine ⟨192021750212539417331390131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256029000283385889775186841 192021750212539417331390131)
      ·
        refine ⟨288032625318809125997085197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192021750212539417331390131 288032625318809125997085197)
        ·
          refine ⟨108012234494553422248906949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288032625318809125997085197 108012234494553422248906949)
          ·
            refine ⟨20252293967728766671670053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108012234494553422248906949 20252293967728766671670053)
            ·
              refine ⟨3797305118949143750938135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20252293967728766671670053 3797305118949143750938135)
              ·
                refine ⟨5695957678423715626407203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797305118949143750938135 5695957678423715626407203)
                ·
                  refine ⟨8543936517635573439610805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5695957678423715626407203 8543936517635573439610805)
                  ·
                    refine ⟨800994048528335009963513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8543936517635573439610805 800994048528335009963513)
                    ·
                      rfl

theorem cell23_4679791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 5].length) (baseStart_4679791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679791 prefixEnd_4679791 := by exact prefixLift 4679791
  have htrace : WordTrace (prefixWord ++ tailWord_4679791) baseStart_4679791 baseEnd_4679791 := by
    simpa [prefixWord, tailWord_4679791, baseEnd_4679791] using wordTrace_append hprefix tailTrace_4679791
  have hstable : (prefixWord ++ tailWord_4679791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679791).length < 2 ^ (prefixWord ++ tailWord_4679791).sum := by decide
  have hdescent : baseEnd_4679791 < baseStart_4679791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679807 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_4679807 : Nat := 118140960795 + 4679807 * 2 ^ 59
def prefixEnd_4679807 : Nat := 4983230072969 + 3 ^ 40 * 4679807 * 2
def baseEnd_4679807 : Nat := 2402990361275476967290465

theorem tailTrace_4679807 : CollatzResearch.WordTrace tailWord_4679807 prefixEnd_4679807 2402990361275476967290465 := by
  unfold tailWord_4679807
  simp only [CollatzResearch.WordTrace]
  refine ⟨170686583756865961249373675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113791055837910640832915783 170686583756865961249373675)
  ·
    refine ⟨256029875635298941874060513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170686583756865961249373675 256029875635298941874060513)
    ·
      refine ⟨192022406726474206405545385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256029875635298941874060513 192022406726474206405545385)
      ·
        refine ⟨144016805044855654804159039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192022406726474206405545385 144016805044855654804159039)
        ·
          refine ⟨216025207567283482206238559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144016805044855654804159039 216025207567283482206238559)
          ·
            refine ⟨324037811350925223309357839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216025207567283482206238559 324037811350925223309357839)
            ·
              refine ⟨486056717026387834964036759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324037811350925223309357839 486056717026387834964036759)
              ·
                refine ⟨729085075539581752446055139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486056717026387834964036759 729085075539581752446055139)
                ·
                  refine ⟨1093627613309372628669082709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729085075539581752446055139 1093627613309372628669082709)
                  ·
                    refine ⟨12815948593469210492215813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1093627613309372628669082709 12815948593469210492215813)
                    ·
                      refine ⟨2402990361275476967290465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12815948593469210492215813 2402990361275476967290465)
                      ·
                        rfl

theorem cell23_4679807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_4679807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679807 prefixEnd_4679807 := by exact prefixLift 4679807
  have htrace : WordTrace (prefixWord ++ tailWord_4679807) baseStart_4679807 baseEnd_4679807 := by
    simpa [prefixWord, tailWord_4679807, baseEnd_4679807] using wordTrace_append hprefix tailTrace_4679807
  have hstable : (prefixWord ++ tailWord_4679807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679807).length < 2 ^ (prefixWord ++ tailWord_4679807).sum := by decide
  have hdescent : baseEnd_4679807 < baseStart_4679807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679817 : List Nat := [1, 2, 1, 1, 4, 2, 2, 10]
def baseStart_4679817 : Nat := 118140960795 + 4679817 * 2 ^ 59
def prefixEnd_4679817 : Nat := 4983230072969 + 3 ^ 40 * 4679817 * 2
def baseEnd_4679817 : Nat := 88999833188223034376497

theorem tailTrace_4679817 : CollatzResearch.WordTrace tailWord_4679817 prefixEnd_4679817 88999833188223034376497 := by
  unfold tailWord_4679817
  simp only [CollatzResearch.WordTrace]
  refine ⟨170686948486829732957237705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113791298991219821971491803 170686948486829732957237705)
  ·
    refine ⟨128015211365122299717928279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170686948486829732957237705 128015211365122299717928279)
    ·
      refine ⟨192022817047683449576892419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128015211365122299717928279 192022817047683449576892419)
      ·
        refine ⟨288034225571525174365338629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192022817047683449576892419 288034225571525174365338629)
        ·
          refine ⟨54006417294660970193500993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288034225571525174365338629 54006417294660970193500993)
          ·
            refine ⟨40504812970995727645125745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54006417294660970193500993 40504812970995727645125745)
            ·
              refine ⟨30378609728246795733844309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40504812970995727645125745 30378609728246795733844309)
              ·
                refine ⟨88999833188223034376497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30378609728246795733844309 88999833188223034376497)
                ·
                  rfl

theorem cell23_4679817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 10].length) (baseStart_4679817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679817 prefixEnd_4679817 := by exact prefixLift 4679817
  have htrace : WordTrace (prefixWord ++ tailWord_4679817) baseStart_4679817 baseEnd_4679817 := by
    simpa [prefixWord, tailWord_4679817, baseEnd_4679817] using wordTrace_append hprefix tailTrace_4679817
  have hstable : (prefixWord ++ tailWord_4679817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679817).length < 2 ^ (prefixWord ++ tailWord_4679817).sum := by decide
  have hdescent : baseEnd_4679817 < baseStart_4679817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679871 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 3, 3, 2]
def baseStart_4679871 : Nat := 118140960795 + 4679871 * 2 ^ 59
def prefixEnd_4679871 : Nat := 4983230072969 + 3 ^ 40 * 4679871 * 2
def baseEnd_4679871 : Nat := 2403023224037364716890171

theorem tailTrace_4679871 : CollatzResearch.WordTrace tailWord_4679871 prefixEnd_4679871 2403023224037364716890171 := by
  unfold tailWord_4679871
  simp only [CollatzResearch.WordTrace]
  refine ⟨170688918028634100179703467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113792612019089400119802311 170688918028634100179703467)
  ·
    refine ⟨256033377042951150269555201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170688918028634100179703467 256033377042951150269555201)
    ·
      refine ⟨192025032782213362702166401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256033377042951150269555201 192025032782213362702166401)
      ·
        refine ⟨144018774586660022026624801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192025032782213362702166401 144018774586660022026624801)
        ·
          refine ⟨108014080939995016519968601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144018774586660022026624801 108014080939995016519968601)
          ·
            refine ⟨81010560704996262389976451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108014080939995016519968601 81010560704996262389976451)
            ·
              refine ⟨121515841057494393584964677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81010560704996262389976451 121515841057494393584964677)
              ·
                refine ⟨22784220198280198797180877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121515841057494393584964677 22784220198280198797180877)
                ·
                  refine ⟨8544082574355074548942829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22784220198280198797180877 8544082574355074548942829)
                  ·
                    refine ⟨3204030965383152955853561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8544082574355074548942829 3204030965383152955853561)
                    ·
                      refine ⟨2403023224037364716890171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204030965383152955853561 2403023224037364716890171)
                      ·
                        rfl

theorem cell23_4679871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_4679871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679871 prefixEnd_4679871 := by exact prefixLift 4679871
  have htrace : WordTrace (prefixWord ++ tailWord_4679871) baseStart_4679871 baseEnd_4679871 := by
    simpa [prefixWord, tailWord_4679871, baseEnd_4679871] using wordTrace_append hprefix tailTrace_4679871
  have hstable : (prefixWord ++ tailWord_4679871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679871).length < 2 ^ (prefixWord ++ tailWord_4679871).sum := by decide
  have hdescent : baseEnd_4679871 < baseStart_4679871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679904 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_4679904 : Nat := 118140960795 + 4679904 * 2 ^ 59
def prefixEnd_4679904 : Nat := 4983230072969 + 3 ^ 40 * 4679904 * 2
def baseEnd_4679904 : Nat := 2403040168898963087777519

theorem tailTrace_4679904 : CollatzResearch.WordTrace tailWord_4679904 prefixEnd_4679904 2403040168898963087777519 := by
  unfold tailWord_4679904
  simp only [CollatzResearch.WordTrace]
  refine ⟨85345060818757273407827383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113793414425009697877103177 85345060818757273407827383)
  ·
    refine ⟨128017591228135910111741075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85345060818757273407827383 128017591228135910111741075)
    ·
      refine ⟨192026386842203865167611613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128017591228135910111741075 192026386842203865167611613)
      ·
        refine ⟨72009895065826449437854355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192026386842203865167611613 72009895065826449437854355)
        ·
          refine ⟨108014842598739674156781533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72009895065826449437854355 108014842598739674156781533)
          ·
            refine ⟨40505565974527377808793075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108014842598739674156781533 40505565974527377808793075)
            ·
              refine ⟨60758348961791066713189613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40505565974527377808793075 60758348961791066713189613)
              ·
                refine ⟨22784380860671650017446105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60758348961791066713189613 22784380860671650017446105)
                ·
                  refine ⟨17088285645503737513084579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22784380860671650017446105 17088285645503737513084579)
                  ·
                    refine ⟨25632428468255606269626869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17088285645503737513084579 25632428468255606269626869)
                    ·
                      refine ⟨2403040168898963087777519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25632428468255606269626869 2403040168898963087777519)
                      ·
                        rfl

theorem cell23_4679904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_4679904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679904 prefixEnd_4679904 := by exact prefixLift 4679904
  have htrace : WordTrace (prefixWord ++ tailWord_4679904) baseStart_4679904 baseEnd_4679904 := by
    simpa [prefixWord, tailWord_4679904, baseEnd_4679904] using wordTrace_append hprefix tailTrace_4679904
  have hstable : (prefixWord ++ tailWord_4679904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679904).length < 2 ^ (prefixWord ++ tailWord_4679904).sum := by decide
  have hdescent : baseEnd_4679904 < baseStart_4679904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4679905 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_4679905 : Nat := 118140960795 + 4679905 * 2 ^ 59
def prefixEnd_4679905 : Nat := 4983230072969 + 3 ^ 40 * 4679905 * 2
def baseEnd_4679905 : Nat := 2403040682379617583865015

theorem tailTrace_4679905 : CollatzResearch.WordTrace tailWord_4679905 prefixEnd_4679905 2403040682379617583865015 := by
  unfold tailWord_4679905
  simp only [CollatzResearch.WordTrace]
  refine ⟨170690158110510923986441169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113793438740340615990960779 170690158110510923986441169)
  ·
    refine ⟨128017618582883192989830877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170690158110510923986441169 128017618582883192989830877)
    ·
      refine ⟨48006606968581197371186579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128017618582883192989830877 48006606968581197371186579)
      ·
        refine ⟨72009910452871796056779869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48006606968581197371186579 72009910452871796056779869)
        ·
          refine ⟨27003716419826923521292451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72009910452871796056779869 27003716419826923521292451)
          ·
            refine ⟨40505574629740385281938677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27003716419826923521292451 40505574629740385281938677)
            ·
              refine ⟨3797397621538161120181751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40505574629740385281938677 3797397621538161120181751)
              ·
                refine ⟨5696096432307241680272627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797397621538161120181751 5696096432307241680272627)
                ·
                  refine ⟨8544144648460862520408941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5696096432307241680272627 8544144648460862520408941)
                  ·
                    refine ⟨3204054243172823445153353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8544144648460862520408941 3204054243172823445153353)
                    ·
                      refine ⟨2403040682379617583865015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204054243172823445153353 2403040682379617583865015)
                      ·
                        rfl

theorem cell23_4679905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_4679905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4679905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4679905 prefixEnd_4679905 := by exact prefixLift 4679905
  have htrace : WordTrace (prefixWord ++ tailWord_4679905) baseStart_4679905 baseEnd_4679905 := by
    simpa [prefixWord, tailWord_4679905, baseEnd_4679905] using wordTrace_append hprefix tailTrace_4679905
  have hstable : (prefixWord ++ tailWord_4679905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4679905).length < 2 ^ (prefixWord ++ tailWord_4679905).sum := by decide
  have hdescent : baseEnd_4679905 < baseStart_4679905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4679905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680048 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 6]
def baseStart_4680048 : Nat := 118140960795 + 4680048 * 2 ^ 59
def prefixEnd_4680048 : Nat := 4983230072969 + 3 ^ 40 * 4680048 * 2
def baseEnd_4680048 : Nat := 267012678901467836041873

theorem tailTrace_4680048 : CollatzResearch.WordTrace tailWord_4680048 prefixEnd_4680048 267012678901467836041873 := by
  unfold tailWord_4680048
  simp only [CollatzResearch.WordTrace]
  refine ⟨85347686874496429704448399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113796915832661906272597865 85347686874496429704448399)
  ·
    refine ⟨128021530311744644556672599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85347686874496429704448399 128021530311744644556672599)
    ·
      refine ⟨192032295467616966835008899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128021530311744644556672599 192032295467616966835008899)
      ·
        refine ⟨288048443201425450252513349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192032295467616966835008899 288048443201425450252513349)
        ·
          refine ⟨54009083100267271922346253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288048443201425450252513349 54009083100267271922346253)
          ·
            refine ⟨20253406162600226970879845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54009083100267271922346253 20253406162600226970879845)
            ·
              refine ⟨3797513655487542557039971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20253406162600226970879845 3797513655487542557039971)
              ·
                refine ⟨5696270483231313835559957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797513655487542557039971 5696270483231313835559957)
                ·
                  refine ⟨267012678901467836041873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5696270483231313835559957 267012678901467836041873)
                  ·
                    rfl

theorem cell23_4680048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 6].length) (baseStart_4680048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680048 prefixEnd_4680048 := by exact prefixLift 4680048
  have htrace : WordTrace (prefixWord ++ tailWord_4680048) baseStart_4680048 baseEnd_4680048 := by
    simpa [prefixWord, tailWord_4680048, baseEnd_4680048] using wordTrace_append hprefix tailTrace_4680048
  have hstable : (prefixWord ++ tailWord_4680048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680048).length < 2 ^ (prefixWord ++ tailWord_4680048).sum := by decide
  have hdescent : baseEnd_4680048 < baseStart_4680048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680081 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_4680081 : Nat := 118140960795 + 4680081 * 2 ^ 59
def prefixEnd_4680081 : Nat := 4983230072969 + 3 ^ 40 * 4680081 * 2
def baseEnd_4680081 : Nat := 2403131054974808895264205

theorem tailTrace_4680081 : CollatzResearch.WordTrace tailWord_4680081 prefixEnd_4680081 2403131054974808895264205 := by
  unfold tailWord_4680081
  simp only [CollatzResearch.WordTrace]
  refine ⟨170696577357873306044848097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113797718238582204029898731 170696577357873306044848097)
  ·
    refine ⟨128022433018404979533636073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170696577357873306044848097 128022433018404979533636073)
    ·
      refine ⟨96016824763803734650227055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128022433018404979533636073 96016824763803734650227055)
      ·
        refine ⟨144025237145705601975340583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96016824763803734650227055 144025237145705601975340583)
        ·
          refine ⟨216037855718558402963010875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144025237145705601975340583 216037855718558402963010875)
          ·
            refine ⟨324056783577837604444516313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216037855718558402963010875 324056783577837604444516313)
            ·
              refine ⟨243042587683378203333387235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324056783577837604444516313 243042587683378203333387235)
              ·
                refine ⟨364563881525067305000080853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243042587683378203333387235 364563881525067305000080853)
                ·
                  refine ⟨8544465973243764960939395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 364563881525067305000080853 8544465973243764960939395)
                  ·
                    refine ⟨12816698959865647441409093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8544465973243764960939395 12816698959865647441409093)
                    ·
                      refine ⟨2403131054974808895264205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12816698959865647441409093 2403131054974808895264205)
                      ·
                        rfl

theorem cell23_4680081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_4680081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680081 prefixEnd_4680081 := by exact prefixLift 4680081
  have htrace : WordTrace (prefixWord ++ tailWord_4680081) baseStart_4680081 baseEnd_4680081 := by
    simpa [prefixWord, tailWord_4680081, baseEnd_4680081] using wordTrace_append hprefix tailTrace_4680081
  have hstable : (prefixWord ++ tailWord_4680081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680081).length < 2 ^ (prefixWord ++ tailWord_4680081).sum := by decide
  have hdescent : baseEnd_4680081 < baseStart_4680081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680098 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4680098 : Nat := 118140960795 + 4680098 * 2 ^ 59
def prefixEnd_4680098 : Nat := 4983230072969 + 3 ^ 40 * 4680098 * 2
def baseEnd_4680098 : Nat := 2403139784145935328751627

theorem tailTrace_4680098 : CollatzResearch.WordTrace tailWord_4680098 prefixEnd_4680098 2403139784145935328751627 := by
  unfold tailWord_4680098
  simp only [CollatzResearch.WordTrace]
  refine ⟨42674299349702929487054237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113798131599207811965477965 42674299349702929487054237)
  ·
    refine ⟨16002862256138598557645339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42674299349702929487054237 16002862256138598557645339)
    ·
      refine ⟨24004293384207897836468009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16002862256138598557645339 24004293384207897836468009)
      ·
        refine ⟨18003220038155923377351007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24004293384207897836468009 18003220038155923377351007)
        ·
          refine ⟨27004830057233885066026511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18003220038155923377351007 27004830057233885066026511)
          ·
            refine ⟨40507245085850827599039767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27004830057233885066026511 40507245085850827599039767)
            ·
              refine ⟨60760867628776241398559651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40507245085850827599039767 60760867628776241398559651)
              ·
                refine ⟨91141301443164362097839477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60760867628776241398559651 91141301443164362097839477)
                ·
                  refine ⟨8544497010296658946672451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91141301443164362097839477 8544497010296658946672451)
                  ·
                    refine ⟨12816745515444988420008677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8544497010296658946672451 12816745515444988420008677)
                    ·
                      refine ⟨2403139784145935328751627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12816745515444988420008677 2403139784145935328751627)
                      ·
                        rfl

theorem cell23_4680098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4680098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680098 prefixEnd_4680098 := by exact prefixLift 4680098
  have htrace : WordTrace (prefixWord ++ tailWord_4680098) baseStart_4680098 baseEnd_4680098 := by
    simpa [prefixWord, tailWord_4680098, baseEnd_4680098] using wordTrace_append hprefix tailTrace_4680098
  have hstable : (prefixWord ++ tailWord_4680098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680098).length < 2 ^ (prefixWord ++ tailWord_4680098).sum := by decide
  have hdescent : baseEnd_4680098 < baseStart_4680098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680101 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_4680101 : Nat := 118140960795 + 4680101 * 2 ^ 59
def prefixEnd_4680101 : Nat := 4983230072969 + 3 ^ 40 * 4680101 * 2
def baseEnd_4680101 : Nat := 2403141324587898817014113

theorem tailTrace_4680101 : CollatzResearch.WordTrace tailWord_4680101 prefixEnd_4680101 2403141324587898817014113 := by
  unfold tailWord_4680101
  simp only [CollatzResearch.WordTrace]
  refine ⟨170697306817800849460576157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113798204545200566307050771 170697306817800849460576157)
  ·
    refine ⟨64011490056675318547716059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170697306817800849460576157 64011490056675318547716059)
    ·
      refine ⟨96017235085012977821574089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64011490056675318547716059 96017235085012977821574089)
      ·
        refine ⟨72012926313759733366180567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96017235085012977821574089 72012926313759733366180567)
        ·
          refine ⟨108019389470639600049270851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72012926313759733366180567 108019389470639600049270851)
          ·
            refine ⟨162029084205959400073906277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108019389470639600049270851 162029084205959400073906277)
            ·
              refine ⟨30380453288617387513857427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162029084205959400073906277 30380453288617387513857427)
              ·
                refine ⟨45570679932926081270786141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30380453288617387513857427 45570679932926081270786141)
                ·
                  refine ⟨17089004974847280476544803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45570679932926081270786141 17089004974847280476544803)
                  ·
                    refine ⟨25633507462270920714817205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17089004974847280476544803 25633507462270920714817205)
                    ·
                      refine ⟨2403141324587898817014113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25633507462270920714817205 2403141324587898817014113)
                      ·
                        rfl

theorem cell23_4680101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_4680101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680101 prefixEnd_4680101 := by exact prefixLift 4680101
  have htrace : WordTrace (prefixWord ++ tailWord_4680101) baseStart_4680101 baseEnd_4680101 := by
    simpa [prefixWord, tailWord_4680101, baseEnd_4680101] using wordTrace_append hprefix tailTrace_4680101
  have hstable : (prefixWord ++ tailWord_4680101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680101).length < 2 ^ (prefixWord ++ tailWord_4680101).sum := by decide
  have hdescent : baseEnd_4680101 < baseStart_4680101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680129 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4680129 : Nat := 118140960795 + 4680129 * 2 ^ 59
def prefixEnd_4680129 : Nat := 4983230072969 + 3 ^ 40 * 4680129 * 2
def baseEnd_4680129 : Nat := 801051900682074902487995

theorem tailTrace_4680129 : CollatzResearch.WordTrace tailWord_4680129 prefixEnd_4680129 801051900682074902487995 := by
  unfold tailWord_4680129
  simp only [CollatzResearch.WordTrace]
  refine ⟨170698328061699410242595441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113798885374466273495063627 170698328061699410242595441)
  ·
    refine ⟨128023746046274557681946581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170698328061699410242595441 128023746046274557681946581)
    ·
      refine ⟨3000556547959559945670623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 128023746046274557681946581 3000556547959559945670623)
      ·
        refine ⟨4500834821939339918505935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000556547959559945670623 4500834821939339918505935)
        ·
          refine ⟨6751252232909009877758903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500834821939339918505935 6751252232909009877758903)
          ·
            refine ⟨10126878349363514816638355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6751252232909009877758903 10126878349363514816638355)
            ·
              refine ⟨15190317524045272224957533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10126878349363514816638355 15190317524045272224957533)
              ·
                refine ⟨5696369071516977084359075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15190317524045272224957533 5696369071516977084359075)
                ·
                  refine ⟨8544553607275465626538613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5696369071516977084359075 8544553607275465626538613)
                  ·
                    refine ⟨801051900682074902487995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8544553607275465626538613 801051900682074902487995)
                    ·
                      rfl

theorem cell23_4680129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4680129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680129 prefixEnd_4680129 := by exact prefixLift 4680129
  have htrace : WordTrace (prefixWord ++ tailWord_4680129) baseStart_4680129 baseEnd_4680129 := by
    simpa [prefixWord, tailWord_4680129, baseEnd_4680129] using wordTrace_append hprefix tailTrace_4680129
  have hstable : (prefixWord ++ tailWord_4680129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680129).length < 2 ^ (prefixWord ++ tailWord_4680129).sum := by decide
  have hdescent : baseEnd_4680129 < baseStart_4680129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680132 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4680132 : Nat := 118140960795 + 4680132 * 2 ^ 59
def prefixEnd_4680132 : Nat := 4983230072969 + 3 ^ 40 * 4680132 * 2
def baseEnd_4680132 : Nat := 2403157242488188195726471

theorem tailTrace_4680132 : CollatzResearch.WordTrace tailWord_4680132 prefixEnd_4680132 2403157242488188195726471 := by
  unfold tailWord_4680132
  simp only [CollatzResearch.WordTrace]
  refine ⟨85349218740344270877477325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113798958320459027836636433 85349218740344270877477325)
  ·
    refine ⟨32005957027629101579053997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85349218740344270877477325 32005957027629101579053997)
    ·
      refine ⟨12002233885360913092145249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32005957027629101579053997 12002233885360913092145249)
      ·
        refine ⟨9001675414020684819108937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12002233885360913092145249 9001675414020684819108937)
        ·
          refine ⟨6751256560515513614331703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9001675414020684819108937 6751256560515513614331703)
          ·
            refine ⟨10126884840773270421497555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6751256560515513614331703 10126884840773270421497555)
            ·
              refine ⟨15190327261159905632246333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10126884840773270421497555 15190327261159905632246333)
              ·
                refine ⟨5696372722934964612092375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15190327261159905632246333 5696372722934964612092375)
                ·
                  refine ⟨8544559084402446918138563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5696372722934964612092375 8544559084402446918138563)
                  ·
                    refine ⟨12816838626603670377207845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8544559084402446918138563 12816838626603670377207845)
                    ·
                      refine ⟨2403157242488188195726471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12816838626603670377207845 2403157242488188195726471)
                      ·
                        rfl

theorem cell23_4680132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4680132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680132 prefixEnd_4680132 := by exact prefixLift 4680132
  have htrace : WordTrace (prefixWord ++ tailWord_4680132) baseStart_4680132 baseEnd_4680132 := by
    simpa [prefixWord, tailWord_4680132, baseEnd_4680132] using wordTrace_append hprefix tailTrace_4680132
  have hstable : (prefixWord ++ tailWord_4680132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680132).length < 2 ^ (prefixWord ++ tailWord_4680132).sum := by decide
  have hdescent : baseEnd_4680132 < baseStart_4680132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680135 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_4680135 : Nat := 118140960795 + 4680135 * 2 ^ 59
def prefixEnd_4680135 : Nat := 4983230072969 + 3 ^ 40 * 4680135 * 2
def baseEnd_4680135 : Nat := 2403158782930151683988957

theorem tailTrace_4680135 : CollatzResearch.WordTrace tailWord_4680135 prefixEnd_4680135 2403158782930151683988957 := by
  unfold tailWord_4680135
  simp only [CollatzResearch.WordTrace]
  refine ⟨170698546899677673267313859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113799031266451782178209239 170698546899677673267313859)
  ·
    refine ⟨256047820349516509900970789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170698546899677673267313859 256047820349516509900970789)
    ·
      refine ⟨48008966315534345606432023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256047820349516509900970789 48008966315534345606432023)
      ·
        refine ⟨72013449473301518409648035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48008966315534345606432023 72013449473301518409648035)
        ·
          refine ⟨108020174209952277614472053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72013449473301518409648035 108020174209952277614472053)
          ·
            refine ⟨10126891332183026026356755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108020174209952277614472053 10126891332183026026356755)
            ·
              refine ⟨15190336998274539039535133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10126891332183026026356755 15190336998274539039535133)
              ·
                refine ⟨5696376374352952139825675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15190336998274539039535133 5696376374352952139825675)
                ·
                  refine ⟨8544564561529428209738513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5696376374352952139825675 8544564561529428209738513)
                  ·
                    refine ⟨6408423421147071157303885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8544564561529428209738513 6408423421147071157303885)
                    ·
                      refine ⟨2403158782930151683988957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6408423421147071157303885 2403158782930151683988957)
                      ·
                        rfl

theorem cell23_4680135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_4680135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680135 prefixEnd_4680135 := by exact prefixLift 4680135
  have htrace : WordTrace (prefixWord ++ tailWord_4680135) baseStart_4680135 baseEnd_4680135 := by
    simpa [prefixWord, tailWord_4680135, baseEnd_4680135] using wordTrace_append hprefix tailTrace_4680135
  have hstable : (prefixWord ++ tailWord_4680135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680135).length < 2 ^ (prefixWord ++ tailWord_4680135).sum := by decide
  have hdescent : baseEnd_4680135 < baseStart_4680135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680149 : List Nat := [1, 3, 2, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4680149 : Nat := 118140960795 + 4680149 * 2 ^ 59
def prefixEnd_4680149 : Nat := 4983230072969 + 3 ^ 40 * 4680149 * 2
def baseEnd_4680149 : Nat := 2403165971659314629213893

theorem tailTrace_4680149 : CollatzResearch.WordTrace tailWord_4680149 prefixEnd_4680149 2403165971659314629213893 := by
  unfold tailWord_4680149
  simp only [CollatzResearch.WordTrace]
  refine ⟨170699057521626953658323501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113799371681084635772215667 170699057521626953658323501)
  ·
    refine ⟨64012146570610107621871313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170699057521626953658323501 64012146570610107621871313)
    ·
      refine ⟨48009109927957580716403485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64012146570610107621871313 48009109927957580716403485)
      ·
        refine ⟨18003416222984092768651307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48009109927957580716403485 18003416222984092768651307)
        ·
          refine ⟨27005124334476139152976961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18003416222984092768651307 27005124334476139152976961)
          ·
            refine ⟨20253843250857104364732721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27005124334476139152976961 20253843250857104364732721)
            ·
              refine ⟨15190382438142828273549541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20253843250857104364732721 15190382438142828273549541)
              ·
                refine ⟨2848196707151780301290539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15190382438142828273549541 2848196707151780301290539)
                ·
                  refine ⟨4272295060727670451935809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848196707151780301290539 4272295060727670451935809)
                  ·
                    refine ⟨3204221295545752838951857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4272295060727670451935809 3204221295545752838951857)
                    ·
                      refine ⟨2403165971659314629213893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204221295545752838951857 2403165971659314629213893)
                      ·
                        rfl

theorem cell23_4680149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4680149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680149 prefixEnd_4680149 := by exact prefixLift 4680149
  have htrace : WordTrace (prefixWord ++ tailWord_4680149) baseStart_4680149 baseEnd_4680149 := by
    simpa [prefixWord, tailWord_4680149, baseEnd_4680149] using wordTrace_append hprefix tailTrace_4680149
  have hstable : (prefixWord ++ tailWord_4680149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680149).length < 2 ^ (prefixWord ++ tailWord_4680149).sum := by decide
  have hdescent : baseEnd_4680149 < baseStart_4680149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680162 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4680162 : Nat := 118140960795 + 4680162 * 2 ^ 59
def prefixEnd_4680162 : Nat := 4983230072969 + 3 ^ 40 * 4680162 * 2
def baseEnd_4680162 : Nat := 2403172646907823078351333

theorem tailTrace_4680162 : CollatzResearch.WordTrace tailWord_4680162 prefixEnd_4680162 2403172646907823078351333 := by
  unfold tailWord_4680162
  simp only [CollatzResearch.WordTrace]
  refine ⟨42674882917644964219636685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113799687780386571252364493 42674882917644964219636685)
  ·
    refine ⟨16003081094116861582363757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42674882917644964219636685 16003081094116861582363757)
    ·
      refine ⟨6001155410293823093386409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16003081094116861582363757 6001155410293823093386409)
      ·
        refine ⟨4500866557720367320039807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6001155410293823093386409 4500866557720367320039807)
        ·
          refine ⟨6751299836580550980059711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500866557720367320039807 6751299836580550980059711)
          ·
            refine ⟨10126949754870826470089567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6751299836580550980059711 10126949754870826470089567)
            ·
              refine ⟨15190424632306239705134351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10126949754870826470089567 15190424632306239705134351)
              ·
                refine ⟨22785636948459359557701527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15190424632306239705134351 22785636948459359557701527)
                ·
                  refine ⟨34178455422689039336552291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22785636948459359557701527 34178455422689039336552291)
                  ·
                    refine ⟨51267683134033559004828437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34178455422689039336552291 51267683134033559004828437)
                    ·
                      refine ⟨2403172646907823078351333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51267683134033559004828437 2403172646907823078351333)
                      ·
                        rfl

theorem cell23_4680162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4680162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680162 prefixEnd_4680162 := by exact prefixLift 4680162
  have htrace : WordTrace (prefixWord ++ tailWord_4680162) baseStart_4680162 baseEnd_4680162 := by
    simpa [prefixWord, tailWord_4680162, baseEnd_4680162] using wordTrace_append hprefix tailTrace_4680162
  have hstable : (prefixWord ++ tailWord_4680162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680162).length < 2 ^ (prefixWord ++ tailWord_4680162).sum := by decide
  have hdescent : baseEnd_4680162 < baseStart_4680162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680201 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_4680201 : Nat := 118140960795 + 4680201 * 2 ^ 59
def prefixEnd_4680201 : Nat := 4983230072969 + 3 ^ 40 * 4680201 * 2
def baseEnd_4680201 : Nat := 2403192672653348425763653

theorem tailTrace_4680201 : CollatzResearch.WordTrace tailWord_4680201 prefixEnd_4680201 2403192672653348425763653 := by
  unfold tailWord_4680201
  simp only [CollatzResearch.WordTrace]
  refine ⟨170700954117438566539216457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113800636078292377692810971 170700954117438566539216457)
  ·
    refine ⟨128025715588078924904412343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170700954117438566539216457 128025715588078924904412343)
    ·
      refine ⟨192038573382118387356618515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128025715588078924904412343 192038573382118387356618515)
      ·
        refine ⟨288057860073177581034927773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192038573382118387356618515 288057860073177581034927773)
        ·
          refine ⟨108021697527441592888097915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288057860073177581034927773 108021697527441592888097915)
          ·
            refine ⟨162032546291162389332146873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108021697527441592888097915 162032546291162389332146873)
            ·
              refine ⟨121524409718371791999110155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162032546291162389332146873 121524409718371791999110155)
              ·
                refine ⟨182286614577557687998665233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121524409718371791999110155 182286614577557687998665233)
                ·
                  refine ⟨136714960933168265998998925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182286614577557687998665233 136714960933168265998998925)
                  ·
                    refine ⟨51268110349938099749624597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136714960933168265998998925 51268110349938099749624597)
                    ·
                      refine ⟨2403192672653348425763653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51268110349938099749624597 2403192672653348425763653)
                      ·
                        rfl

theorem cell23_4680201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_4680201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680201 prefixEnd_4680201 := by exact prefixLift 4680201
  have htrace : WordTrace (prefixWord ++ tailWord_4680201) baseStart_4680201 baseEnd_4680201 := by
    simpa [prefixWord, tailWord_4680201, baseEnd_4680201] using wordTrace_append hprefix tailTrace_4680201
  have hstable : (prefixWord ++ tailWord_4680201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680201).length < 2 ^ (prefixWord ++ tailWord_4680201).sum := by decide
  have hdescent : baseEnd_4680201 < baseStart_4680201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680218 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_4680218 : Nat := 118140960795 + 4680218 * 2 ^ 59
def prefixEnd_4680218 : Nat := 4983230072969 + 3 ^ 40 * 4680218 * 2
def baseEnd_4680218 : Nat := 2403201401824474859251075

theorem tailTrace_4680218 : CollatzResearch.WordTrace tailWord_4680218 prefixEnd_4680218 2403201401824474859251075 := by
  unfold tailWord_4680218
  simp only [CollatzResearch.WordTrace]
  refine ⟨42675393539594244610646327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113801049438917985628390205 42675393539594244610646327)
  ·
    refine ⟨64013090309391366915969491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42675393539594244610646327 64013090309391366915969491)
    ·
      refine ⟨96019635464087050373954237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64013090309391366915969491 96019635464087050373954237)
      ·
        refine ⟨36007363299032643890232839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96019635464087050373954237 36007363299032643890232839)
        ·
          refine ⟨54011044948548965835349259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36007363299032643890232839 54011044948548965835349259)
          ·
            refine ⟨81016567422823448753023889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54011044948548965835349259 81016567422823448753023889)
            ·
              refine ⟨60762425567117586564767917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81016567422823448753023889 60762425567117586564767917)
              ·
                refine ⟨22785909587669094961787969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60762425567117586564767917 22785909587669094961787969)
                ·
                  refine ⟨17089432190751821221340977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22785909587669094961787969 17089432190751821221340977)
                  ·
                    refine ⟨12817074143063865916005733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17089432190751821221340977 12817074143063865916005733)
                    ·
                      refine ⟨2403201401824474859251075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12817074143063865916005733 2403201401824474859251075)
                      ·
                        rfl

theorem cell23_4680218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_4680218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680218 prefixEnd_4680218 := by exact prefixLift 4680218
  have htrace : WordTrace (prefixWord ++ tailWord_4680218) baseStart_4680218 baseEnd_4680218 := by
    simpa [prefixWord, tailWord_4680218, baseEnd_4680218] using wordTrace_append hprefix tailTrace_4680218
  have hstable : (prefixWord ++ tailWord_4680218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680218).length < 2 ^ (prefixWord ++ tailWord_4680218).sum := by decide
  have hdescent : baseEnd_4680218 < baseStart_4680218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680245 : List Nat := [1, 3, 3, 1, 1, 2, 2, 5, 5]
def baseStart_4680245 : Nat := 118140960795 + 4680245 * 2 ^ 59
def prefixEnd_4680245 : Nat := 4983230072969 + 3 ^ 40 * 4680245 * 2
def baseEnd_4680245 : Nat := 267023918422460694845939

theorem tailTrace_4680245 : CollatzResearch.WordTrace tailWord_4680245 prefixEnd_4680245 267023918422460694845939 := by
  unfold tailWord_4680245
  simp only [CollatzResearch.WordTrace]
  refine ⟨170702558929279162053818189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113801705952852774702545459 170702558929279162053818189)
  ·
    refine ⟨64013459598479685770181821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170702558929279162053818189 64013459598479685770181821)
    ·
      refine ⟨24005047349429882163818183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64013459598479685770181821 24005047349429882163818183)
      ·
        refine ⟨36007571024144823245727275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24005047349429882163818183 36007571024144823245727275)
        ·
          refine ⟨54011356536217234868590913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36007571024144823245727275 54011356536217234868590913)
          ·
            refine ⟨40508517402162926151443185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54011356536217234868590913 40508517402162926151443185)
            ·
              refine ⟨30381388051622194613582389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40508517402162926151443185 30381388051622194613582389)
              ·
                refine ⟨2848255129839580745023349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30381388051622194613582389 2848255129839580745023349)
                ·
                  refine ⟨267023918422460694845939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2848255129839580745023349 267023918422460694845939)
                  ·
                    rfl

theorem cell23_4680245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_4680245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680245 prefixEnd_4680245 := by exact prefixLift 4680245
  have htrace : WordTrace (prefixWord ++ tailWord_4680245) baseStart_4680245 baseEnd_4680245 := by
    simpa [prefixWord, tailWord_4680245, baseEnd_4680245] using wordTrace_append hprefix tailTrace_4680245
  have hstable : (prefixWord ++ tailWord_4680245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680245).length < 2 ^ (prefixWord ++ tailWord_4680245).sum := by decide
  have hdescent : baseEnd_4680245 < baseStart_4680245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680268 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_4680268 : Nat := 118140960795 + 4680268 * 2 ^ 59
def prefixEnd_4680268 : Nat := 4983230072969 + 3 ^ 40 * 4680268 * 2
def baseEnd_4680268 : Nat := 2403227075857199663625845

theorem tailTrace_4680268 : CollatzResearch.WordTrace tailWord_4680268 prefixEnd_4680268 2403227075857199663625845 := by
  unfold tailWord_4680268
  simp only [CollatzResearch.WordTrace]
  refine ⟨85351698904097918490952729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113802265205463891321270305 85351698904097918490952729)
  ·
    refine ⟨64013774178073438868214547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85351698904097918490952729 64013774178073438868214547)
    ·
      refine ⟨96020661267110158302321821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64013774178073438868214547 96020661267110158302321821)
      ·
        refine ⟨36007747975166309363370683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96020661267110158302321821 36007747975166309363370683)
        ·
          refine ⟨54011621962749464045056025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36007747975166309363370683 54011621962749464045056025)
          ·
            refine ⟨40508716472062098033792019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54011621962749464045056025 40508716472062098033792019)
            ·
              refine ⟨60763074708093147050688029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40508716472062098033792019 60763074708093147050688029)
              ·
                refine ⟨22786153015534930144008011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60763074708093147050688029 22786153015534930144008011)
                ·
                  refine ⟨34179229523302395216012017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22786153015534930144008011 34179229523302395216012017)
                  ·
                    refine ⟨25634422142476796412009013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34179229523302395216012017 25634422142476796412009013)
                    ·
                      refine ⟨2403227075857199663625845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25634422142476796412009013 2403227075857199663625845)
                      ·
                        rfl

theorem cell23_4680268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_4680268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680268 prefixEnd_4680268 := by exact prefixLift 4680268
  have htrace : WordTrace (prefixWord ++ tailWord_4680268) baseStart_4680268 baseEnd_4680268 := by
    simpa [prefixWord, tailWord_4680268, baseEnd_4680268] using wordTrace_append hprefix tailTrace_4680268
  have hstable : (prefixWord ++ tailWord_4680268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680268).length < 2 ^ (prefixWord ++ tailWord_4680268).sum := by decide
  have hdescent : baseEnd_4680268 < baseStart_4680268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680295 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_4680295 : Nat := 118140960795 + 4680295 * 2 ^ 59
def prefixEnd_4680295 : Nat := 4983230072969 + 3 ^ 40 * 4680295 * 2
def baseEnd_4680295 : Nat := 2403240939834871057988221

theorem tailTrace_4680295 : CollatzResearch.WordTrace tailWord_4680295 prefixEnd_4680295 2403240939834871057988221 := by
  unfold tailWord_4680295
  simp only [CollatzResearch.WordTrace]
  refine ⟨170704382579098020593138339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113802921719398680395425559 170704382579098020593138339)
  ·
    refine ⟨256056573868647030889707509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170704382579098020593138339 256056573868647030889707509)
    ·
      refine ⟨24005303800185659145910079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256056573868647030889707509 24005303800185659145910079)
      ·
        refine ⟨36007955700278488718865119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24005303800185659145910079 36007955700278488718865119)
        ·
          refine ⟨54011933550417733078297679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36007955700278488718865119 54011933550417733078297679)
          ·
            refine ⟨81017900325626599617446519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54011933550417733078297679 81017900325626599617446519)
            ·
              refine ⟨121526850488439899426169779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81017900325626599617446519 121526850488439899426169779)
              ·
                refine ⟨182290275732659849139254669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121526850488439899426169779 182290275732659849139254669)
                ·
                  refine ⟨68358853399747443427220501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182290275732659849139254669 68358853399747443427220501)
                  ·
                    refine ⟨3204321253113161410650961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68358853399747443427220501 3204321253113161410650961)
                    ·
                      refine ⟨2403240939834871057988221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204321253113161410650961 2403240939834871057988221)
                      ·
                        rfl

theorem cell23_4680295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_4680295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680295 prefixEnd_4680295 := by exact prefixLift 4680295
  have htrace : WordTrace (prefixWord ++ tailWord_4680295) baseStart_4680295 baseEnd_4680295 := by
    simpa [prefixWord, tailWord_4680295, baseEnd_4680295] using wordTrace_append hprefix tailTrace_4680295
  have hstable : (prefixWord ++ tailWord_4680295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680295).length < 2 ^ (prefixWord ++ tailWord_4680295).sum := by decide
  have hdescent : baseEnd_4680295 < baseStart_4680295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680412 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4680412 : Nat := 118140960795 + 4680412 * 2 ^ 59
def prefixEnd_4680412 : Nat := 4983230072969 + 3 ^ 40 * 4680412 * 2
def baseEnd_4680412 : Nat := 801100339023815700075061

theorem tailTrace_4680412 : CollatzResearch.WordTrace tailWord_4680412 prefixEnd_4680412 801100339023815700075061 := by
  unfold tailWord_4680412
  simp only [CollatzResearch.WordTrace]
  refine ⟨85354324959837074787573745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113805766613116099716764993 85354324959837074787573745)
  ·
    refine ⟨64015743719877806090680309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85354324959837074787573745 64015743719877806090680309)
    ·
      refine ⟨6001475973738544321001279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64015743719877806090680309 6001475973738544321001279)
      ·
        refine ⟨9002213960607816481501919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6001475973738544321001279 9002213960607816481501919)
        ·
          refine ⟨13503320940911724722252879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9002213960607816481501919 13503320940911724722252879)
          ·
            refine ⟨20254981411367587083379319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13503320940911724722252879 20254981411367587083379319)
            ·
              refine ⟨30382472117051380625068979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20254981411367587083379319 30382472117051380625068979)
              ·
                refine ⟨45573708175577070937603469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30382472117051380625068979 45573708175577070937603469)
                ·
                  refine ⟨17090140565841401601601301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45573708175577070937603469 17090140565841401601601301)
                  ·
                    refine ⟨801100339023815700075061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17090140565841401601601301 801100339023815700075061)
                    ·
                      rfl

theorem cell23_4680412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4680412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680412 prefixEnd_4680412 := by exact prefixLift 4680412
  have htrace : WordTrace (prefixWord ++ tailWord_4680412) baseStart_4680412 baseEnd_4680412 := by
    simpa [prefixWord, tailWord_4680412, baseEnd_4680412] using wordTrace_append hprefix tailTrace_4680412
  have hstable : (prefixWord ++ tailWord_4680412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680412).length < 2 ^ (prefixWord ++ tailWord_4680412).sum := by decide
  have hdescent : baseEnd_4680412 < baseStart_4680412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680415 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_4680415 : Nat := 118140960795 + 4680415 * 2 ^ 59
def prefixEnd_4680415 : Nat := 4983230072969 + 3 ^ 40 * 4680415 * 2
def baseEnd_4680415 : Nat := 2403302557513410588487669

theorem tailTrace_4680415 : CollatzResearch.WordTrace tailWord_4680415 prefixEnd_4680415 2403302557513410588487669 := by
  unfold tailWord_4680415
  simp only [CollatzResearch.WordTrace]
  refine ⟨170708759338663281087506699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113805839559108854058337799 170708759338663281087506699)
  ·
    refine ⟨256063139007994921631260049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170708759338663281087506699 256063139007994921631260049)
    ·
      refine ⟨192047354255996191223445037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256063139007994921631260049 192047354255996191223445037)
      ·
        refine ⟨72017757845998571708791889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192047354255996191223445037 72017757845998571708791889)
        ·
          refine ⟨54013318384498928781593917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72017757845998571708791889 54013318384498928781593917)
          ·
            refine ⟨20254994394187098293097719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54013318384498928781593917 20254994394187098293097719)
            ·
              refine ⟨30382491591280647439646579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20254994394187098293097719 30382491591280647439646579)
              ·
                refine ⟨45573737386920971159469869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30382491591280647439646579 45573737386920971159469869)
                ·
                  refine ⟨17090151520095364184801201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45573737386920971159469869 17090151520095364184801201)
                  ·
                    refine ⟨12817613640071523138600901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17090151520095364184801201 12817613640071523138600901)
                    ·
                      refine ⟨2403302557513410588487669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12817613640071523138600901 2403302557513410588487669)
                      ·
                        rfl

theorem cell23_4680415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_4680415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680415 prefixEnd_4680415 := by exact prefixLift 4680415
  have htrace : WordTrace (prefixWord ++ tailWord_4680415) baseStart_4680415 baseEnd_4680415 := by
    simpa [prefixWord, tailWord_4680415, baseEnd_4680415] using wordTrace_append hprefix tailTrace_4680415
  have hstable : (prefixWord ++ tailWord_4680415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680415).length < 2 ^ (prefixWord ++ tailWord_4680415).sum := by decide
  have hdescent : baseEnd_4680415 < baseStart_4680415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680429 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_4680429 : Nat := 118140960795 + 4680429 * 2 ^ 59
def prefixEnd_4680429 : Nat := 4983230072969 + 3 ^ 40 * 4680429 * 2
def baseEnd_4680429 : Nat := 801103248747524511237535

theorem tailTrace_4680429 : CollatzResearch.WordTrace tailWord_4680429 prefixEnd_4680429 801103248747524511237535 := by
  unfold tailWord_4680429
  simp only [CollatzResearch.WordTrace]
  refine ⟨170709269960612561478516341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113806179973741707652344227 170709269960612561478516341)
  ·
    refine ⟨16003994058807427638610907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170709269960612561478516341 16003994058807427638610907)
    ·
      refine ⟨24005991088211141457916361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16003994058807427638610907 24005991088211141457916361)
      ·
        refine ⟨18004493316158356093437271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24005991088211141457916361 18004493316158356093437271)
        ·
          refine ⟨27006739974237534140155907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18004493316158356093437271 27006739974237534140155907)
          ·
            refine ⟨40510109961356301210233861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27006739974237534140155907 40510109961356301210233861)
            ·
              refine ⟨7595645617754306476918849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40510109961356301210233861 7595645617754306476918849)
              ·
                refine ⟨5696734213315729857689137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7595645617754306476918849 5696734213315729857689137)
                ·
                  refine ⟨4272550659986797393266853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5696734213315729857689137 4272550659986797393266853)
                  ·
                    refine ⟨801103248747524511237535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4272550659986797393266853 801103248747524511237535)
                    ·
                      rfl

theorem cell23_4680429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_4680429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680429 prefixEnd_4680429 := by exact prefixLift 4680429
  have htrace : WordTrace (prefixWord ++ tailWord_4680429) baseStart_4680429 baseEnd_4680429 := by
    simpa [prefixWord, tailWord_4680429, baseEnd_4680429] using wordTrace_append hprefix tailTrace_4680429
  have hstable : (prefixWord ++ tailWord_4680429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680429).length < 2 ^ (prefixWord ++ tailWord_4680429).sum := by decide
  have hdescent : baseEnd_4680429 < baseStart_4680429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680435 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 3]
def baseStart_4680435 : Nat := 118140960795 + 4680435 * 2 ^ 59
def prefixEnd_4680435 : Nat := 4983230072969 + 3 ^ 40 * 4680435 * 2
def baseEnd_4680435 : Nat := 2403312827126500510237577

theorem tailTrace_4680435 : CollatzResearch.WordTrace tailWord_4680435 prefixEnd_4680435 2403312827126500510237577 := by
  unfold tailWord_4680435
  simp only [CollatzResearch.WordTrace]
  refine ⟨170709488798590824503234759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113806325865727216335489839 170709488798590824503234759)
  ·
    refine ⟨256064233197886236754852139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170709488798590824503234759 256064233197886236754852139)
    ·
      refine ⟨384096349796829355132278209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256064233197886236754852139 384096349796829355132278209)
      ·
        refine ⟨288072262347622016349208657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384096349796829355132278209 288072262347622016349208657)
        ·
          refine ⟨216054196760716512261906493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288072262347622016349208657 216054196760716512261906493)
          ·
            refine ⟨81020323785268692098214935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216054196760716512261906493 81020323785268692098214935)
            ·
              refine ⟨121530485677903038147322403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81020323785268692098214935 121530485677903038147322403)
              ·
                refine ⟨182295728516854557220983605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121530485677903038147322403 182295728516854557220983605)
                ·
                  refine ⟨17090224548455114739467213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182295728516854557220983605 17090224548455114739467213)
                  ·
                    refine ⟨6408834205670668027300205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17090224548455114739467213 6408834205670668027300205)
                    ·
                      refine ⟨2403312827126500510237577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6408834205670668027300205 2403312827126500510237577)
                      ·
                        rfl

theorem cell23_4680435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_4680435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680435 prefixEnd_4680435 := by exact prefixLift 4680435
  have htrace : WordTrace (prefixWord ++ tailWord_4680435) baseStart_4680435 baseEnd_4680435 := by
    simpa [prefixWord, tailWord_4680435, baseEnd_4680435] using wordTrace_append hprefix tailTrace_4680435
  have hstable : (prefixWord ++ tailWord_4680435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680435).length < 2 ^ (prefixWord ++ tailWord_4680435).sum := by decide
  have hdescent : baseEnd_4680435 < baseStart_4680435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680485 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_4680485 : Nat := 118140960795 + 4680485 * 2 ^ 59
def prefixEnd_4680485 : Nat := 4983230072969 + 3 ^ 40 * 4680485 * 2
def baseEnd_4680485 : Nat := 801112833719741771537449

theorem tailTrace_4680485 : CollatzResearch.WordTrace tailWord_4680485 prefixEnd_4680485 801112833719741771537449 := by
  unfold tailWord_4680485
  simp only [CollatzResearch.WordTrace]
  refine ⟨170711312448409683042554909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113807541632273122028369939 170711312448409683042554909)
  ·
    refine ⟨64016742168153631140958091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170711312448409683042554909 64016742168153631140958091)
    ·
      refine ⟨96025113252230446711437137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64016742168153631140958091 96025113252230446711437137)
      ·
        refine ⟨72018834939172835033577853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96025113252230446711437137 72018834939172835033577853)
        ·
          refine ⟨27007063102189813137591695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72018834939172835033577853 27007063102189813137591695)
          ·
            refine ⟨40510594653284719706387543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27007063102189813137591695 40510594653284719706387543)
            ·
              refine ⟨60765891979927079559581315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40510594653284719706387543 60765891979927079559581315)
              ·
                refine ⟨91148837969890619339371973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60765891979927079559581315 91148837969890619339371973)
                ·
                  refine ⟨17090407119354491126132245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91148837969890619339371973 17090407119354491126132245)
                  ·
                    refine ⟨801112833719741771537449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17090407119354491126132245 801112833719741771537449)
                    ·
                      rfl

theorem cell23_4680485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_4680485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680485 prefixEnd_4680485 := by exact prefixLift 4680485
  have htrace : WordTrace (prefixWord ++ tailWord_4680485) baseStart_4680485 baseEnd_4680485 := by
    simpa [prefixWord, tailWord_4680485, baseEnd_4680485] using wordTrace_append hprefix tailTrace_4680485
  have hstable : (prefixWord ++ tailWord_4680485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680485).length < 2 ^ (prefixWord ++ tailWord_4680485).sum := by decide
  have hdescent : baseEnd_4680485 < baseStart_4680485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680515 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 7]
def baseStart_4680515 : Nat := 118140960795 + 4680515 * 2 ^ 59
def prefixEnd_4680515 : Nat := 4983230072969 + 3 ^ 40 * 4680515 * 2
def baseEnd_4680515 : Nat := 267039322842095577470801

theorem tailTrace_4680515 : CollatzResearch.WordTrace tailWord_4680515 prefixEnd_4680515 267039322842095577470801 := by
  unfold tailWord_4680515
  simp only [CollatzResearch.WordTrace]
  refine ⟨170712406638300998166146999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113808271092200665444097999 170712406638300998166146999)
  ·
    refine ⟨256068609957451497249220499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170712406638300998166146999 256068609957451497249220499)
    ·
      refine ⟨384102914936177245873830749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256068609957451497249220499 384102914936177245873830749)
      ·
        refine ⟨144038593101066467202686531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384102914936177245873830749 144038593101066467202686531)
        ·
          refine ⟨216057889651599700804029797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144038593101066467202686531 216057889651599700804029797)
          ·
            refine ⟨40510854309674943900755587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216057889651599700804029797 40510854309674943900755587)
            ·
              refine ⟨60766281464512415851133381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40510854309674943900755587 60766281464512415851133381)
              ·
                refine ⟨11393677774596077972087509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60766281464512415851133381 11393677774596077972087509)
                ·
                  refine ⟨267039322842095577470801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11393677774596077972087509 267039322842095577470801)
                  ·
                    rfl

theorem cell23_4680515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 7].length) (baseStart_4680515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680515 prefixEnd_4680515 := by exact prefixLift 4680515
  have htrace : WordTrace (prefixWord ++ tailWord_4680515) baseStart_4680515 baseEnd_4680515 := by
    simpa [prefixWord, tailWord_4680515, baseEnd_4680515] using wordTrace_append hprefix tailTrace_4680515
  have hstable : (prefixWord ++ tailWord_4680515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680515).length < 2 ^ (prefixWord ++ tailWord_4680515).sum := by decide
  have hdescent : baseEnd_4680515 < baseStart_4680515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680545 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 3, 7]
def baseStart_4680545 : Nat := 118140960795 + 4680545 * 2 ^ 59
def prefixEnd_4680545 : Nat := 4983230072969 + 3 ^ 40 * 4680545 * 2
def baseEnd_4680545 : Nat := 801123103332831693287357

theorem tailTrace_4680545 : CollatzResearch.WordTrace tailWord_4680545 prefixEnd_4680545 801123103332831693287357 := by
  unfold tailWord_4680545
  simp only [CollatzResearch.WordTrace]
  refine ⟨170713500828192313289739089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113809000552128208859826059 170713500828192313289739089)
  ·
    refine ⟨128035125621144234967304317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170713500828192313289739089 128035125621144234967304317)
    ·
      refine ⟨48013172107929088112739119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128035125621144234967304317 48013172107929088112739119)
      ·
        refine ⟨72019758161893632169108679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48013172107929088112739119 72019758161893632169108679)
        ·
          refine ⟨108029637242840448253663019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72019758161893632169108679 108029637242840448253663019)
          ·
            refine ⟨162044455864260672380494529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108029637242840448253663019 162044455864260672380494529)
            ·
              refine ⟨121533341898195504285370897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162044455864260672380494529 121533341898195504285370897)
              ·
                refine ⟨91150006423646628214028173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121533341898195504285370897 91150006423646628214028173)
                ·
                  refine ⟨34181252408867485580260565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91150006423646628214028173 34181252408867485580260565)
                  ·
                    refine ⟨801123103332831693287357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34181252408867485580260565 801123103332831693287357)
                    ·
                      rfl

theorem cell23_4680545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_4680545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680545 prefixEnd_4680545 := by exact prefixLift 4680545
  have htrace : WordTrace (prefixWord ++ tailWord_4680545) baseStart_4680545 baseEnd_4680545 := by
    simpa [prefixWord, tailWord_4680545, baseEnd_4680545] using wordTrace_append hprefix tailTrace_4680545
  have hstable : (prefixWord ++ tailWord_4680545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680545).length < 2 ^ (prefixWord ++ tailWord_4680545).sum := by decide
  have hdescent : baseEnd_4680545 < baseStart_4680545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680555 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7]
def baseStart_4680555 : Nat := 118140960795 + 4680555 * 2 ^ 59
def prefixEnd_4680555 : Nat := 4983230072969 + 3 ^ 40 * 4680555 * 2
def baseEnd_4680555 : Nat := 2403374444805040040737025

theorem tailTrace_4680555 : CollatzResearch.WordTrace tailWord_4680555 prefixEnd_4680555 2403374444805040040737025 := by
  unfold tailWord_4680555
  simp only [CollatzResearch.WordTrace]
  refine ⟨170713865558156084997603119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113809243705437389998402079 170713865558156084997603119)
  ·
    refine ⟨256070798337234127496404679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170713865558156084997603119 256070798337234127496404679)
    ·
      refine ⟨384106197505851191244607019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256070798337234127496404679 384106197505851191244607019)
      ·
        refine ⟨576159296258776786866910529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384106197505851191244607019 576159296258776786866910529)
        ·
          refine ⟨432119472194082590150182897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576159296258776786866910529 432119472194082590150182897)
          ·
            refine ⟨324089604145561942612637173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432119472194082590150182897 324089604145561942612637173)
            ·
              refine ⟨30383400388646432119934735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324089604145561942612637173 30383400388646432119934735)
              ·
                refine ⟨45575100582969648179902103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30383400388646432119934735 45575100582969648179902103)
                ·
                  refine ⟨68362650874454472269853155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45575100582969648179902103 68362650874454472269853155)
                  ·
                    refine ⟨102543976311681708404779733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68362650874454472269853155 102543976311681708404779733)
                    ·
                      refine ⟨2403374444805040040737025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102543976311681708404779733 2403374444805040040737025)
                      ·
                        rfl

theorem cell23_4680555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_4680555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680555 prefixEnd_4680555 := by exact prefixLift 4680555
  have htrace : WordTrace (prefixWord ++ tailWord_4680555) baseStart_4680555 baseEnd_4680555 := by
    simpa [prefixWord, tailWord_4680555, baseEnd_4680555] using wordTrace_append hprefix tailTrace_4680555
  have hstable : (prefixWord ++ tailWord_4680555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680555).length < 2 ^ (prefixWord ++ tailWord_4680555).sum := by decide
  have hdescent : baseEnd_4680555 < baseStart_4680555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680575 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 2, 8]
def baseStart_4680575 : Nat := 118140960795 + 4680575 * 2 ^ 59
def prefixEnd_4680575 : Nat := 4983230072969 + 3 ^ 40 * 4680575 * 2
def baseEnd_4680575 : Nat := 801128238139376654162311

theorem tailTrace_4680575 : CollatzResearch.WordTrace tailWord_4680575 prefixEnd_4680575 801128238139376654162311 := by
  unfold tailWord_4680575
  simp only [CollatzResearch.WordTrace]
  refine ⟨170714595018083628413331179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113809730012055752275554119 170714595018083628413331179)
  ·
    refine ⟨256071892527125442619996769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170714595018083628413331179 256071892527125442619996769)
    ·
      refine ⟨192053919395344081964997577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256071892527125442619996769 192053919395344081964997577)
      ·
        refine ⟨144040439546508061473748183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192053919395344081964997577 144040439546508061473748183)
        ·
          refine ⟨216060659319762092210622275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144040439546508061473748183 216060659319762092210622275)
          ·
            refine ⟨324090988979643138315933413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216060659319762092210622275 324090988979643138315933413)
            ·
              refine ⟨60767060433683088434237515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 324090988979643138315933413 60767060433683088434237515)
              ·
                refine ⟨91150590650524632651356273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60767060433683088434237515 91150590650524632651356273)
                ·
                  refine ⟨68362942987893474488517205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91150590650524632651356273 68362942987893474488517205)
                  ·
                    refine ⟨801128238139376654162311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68362942987893474488517205 801128238139376654162311)
                    ·
                      rfl

theorem cell23_4680575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_4680575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680575 prefixEnd_4680575 := by exact prefixLift 4680575
  have htrace : WordTrace (prefixWord ++ tailWord_4680575) baseStart_4680575 baseEnd_4680575 := by
    simpa [prefixWord, tailWord_4680575, baseEnd_4680575] using wordTrace_append hprefix tailTrace_4680575
  have hstable : (prefixWord ++ tailWord_4680575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680575).length < 2 ^ (prefixWord ++ tailWord_4680575).sum := by decide
  have hdescent : baseEnd_4680575 < baseStart_4680575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680599 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 2, 4, 2]
def baseStart_4680599 : Nat := 118140960795 + 4680599 * 2 ^ 59
def prefixEnd_4680599 : Nat := 4983230072969 + 3 ^ 40 * 4680599 * 2
def baseEnd_4680599 : Nat := 2403397037953837868586823

theorem tailTrace_4680599 : CollatzResearch.WordTrace tailWord_4680599 prefixEnd_4680599 2403397037953837868586823 := by
  unfold tailWord_4680599
  simp only [CollatzResearch.WordTrace]
  refine ⟨170715470369996680512204851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113810313579997787008136567 170715470369996680512204851)
  ·
    refine ⟨256073205554995020768307277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170715470369996680512204851 256073205554995020768307277)
    ·
      refine ⟨96027452083123132788115229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256073205554995020768307277 96027452083123132788115229)
      ·
        refine ⟨36010294531171174795543211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96027452083123132788115229 36010294531171174795543211)
        ·
          refine ⟨54015441796756762193314817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36010294531171174795543211 54015441796756762193314817)
          ·
            refine ⟨40511581347567571644986113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54015441796756762193314817 40511581347567571644986113)
            ·
              refine ⟨30383686010675678733739585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40511581347567571644986113 30383686010675678733739585)
              ·
                refine ⟨22787764508006759050304689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30383686010675678733739585 22787764508006759050304689)
                ·
                  refine ⟨17090823381005069287728517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22787764508006759050304689 17090823381005069287728517)
                  ·
                    refine ⟨3204529383938450491449097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17090823381005069287728517 3204529383938450491449097)
                    ·
                      refine ⟨2403397037953837868586823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204529383938450491449097 2403397037953837868586823)
                      ·
                        rfl

theorem cell23_4680599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_4680599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680599 prefixEnd_4680599 := by exact prefixLift 4680599
  have htrace : WordTrace (prefixWord ++ tailWord_4680599) baseStart_4680599 baseEnd_4680599 := by
    simpa [prefixWord, tailWord_4680599, baseEnd_4680599] using wordTrace_append hprefix tailTrace_4680599
  have hstable : (prefixWord ++ tailWord_4680599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680599).length < 2 ^ (prefixWord ++ tailWord_4680599).sum := by decide
  have hdescent : baseEnd_4680599 < baseStart_4680599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680666 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_4680666 : Nat := 118140960795 + 4680666 * 2 ^ 59
def prefixEnd_4680666 : Nat := 4983230072969 + 3 ^ 40 * 4680666 * 2
def baseEnd_4680666 : Nat := 2403431441157689106449015

theorem tailTrace_4680666 : CollatzResearch.WordTrace tailWord_4680666 prefixEnd_4680666 2403431441157689106449015 := by
  unfold tailWord_4680666
  simp only [CollatzResearch.WordTrace]
  refine ⟨42679478515188487738723463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113811942707169300636595901 42679478515188487738723463)
  ·
    refine ⟨64019217772782731608085195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42679478515188487738723463 64019217772782731608085195)
    ·
      refine ⟨96028826659174097412127793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64019217772782731608085195 96028826659174097412127793)
      ·
        refine ⟨72021619994380573059095845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96028826659174097412127793 72021619994380573059095845)
        ·
          refine ⟨13504053748946357448580471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72021619994380573059095845 13504053748946357448580471)
          ·
            refine ⟨20256080623419536172870707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13504053748946357448580471 20256080623419536172870707)
            ·
              refine ⟨30384120935129304259306061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20256080623419536172870707 30384120935129304259306061)
              ·
                refine ⟨11394045350673489097239773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30384120935129304259306061 11394045350673489097239773)
                ·
                  refine ⟨4272767006502558411464915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11394045350673489097239773 4272767006502558411464915)
                  ·
                    refine ⟨6409150509753837617197373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4272767006502558411464915 6409150509753837617197373)
                    ·
                      refine ⟨2403431441157689106449015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409150509753837617197373 2403431441157689106449015)
                      ·
                        rfl

theorem cell23_4680666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_4680666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680666 prefixEnd_4680666 := by exact prefixLift 4680666
  have htrace : WordTrace (prefixWord ++ tailWord_4680666) baseStart_4680666 baseEnd_4680666 := by
    simpa [prefixWord, tailWord_4680666, baseEnd_4680666] using wordTrace_append hprefix tailTrace_4680666
  have hstable : (prefixWord ++ tailWord_4680666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680666).length < 2 ^ (prefixWord ++ tailWord_4680666).sum := by decide
  have hdescent : baseEnd_4680666 < baseStart_4680666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680700 : List Nat := [2, 2, 2, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_4680700 : Nat := 118140960795 + 4680700 * 2 ^ 59
def prefixEnd_4680700 : Nat := 4983230072969 + 3 ^ 40 * 4680700 * 2
def baseEnd_4680700 : Nat := 2403448899499941973423859

theorem tailTrace_4680700 : CollatzResearch.WordTrace tailWord_4680700 prefixEnd_4680700 2403448899499941973423859 := by
  unfold tailWord_4680700
  simp only [CollatzResearch.WordTrace]
  refine ⟨85359577071315387380815777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113812769428420516507754369 85359577071315387380815777)
  ·
    refine ⟨64019682803486540535611833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85359577071315387380815777 64019682803486540535611833)
    ·
      refine ⟨48014762102614905401708875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64019682803486540535611833 48014762102614905401708875)
      ·
        refine ⟨72022143153922358102563313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48014762102614905401708875 72022143153922358102563313)
        ·
          refine ⟨54016607365441768576922485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72022143153922358102563313 54016607365441768576922485)
          ·
            refine ⟨5064056940510165804086483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54016607365441768576922485 5064056940510165804086483)
            ·
              refine ⟨7596085410765248706129725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5064056940510165804086483 7596085410765248706129725)
              ·
                refine ⟨2848532029036968264798647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7596085410765248706129725 2848532029036968264798647)
                ·
                  refine ⟨4272798043555452397197971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848532029036968264798647 4272798043555452397197971)
                  ·
                    refine ⟨6409197065333178595796957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4272798043555452397197971 6409197065333178595796957)
                    ·
                      refine ⟨2403448899499941973423859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409197065333178595796957 2403448899499941973423859)
                      ·
                        rfl

theorem cell23_4680700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_4680700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680700 prefixEnd_4680700 := by exact prefixLift 4680700
  have htrace : WordTrace (prefixWord ++ tailWord_4680700) baseStart_4680700 baseEnd_4680700 := by
    simpa [prefixWord, tailWord_4680700, baseEnd_4680700] using wordTrace_append hprefix tailTrace_4680700
  have hstable : (prefixWord ++ tailWord_4680700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680700).length < 2 ^ (prefixWord ++ tailWord_4680700).sum := by decide
  have hdescent : baseEnd_4680700 < baseStart_4680700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680709 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_4680709 : Nat := 118140960795 + 4680709 * 2 ^ 59
def prefixEnd_4680709 : Nat := 4983230072969 + 3 ^ 40 * 4680709 * 2
def baseEnd_4680709 : Nat := 2403453520825832438211317

theorem tailTrace_4680709 : CollatzResearch.WordTrace tailWord_4680709 prefixEnd_4680709 2403453520825832438211317 := by
  unfold tailWord_4680709
  simp only [CollatzResearch.WordTrace]
  refine ⟨170719482399598169298709181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113812988266398779532472787 170719482399598169298709181)
  ·
    refine ⟨64019805899849313487015943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170719482399598169298709181 64019805899849313487015943)
    ·
      refine ⟨96029708849773970230523915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64019805899849313487015943 96029708849773970230523915)
      ·
        refine ⟨144044563274660955345785873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96029708849773970230523915 144044563274660955345785873)
        ·
          refine ⟨108033422455995716509339405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144044563274660955345785873 108033422455995716509339405)
          ·
            refine ⟨40512533420998393691002277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108033422455995716509339405 40512533420998393691002277)
            ·
              refine ⟨7596100016437198817062927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40512533420998393691002277 7596100016437198817062927)
              ·
                refine ⟨11394150024655798225594391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7596100016437198817062927 11394150024655798225594391)
                ·
                  refine ⟨17091225036983697338391587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11394150024655798225594391 17091225036983697338391587)
                  ·
                    refine ⟨25636837555475546007587381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17091225036983697338391587 25636837555475546007587381)
                    ·
                      refine ⟨2403453520825832438211317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25636837555475546007587381 2403453520825832438211317)
                      ·
                        rfl

theorem cell23_4680709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_4680709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680709 prefixEnd_4680709 := by exact prefixLift 4680709
  have htrace : WordTrace (prefixWord ++ tailWord_4680709) baseStart_4680709 baseEnd_4680709 := by
    simpa [prefixWord, tailWord_4680709, baseEnd_4680709] using wordTrace_append hprefix tailTrace_4680709
  have hstable : (prefixWord ++ tailWord_4680709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680709).length < 2 ^ (prefixWord ++ tailWord_4680709).sum := by decide
  have hdescent : baseEnd_4680709 < baseStart_4680709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680712 : List Nat := [2, 1, 3, 2, 1, 3, 11]
def baseStart_4680712 : Nat := 118140960795 + 4680712 * 2 ^ 59
def prefixEnd_4680712 : Nat := 4983230072969 + 3 ^ 40 * 4680712 * 2
def baseEnd_4680712 : Nat := 29672284707009826252763

theorem tailTrace_4680712 : CollatzResearch.WordTrace tailWord_4680712 prefixEnd_4680712 29672284707009826252763 := by
  unfold tailWord_4680712
  simp only [CollatzResearch.WordTrace]
  refine ⟨85359795909293650405534195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113813061212391533874045593 85359795909293650405534195)
  ·
    refine ⟨128039693863940475608301293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85359795909293650405534195 128039693863940475608301293)
    ·
      refine ⟨48014885198977678353112985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128039693863940475608301293 48014885198977678353112985)
      ·
        refine ⟨36011163899233258764834739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48014885198977678353112985 36011163899233258764834739)
        ·
          refine ⟨54016745848849888147252109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36011163899233258764834739 54016745848849888147252109)
          ·
            refine ⟨20256279693318708055219541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54016745848849888147252109 20256279693318708055219541)
            ·
              refine ⟨29672284707009826252763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20256279693318708055219541 29672284707009826252763)
              ·
                rfl

theorem cell23_4680712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 11].length) (baseStart_4680712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680712 prefixEnd_4680712 := by exact prefixLift 4680712
  have htrace : WordTrace (prefixWord ++ tailWord_4680712) baseStart_4680712 baseEnd_4680712 := by
    simpa [prefixWord, tailWord_4680712, baseEnd_4680712] using wordTrace_append hprefix tailTrace_4680712
  have hstable : (prefixWord ++ tailWord_4680712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680712).length < 2 ^ (prefixWord ++ tailWord_4680712).sum := by decide
  have hdescent : baseEnd_4680712 < baseStart_4680712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680733 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_4680733 : Nat := 118140960795 + 4680733 * 2 ^ 59
def prefixEnd_4680733 : Nat := 4983230072969 + 3 ^ 40 * 4680733 * 2
def baseEnd_4680733 : Nat := 801155281453846781437069

theorem tailTrace_4680733 : CollatzResearch.WordTrace tailWord_4680733 prefixEnd_4680733 801155281453846781437069 := by
  unfold tailWord_4680733
  simp only [CollatzResearch.WordTrace]
  refine ⟨170720357751511221397582853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113813571834340814265055235 170720357751511221397582853)
  ·
    refine ⟨32010067078408354012046785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170720357751511221397582853 32010067078408354012046785)
    ·
      refine ⟨24007550308806265509035089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32010067078408354012046785 24007550308806265509035089)
      ·
        refine ⟨18005662731604699131776317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24007550308806265509035089 18005662731604699131776317)
        ·
          refine ⟨6752123524351762174416119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18005662731604699131776317 6752123524351762174416119)
          ·
            refine ⟨10128185286527643261624179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6752123524351762174416119 10128185286527643261624179)
            ·
              refine ⟨15192277929791464892436269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10128185286527643261624179 15192277929791464892436269)
              ·
                refine ⟨5697104223671799334663601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15192277929791464892436269 5697104223671799334663601)
                ·
                  refine ⟨4272828167753849500997701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5697104223671799334663601 4272828167753849500997701)
                  ·
                    refine ⟨801155281453846781437069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4272828167753849500997701 801155281453846781437069)
                    ·
                      rfl

theorem cell23_4680733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_4680733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680733 prefixEnd_4680733 := by exact prefixLift 4680733
  have htrace : WordTrace (prefixWord ++ tailWord_4680733) baseStart_4680733 baseEnd_4680733 := by
    simpa [prefixWord, tailWord_4680733, baseEnd_4680733] using wordTrace_append hprefix tailTrace_4680733
  have hstable : (prefixWord ++ tailWord_4680733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680733).length < 2 ^ (prefixWord ++ tailWord_4680733).sum := by decide
  have hdescent : baseEnd_4680733 < baseStart_4680733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680743 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4680743 : Nat := 118140960795 + 4680743 * 2 ^ 59
def prefixEnd_4680743 : Nat := 4983230072969 + 3 ^ 40 * 4680743 * 2
def baseEnd_4680743 : Nat := 2403470979168085305186161

theorem tailTrace_4680743 : CollatzResearch.WordTrace tailWord_4680743 prefixEnd_4680743 2403470979168085305186161 := by
  unfold tailWord_4680743
  simp only [CollatzResearch.WordTrace]
  refine ⟨170720722481474993105446883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113813814987649995403631255 170720722481474993105446883)
  ·
    refine ⟨256081083722212489658170325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170720722481474993105446883 256081083722212489658170325)
    ·
      refine ⟨6001900399739355226363367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 256081083722212489658170325 6001900399739355226363367)
      ·
        refine ⟨9002850599609032839545051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6001900399739355226363367 9002850599609032839545051)
        ·
          refine ⟨13504275899413549259317577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9002850599609032839545051 13504275899413549259317577)
          ·
            refine ⟨10128206924560161944488183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13504275899413549259317577 10128206924560161944488183)
            ·
              refine ⟨15192310386840242916732275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10128206924560161944488183 15192310386840242916732275)
              ·
                refine ⟨22788465580260364375098413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15192310386840242916732275 22788465580260364375098413)
                ·
                  refine ⟨8545674592597636640661905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22788465580260364375098413 8545674592597636640661905)
                  ·
                    refine ⟨6409255944448227480496429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8545674592597636640661905 6409255944448227480496429)
                    ·
                      refine ⟨2403470979168085305186161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409255944448227480496429 2403470979168085305186161)
                      ·
                        rfl

theorem cell23_4680743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4680743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680743 prefixEnd_4680743 := by exact prefixLift 4680743
  have htrace : WordTrace (prefixWord ++ tailWord_4680743) baseStart_4680743 baseEnd_4680743 := by
    simpa [prefixWord, tailWord_4680743, baseEnd_4680743] using wordTrace_append hprefix tailTrace_4680743
  have hstable : (prefixWord ++ tailWord_4680743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680743).length < 2 ^ (prefixWord ++ tailWord_4680743).sum := by decide
  have hdescent : baseEnd_4680743 < baseStart_4680743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680774 : List Nat := [6, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_4680774 : Nat := 118140960795 + 4680774 * 2 ^ 59
def prefixEnd_4680774 : Nat := 4983230072969 + 3 ^ 40 * 4680774 * 2
def baseEnd_4680774 : Nat := 2403486897068374683898519

theorem tailTrace_4680774 : CollatzResearch.WordTrace tailWord_4680774 prefixEnd_4680774 2403486897068374683898519 := by
  unfold tailWord_4680774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335057910761333918744543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113814568762908456933216917 5335057910761333918744543)
  ·
    refine ⟨8002586866142000878116815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5335057910761333918744543 8002586866142000878116815)
    ·
      refine ⟨12003880299213001317175223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8002586866142000878116815 12003880299213001317175223)
      ·
        refine ⟨18005820448819501975762835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12003880299213001317175223 18005820448819501975762835)
        ·
          refine ⟨27008730673229252963644253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18005820448819501975762835 27008730673229252963644253)
          ·
            refine ⟨10128274002460969861366595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27008730673229252963644253 10128274002460969861366595)
            ·
              refine ⟨15192411003691454792049893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10128274002460969861366595 15192411003691454792049893)
              ·
                refine ⟨2848577063192147773509355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15192411003691454792049893 2848577063192147773509355)
                ·
                  refine ⟨4272865594788221660264033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848577063192147773509355 4272865594788221660264033)
                  ·
                    refine ⟨3204649196091166245198025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4272865594788221660264033 3204649196091166245198025)
                    ·
                      refine ⟨2403486897068374683898519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204649196091166245198025 2403486897068374683898519)
                      ·
                        rfl

theorem cell23_4680774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_4680774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680774 prefixEnd_4680774 := by exact prefixLift 4680774
  have htrace : WordTrace (prefixWord ++ tailWord_4680774) baseStart_4680774 baseEnd_4680774 := by
    simpa [prefixWord, tailWord_4680774, baseEnd_4680774] using wordTrace_append hprefix tailTrace_4680774
  have hstable : (prefixWord ++ tailWord_4680774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680774).length < 2 ^ (prefixWord ++ tailWord_4680774).sum := by decide
  have hdescent : baseEnd_4680774 < baseStart_4680774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680789 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_4680789 : Nat := 118140960795 + 4680789 * 2 ^ 59
def prefixEnd_4680789 : Nat := 4983230072969 + 3 ^ 40 * 4680789 * 2
def baseEnd_4680789 : Nat := 801164866426064041736983

theorem tailTrace_4680789 : CollatzResearch.WordTrace tailWord_4680789 prefixEnd_4680789 801164866426064041736983 := by
  unfold tailWord_4680789
  simp only [CollatzResearch.WordTrace]
  refine ⟨170722400239308342961621421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113814933492872228641080947 170722400239308342961621421)
  ·
    refine ⟨64020900089740628610608033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170722400239308342961621421 64020900089740628610608033)
    ·
      refine ⟨48015675067305471457956025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64020900089740628610608033 48015675067305471457956025)
      ·
        refine ⟨36011756300479103593467019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48015675067305471457956025 36011756300479103593467019)
        ·
          refine ⟨54017634450718655390200529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36011756300479103593467019 54017634450718655390200529)
          ·
            refine ⟨40513225838038991542650397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54017634450718655390200529 40513225838038991542650397)
            ·
              refine ⟨15192459689264621828493899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40513225838038991542650397 15192459689264621828493899)
              ·
                refine ⟨22788689533896932742740849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15192459689264621828493899 22788689533896932742740849)
                ·
                  refine ⟨17091517150422699557055637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22788689533896932742740849 17091517150422699557055637)
                  ·
                    refine ⟨801164866426064041736983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17091517150422699557055637 801164866426064041736983)
                    ·
                      rfl

theorem cell23_4680789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_4680789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680789 prefixEnd_4680789 := by exact prefixLift 4680789
  have htrace : WordTrace (prefixWord ++ tailWord_4680789) baseStart_4680789 baseEnd_4680789 := by
    simpa [prefixWord, tailWord_4680789, baseEnd_4680789] using wordTrace_append hprefix tailTrace_4680789
  have hstable : (prefixWord ++ tailWord_4680789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680789).length < 2 ^ (prefixWord ++ tailWord_4680789).sum := by decide
  have hdescent : baseEnd_4680789 < baseStart_4680789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680799 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 3]
def baseStart_4680799 : Nat := 118140960795 + 4680799 * 2 ^ 59
def prefixEnd_4680799 : Nat := 4983230072969 + 3 ^ 40 * 4680799 * 2
def baseEnd_4680799 : Nat := 2403499734084737086085903

theorem tailTrace_4680799 : CollatzResearch.WordTrace tailWord_4680799 prefixEnd_4680799 2403499734084737086085903 := by
  unfold tailWord_4680799
  simp only [CollatzResearch.WordTrace]
  refine ⟨170722764969272114669485451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113815176646181409779656967 170722764969272114669485451)
  ·
    refine ⟨256084147453908172004228177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170722764969272114669485451 256084147453908172004228177)
    ·
      refine ⟨192063110590431129003171133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256084147453908172004228177 192063110590431129003171133)
      ·
        refine ⟨72023666471411673376189175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192063110590431129003171133 72023666471411673376189175)
        ·
          refine ⟨108035499707117510064283763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72023666471411673376189175 108035499707117510064283763)
          ·
            refine ⟨162053249560676265096425645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108035499707117510064283763 162053249560676265096425645)
            ·
              refine ⟨60769968585253599411159617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162053249560676265096425645 60769968585253599411159617)
              ·
                refine ⟨45577476438940199558369713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60769968585253599411159617 45577476438940199558369713)
                ·
                  refine ⟨34183107329205149668777285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45577476438940199558369713 34183107329205149668777285)
                  ·
                    refine ⟨6409332624225965562895741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34183107329205149668777285 6409332624225965562895741)
                    ·
                      refine ⟨2403499734084737086085903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409332624225965562895741 2403499734084737086085903)
                      ·
                        rfl

theorem cell23_4680799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_4680799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680799 prefixEnd_4680799 := by exact prefixLift 4680799
  have htrace : WordTrace (prefixWord ++ tailWord_4680799) baseStart_4680799 baseEnd_4680799 := by
    simpa [prefixWord, tailWord_4680799, baseEnd_4680799] using wordTrace_append hprefix tailTrace_4680799
  have hstable : (prefixWord ++ tailWord_4680799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680799).length < 2 ^ (prefixWord ++ tailWord_4680799).sum := by decide
  have hdescent : baseEnd_4680799 < baseStart_4680799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680813 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_4680813 : Nat := 118140960795 + 4680813 * 2 ^ 59
def prefixEnd_4680813 : Nat := 4983230072969 + 3 ^ 40 * 4680813 * 2
def baseEnd_4680813 : Nat := 2403506922813900031310839

theorem tailTrace_4680813 : CollatzResearch.WordTrace tailWord_4680813 prefixEnd_4680813 2403506922813900031310839 := by
  unfold tailWord_4680813
  simp only [CollatzResearch.WordTrace]
  refine ⟨170723275591221395060495093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113815517060814263373663395 170723275591221395060495093)
  ·
    refine ⟨16005307086677005786921415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170723275591221395060495093 16005307086677005786921415)
    ·
      refine ⟨24007960630015508680382123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16005307086677005786921415 24007960630015508680382123)
      ·
        refine ⟨36011940945023263020573185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24007960630015508680382123 36011940945023263020573185)
        ·
          refine ⟨27008955708767447265429889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36011940945023263020573185 27008955708767447265429889)
          ·
            refine ⟨20256716781575585449072417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27008955708767447265429889 20256716781575585449072417)
            ·
              refine ⟨15192537586181689086804313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20256716781575585449072417 15192537586181689086804313)
              ·
                refine ⟨11394403189636266815103235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15192537586181689086804313 11394403189636266815103235)
                ·
                  refine ⟨17091604784454400222654853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11394403189636266815103235 17091604784454400222654853)
                  ·
                    refine ⟨3204675897085200041747785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17091604784454400222654853 3204675897085200041747785)
                    ·
                      refine ⟨2403506922813900031310839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204675897085200041747785 2403506922813900031310839)
                      ·
                        rfl

theorem cell23_4680813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_4680813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680813 prefixEnd_4680813 := by exact prefixLift 4680813
  have htrace : WordTrace (prefixWord ++ tailWord_4680813) baseStart_4680813 baseEnd_4680813 := by
    simpa [prefixWord, tailWord_4680813, baseEnd_4680813] using wordTrace_append hprefix tailTrace_4680813
  have hstable : (prefixWord ++ tailWord_4680813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680813).length < 2 ^ (prefixWord ++ tailWord_4680813).sum := by decide
  have hdescent : baseEnd_4680813 < baseStart_4680813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680836 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 7]
def baseStart_4680836 : Nat := 118140960795 + 4680836 * 2 ^ 59
def prefixEnd_4680836 : Nat := 4983230072969 + 3 ^ 40 * 4680836 * 2
def baseEnd_4680836 : Nat := 267057636985439271258137

theorem tailTrace_4680836 : CollatzResearch.WordTrace tailWord_4680836 prefixEnd_4680836 267057636985439271258137 := by
  unfold tailWord_4680836
  simp only [CollatzResearch.WordTrace]
  refine ⟨85362057235069034994291181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113816076313425379992388241 85362057235069034994291181)
  ·
    refine ⟨32010771463150888122859193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85362057235069034994291181 32010771463150888122859193)
    ·
      refine ⟨24008078597363166092144395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32010771463150888122859193 24008078597363166092144395)
      ·
        refine ⟨36012117896044749138216593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24008078597363166092144395 36012117896044749138216593)
        ·
          refine ⟨27009088422033561853662445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36012117896044749138216593 27009088422033561853662445)
          ·
            refine ⟨10128408158262585695123417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27009088422033561853662445 10128408158262585695123417)
            ·
              refine ⟨7596306118696939271342563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10128408158262585695123417 7596306118696939271342563)
              ·
                refine ⟨11394459178045408907013845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7596306118696939271342563 11394459178045408907013845)
                ·
                  refine ⟨267057636985439271258137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11394459178045408907013845 267057636985439271258137)
                  ·
                    rfl

theorem cell23_4680836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_4680836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680836 prefixEnd_4680836 := by exact prefixLift 4680836
  have htrace : WordTrace (prefixWord ++ tailWord_4680836) baseStart_4680836 baseEnd_4680836 := by
    simpa [prefixWord, tailWord_4680836, baseEnd_4680836] using wordTrace_append hprefix tailTrace_4680836
  have hstable : (prefixWord ++ tailWord_4680836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680836).length < 2 ^ (prefixWord ++ tailWord_4680836).sum := by decide
  have hdescent : baseEnd_4680836 < baseStart_4680836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680898 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_4680898 : Nat := 118140960795 + 4680898 * 2 ^ 59
def prefixEnd_4680898 : Nat := 4983230072969 + 3 ^ 40 * 4680898 * 2
def baseEnd_4680898 : Nat := 2403550568669532198747949

theorem tailTrace_4680898 : CollatzResearch.WordTrace tailWord_4680898 prefixEnd_4680898 2403550568669532198747949 := by
  unfold tailWord_4680898
  simp only [CollatzResearch.WordTrace]
  refine ⟨42681593948978363644334837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113817583863942303051559565 42681593948978363644334837)
  ·
    refine ⟨4001399432716721591656391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42681593948978363644334837 4001399432716721591656391)
    ·
      refine ⟨6002099149075082387484587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4001399432716721591656391 6002099149075082387484587)
      ·
        refine ⟨9003148723612623581226881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6002099149075082387484587 9003148723612623581226881)
        ·
          refine ⟨6752361542709467685920161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9003148723612623581226881 6752361542709467685920161)
          ·
            refine ⟨5064271157032100764440121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6752361542709467685920161 5064271157032100764440121)
            ·
              refine ⟨3798203367774075573330091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5064271157032100764440121 3798203367774075573330091)
              ·
                refine ⟨5697305051661113359995137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3798203367774075573330091 5697305051661113359995137)
                ·
                  refine ⟨4272978788745835019996353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5697305051661113359995137 4272978788745835019996353)
                  ·
                    refine ⟨3204734091559376264997265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4272978788745835019996353 3204734091559376264997265)
                    ·
                      refine ⟨2403550568669532198747949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204734091559376264997265 2403550568669532198747949)
                      ·
                        rfl

theorem cell23_4680898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_4680898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680898 prefixEnd_4680898 := by exact prefixLift 4680898
  have htrace : WordTrace (prefixWord ++ tailWord_4680898) baseStart_4680898 baseEnd_4680898 := by
    simpa [prefixWord, tailWord_4680898, baseEnd_4680898] using wordTrace_append hprefix tailTrace_4680898
  have hstable : (prefixWord ++ tailWord_4680898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680898).length < 2 ^ (prefixWord ++ tailWord_4680898).sum := by decide
  have hdescent : baseEnd_4680898 < baseStart_4680898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680899 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4]
def baseStart_4680899 : Nat := 118140960795 + 4680899 * 2 ^ 59
def prefixEnd_4680899 : Nat := 4983230072969 + 3 ^ 40 * 4680899 * 2
def baseEnd_4680899 : Nat := 2403551082150186694835443

theorem tailTrace_4680899 : CollatzResearch.WordTrace tailWord_4680899 prefixEnd_4680899 2403551082150186694835443 := by
  unfold tailWord_4680899
  simp only [CollatzResearch.WordTrace]
  refine ⟨170726412268909831748125751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113817608179273221165417167 170726412268909831748125751)
  ·
    refine ⟨256089618403364747622188627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170726412268909831748125751 256089618403364747622188627)
    ·
      refine ⟨384134427605047121433282941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256089618403364747622188627 384134427605047121433282941)
      ·
        refine ⟨144050410351892670537481103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384134427605047121433282941 144050410351892670537481103)
        ·
          refine ⟨216075615527839005806221655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144050410351892670537481103 216075615527839005806221655)
          ·
            refine ⟨324113423291758508709332483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216075615527839005806221655 324113423291758508709332483)
            ·
              refine ⟨486170134937637763063998725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324113423291758508709332483 486170134937637763063998725)
              ·
                refine ⟨91156900300807080574499761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 486170134937637763063998725 91156900300807080574499761)
                ·
                  refine ⟨68367675225605310430874821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91156900300807080574499761 68367675225605310430874821)
                  ·
                    refine ⟨12818939104800995705789029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68367675225605310430874821 12818939104800995705789029)
                    ·
                      refine ⟨2403551082150186694835443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12818939104800995705789029 2403551082150186694835443)
                      ·
                        rfl

theorem cell23_4680899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_4680899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680899 prefixEnd_4680899 := by exact prefixLift 4680899
  have htrace : WordTrace (prefixWord ++ tailWord_4680899) baseStart_4680899 baseEnd_4680899 := by
    simpa [prefixWord, tailWord_4680899, baseEnd_4680899] using wordTrace_append hprefix tailTrace_4680899
  have hstable : (prefixWord ++ tailWord_4680899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680899).length < 2 ^ (prefixWord ++ tailWord_4680899).sum := by decide
  have hdescent : baseEnd_4680899 < baseStart_4680899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680943 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 6]
def baseStart_4680943 : Nat := 118140960795 + 4680943 * 2 ^ 59
def prefixEnd_4680943 : Nat := 4983230072969 + 3 ^ 40 * 4680943 * 2
def baseEnd_4680943 : Nat := 267063741699887169187249

theorem tailTrace_4680943 : CollatzResearch.WordTrace tailWord_4680943 prefixEnd_4680943 267063741699887169187249 := by
  unfold tailWord_4680943
  simp only [CollatzResearch.WordTrace]
  refine ⟨170728017080750427262727483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113818678053833618175151655 170728017080750427262727483)
  ·
    refine ⟨256092025621125640894091225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170728017080750427262727483 256092025621125640894091225)
    ·
      refine ⟨192069019215844230670568419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256092025621125640894091225 192069019215844230670568419)
      ·
        refine ⟨288103528823766346005852629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192069019215844230670568419 288103528823766346005852629)
        ·
          refine ⟨6752426456807023734512171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 288103528823766346005852629 6752426456807023734512171)
          ·
            refine ⟨10128639685210535601768257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6752426456807023734512171 10128639685210535601768257)
            ·
              refine ⟨7596479763907901701326193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10128639685210535601768257 7596479763907901701326193)
              ·
                refine ⟨5697359822930926275994645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7596479763907901701326193 5697359822930926275994645)
                ·
                  refine ⟨267063741699887169187249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5697359822930926275994645 267063741699887169187249)
                  ·
                    rfl

theorem cell23_4680943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 6].length) (baseStart_4680943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680943 prefixEnd_4680943 := by exact prefixLift 4680943
  have htrace : WordTrace (prefixWord ++ tailWord_4680943) baseStart_4680943 baseEnd_4680943 := by
    simpa [prefixWord, tailWord_4680943, baseEnd_4680943] using wordTrace_append hprefix tailTrace_4680943
  have hstable : (prefixWord ++ tailWord_4680943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680943).length < 2 ^ (prefixWord ++ tailWord_4680943).sum := by decide
  have hdescent : baseEnd_4680943 < baseStart_4680943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680947 : List Nat := [1, 1, 1, 2, 2, 7, 2, 2, 1, 4]
def baseStart_4680947 : Nat := 118140960795 + 4680947 * 2 ^ 59
def prefixEnd_4680947 : Nat := 4983230072969 + 3 ^ 40 * 4680947 * 2
def baseEnd_4680947 : Nat := 801191909740534169011741

theorem tailTrace_4680947 : CollatzResearch.WordTrace tailWord_4680947 prefixEnd_4680947 801191909740534169011741 := by
  unfold tailWord_4680947
  simp only [CollatzResearch.WordTrace]
  refine ⟨170728162972735935945873095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113818775315157290630582063 170728162972735935945873095)
  ·
    refine ⟨256092244459103903918809643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170728162972735935945873095 256092244459103903918809643)
    ·
      refine ⟨384138366688655855878214465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256092244459103903918809643 384138366688655855878214465)
      ·
        refine ⟨288103775016491891908660849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384138366688655855878214465 288103775016491891908660849)
        ·
          refine ⟨216077831262368918931495637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288103775016491891908660849 216077831262368918931495637)
          ·
            refine ⟨5064324170211771537456929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 216077831262368918931495637 5064324170211771537456929)
            ·
              refine ⟨3798243127658828653092697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5064324170211771537456929 3798243127658828653092697)
              ·
                refine ⟨2848682345744121489819523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3798243127658828653092697 2848682345744121489819523)
                ·
                  refine ⟨4273023518616182234729285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848682345744121489819523 4273023518616182234729285)
                  ·
                    refine ⟨801191909740534169011741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273023518616182234729285 801191909740534169011741)
                    ·
                      rfl

theorem cell23_4680947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 4].length) (baseStart_4680947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680947 prefixEnd_4680947 := by exact prefixLift 4680947
  have htrace : WordTrace (prefixWord ++ tailWord_4680947) baseStart_4680947 baseEnd_4680947 := by
    simpa [prefixWord, tailWord_4680947, baseEnd_4680947] using wordTrace_append hprefix tailTrace_4680947
  have hstable : (prefixWord ++ tailWord_4680947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680947).length < 2 ^ (prefixWord ++ tailWord_4680947).sum := by decide
  have hdescent : baseEnd_4680947 < baseStart_4680947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4680953 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 3]
def baseStart_4680953 : Nat := 118140960795 + 4680953 * 2 ^ 59
def prefixEnd_4680953 : Nat := 4983230072969 + 3 ^ 40 * 4680953 * 2
def baseEnd_4680953 : Nat := 2403578810105529483560195

theorem tailTrace_4680953 : CollatzResearch.WordTrace tailWord_4680953 prefixEnd_4680953 2403578810105529483560195 := by
  unfold tailWord_4680953
  simp only [CollatzResearch.WordTrace]
  refine ⟨170728381810714198970591513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113818921207142799313727675 170728381810714198970591513)
  ·
    refine ⟨128046286358035649227943635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170728381810714198970591513 128046286358035649227943635)
    ·
      refine ⟨192069429537053473841915453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128046286358035649227943635 192069429537053473841915453)
      ·
        refine ⟨72026036076395052690718295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192069429537053473841915453 72026036076395052690718295)
        ·
          refine ⟨108039054114592579036077443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72026036076395052690718295 108039054114592579036077443)
          ·
            refine ⟨162058581171888868554116165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108039054114592579036077443 162058581171888868554116165)
            ·
              refine ⟨30385983969729162853896781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162058581171888868554116165 30385983969729162853896781)
              ·
                refine ⟨11394743988648436070211293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30385983969729162853896781 11394743988648436070211293)
                ·
                  refine ⟨4273028995743163526329235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11394743988648436070211293 4273028995743163526329235)
                  ·
                    refine ⟨6409543493614745289493853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273028995743163526329235 6409543493614745289493853)
                    ·
                      refine ⟨2403578810105529483560195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409543493614745289493853 2403578810105529483560195)
                      ·
                        rfl

theorem cell23_4680953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_4680953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4680953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4680953 prefixEnd_4680953 := by exact prefixLift 4680953
  have htrace : WordTrace (prefixWord ++ tailWord_4680953) baseStart_4680953 baseEnd_4680953 := by
    simpa [prefixWord, tailWord_4680953, baseEnd_4680953] using wordTrace_append hprefix tailTrace_4680953
  have hstable : (prefixWord ++ tailWord_4680953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4680953).length < 2 ^ (prefixWord ++ tailWord_4680953).sum := by decide
  have hdescent : baseEnd_4680953 < baseStart_4680953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4680953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681013 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4681013 : Nat := 118140960795 + 4681013 * 2 ^ 59
def prefixEnd_4681013 : Nat := 4983230072969 + 3 ^ 40 * 4681013 * 2
def baseEnd_4681013 : Nat := 2403609618944799248809919

theorem tailTrace_4681013 : CollatzResearch.WordTrace tailWord_4681013 prefixEnd_4681013 2403609618944799248809919 := by
  unfold tailWord_4681013
  simp only [CollatzResearch.WordTrace]
  refine ⟨170730570190496829217775693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113820380126997886145183795 170730570190496829217775693)
  ·
    refine ⟨64023963821436310956665885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170730570190496829217775693 64023963821436310956665885)
    ·
      refine ⟨24008986433038616608749707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64023963821436310956665885 24008986433038616608749707)
      ·
        refine ⟨36013479649557924913124561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24008986433038616608749707 36013479649557924913124561)
        ·
          refine ⟨27010109737168443684843421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36013479649557924913124561 27010109737168443684843421)
          ·
            refine ⟨10128791151438166381816283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27010109737168443684843421 10128791151438166381816283)
            ·
              refine ⟨15193186727157249572724425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10128791151438166381816283 15193186727157249572724425)
              ·
                refine ⟨11394890045367937179543319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15193186727157249572724425 11394890045367937179543319)
                ·
                  refine ⟨17092335068051905769314979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11394890045367937179543319 17092335068051905769314979)
                  ·
                    refine ⟨25638502602077858653972469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17092335068051905769314979 25638502602077858653972469)
                    ·
                      refine ⟨2403609618944799248809919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25638502602077858653972469 2403609618944799248809919)
                      ·
                        rfl

theorem cell23_4681013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4681013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681013 prefixEnd_4681013 := by exact prefixLift 4681013
  have htrace : WordTrace (prefixWord ++ tailWord_4681013) baseStart_4681013 baseEnd_4681013 := by
    simpa [prefixWord, tailWord_4681013, baseEnd_4681013] using wordTrace_append hprefix tailTrace_4681013
  have hstable : (prefixWord ++ tailWord_4681013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681013).length < 2 ^ (prefixWord ++ tailWord_4681013).sum := by decide
  have hdescent : baseEnd_4681013 < baseStart_4681013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681023 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 4]
def baseStart_4681023 : Nat := 118140960795 + 4681023 * 2 ^ 59
def prefixEnd_4681023 : Nat := 4983230072969 + 3 ^ 40 * 4681023 * 2
def baseEnd_4681023 : Nat := 2403614753751344209684873

theorem tailTrace_4681023 : CollatzResearch.WordTrace tailWord_4681023 prefixEnd_4681023 2403614753751344209684873 := by
  unfold tailWord_4681023
  simp only [CollatzResearch.WordTrace]
  refine ⟨170730934920460600925639723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113820623280307067283759815 170730934920460600925639723)
  ·
    refine ⟨256096402380690901388459585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170730934920460600925639723 256096402380690901388459585)
    ·
      refine ⟨192072301785518176041344689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256096402380690901388459585 192072301785518176041344689)
      ·
        refine ⟨144054226339138632031008517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192072301785518176041344689 144054226339138632031008517)
        ·
          refine ⟨27010167438588493505814097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144054226339138632031008517 27010167438588493505814097)
          ·
            refine ⟨20257625578941370129360573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27010167438588493505814097 20257625578941370129360573)
            ·
              refine ⟨7596609592103013798510215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20257625578941370129360573 7596609592103013798510215)
              ·
                refine ⟨11394914388154520697765323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7596609592103013798510215 11394914388154520697765323)
                ·
                  refine ⟨17092371582231781046647985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11394914388154520697765323 17092371582231781046647985)
                  ·
                    refine ⟨12819278686673835784985989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17092371582231781046647985 12819278686673835784985989)
                    ·
                      refine ⟨2403614753751344209684873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12819278686673835784985989 2403614753751344209684873)
                      ·
                        rfl

theorem cell23_4681023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_4681023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681023 prefixEnd_4681023 := by exact prefixLift 4681023
  have htrace : WordTrace (prefixWord ++ tailWord_4681023) baseStart_4681023 baseEnd_4681023 := by
    simpa [prefixWord, tailWord_4681023, baseEnd_4681023] using wordTrace_append hprefix tailTrace_4681023
  have hstable : (prefixWord ++ tailWord_4681023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681023).length < 2 ^ (prefixWord ++ tailWord_4681023).sum := by decide
  have hdescent : baseEnd_4681023 < baseStart_4681023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681043 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 3]
def baseStart_4681043 : Nat := 118140960795 + 4681043 * 2 ^ 59
def prefixEnd_4681043 : Nat := 4983230072969 + 3 ^ 40 * 4681043 * 2
def baseEnd_4681043 : Nat := 2403625023364434131434781

theorem tailTrace_4681043 : CollatzResearch.WordTrace tailWord_4681043 prefixEnd_4681043 2403625023364434131434781 := by
  unfold tailWord_4681043
  simp only [CollatzResearch.WordTrace]
  refine ⟨170731664380388144341367783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113821109586925429560911855 170731664380388144341367783)
  ·
    refine ⟨256097496570582216512051675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170731664380388144341367783 256097496570582216512051675)
    ·
      refine ⟨384146244855873324768077513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256097496570582216512051675 384146244855873324768077513)
      ·
        refine ⟨288109683641904993576058135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384146244855873324768077513 288109683641904993576058135)
        ·
          refine ⟨432164525462857490364087203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288109683641904993576058135 432164525462857490364087203)
          ·
            refine ⟨648246788194286235546130805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432164525462857490364087203 648246788194286235546130805)
            ·
              refine ⟨60773136393214334582449763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 648246788194286235546130805 60773136393214334582449763)
              ·
                refine ⟨91159704589821501873674645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60773136393214334582449763 91159704589821501873674645)
                ·
                  refine ⟨4273111152647882900328499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91159704589821501873674645 4273111152647882900328499)
                  ·
                    refine ⟨6409666728971824350492749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273111152647882900328499 6409666728971824350492749)
                    ·
                      refine ⟨2403625023364434131434781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409666728971824350492749 2403625023364434131434781)
                      ·
                        rfl

theorem cell23_4681043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 3].length) (baseStart_4681043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681043 prefixEnd_4681043 := by exact prefixLift 4681043
  have htrace : WordTrace (prefixWord ++ tailWord_4681043) baseStart_4681043 baseEnd_4681043 := by
    simpa [prefixWord, tailWord_4681043, baseEnd_4681043] using wordTrace_append hprefix tailTrace_4681043
  have hstable : (prefixWord ++ tailWord_4681043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681043).length < 2 ^ (prefixWord ++ tailWord_4681043).sum := by decide
  have hdescent : baseEnd_4681043 < baseStart_4681043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681060 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_4681060 : Nat := 118140960795 + 4681060 * 2 ^ 59
def prefixEnd_4681060 : Nat := 4983230072969 + 3 ^ 40 * 4681060 * 2
def baseEnd_4681060 : Nat := 2403633752535560564922203

theorem tailTrace_4681060 : CollatzResearch.WordTrace tailWord_4681060 prefixEnd_4681060 2403633752535560564922203 := by
  unfold tailWord_4681060
  simp only [CollatzResearch.WordTrace]
  refine ⟨85366142210663278122368317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113821522947551037496491089 85366142210663278122368317)
  ·
    refine ⟨32012303328998729295888119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85366142210663278122368317 32012303328998729295888119)
    ·
      refine ⟨48018454993498093943832179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32012303328998729295888119 48018454993498093943832179)
      ·
        refine ⟨72027682490247140915748269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48018454993498093943832179 72027682490247140915748269)
        ·
          refine ⟨27010380933842677843405601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72027682490247140915748269 27010380933842677843405601)
          ·
            refine ⟨20257785700382008382554201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27010380933842677843405601 20257785700382008382554201)
            ·
              refine ⟨15193339275286506286915651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20257785700382008382554201 15193339275286506286915651)
              ·
                refine ⟨22790008912929759430373477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15193339275286506286915651 22790008912929759430373477)
                ·
                  refine ⟨4273126671174329893195027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22790008912929759430373477 4273126671174329893195027)
                  ·
                    refine ⟨6409690006761494839792541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273126671174329893195027 6409690006761494839792541)
                    ·
                      refine ⟨2403633752535560564922203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409690006761494839792541 2403633752535560564922203)
                      ·
                        rfl

theorem cell23_4681060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_4681060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681060 prefixEnd_4681060 := by exact prefixLift 4681060
  have htrace : WordTrace (prefixWord ++ tailWord_4681060) baseStart_4681060 baseEnd_4681060 := by
    simpa [prefixWord, tailWord_4681060, baseEnd_4681060] using wordTrace_append hprefix tailTrace_4681060
  have hstable : (prefixWord ++ tailWord_4681060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681060).length < 2 ^ (prefixWord ++ tailWord_4681060).sum := by decide
  have hdescent : baseEnd_4681060 < baseStart_4681060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681100 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 1, 4, 2]
def baseStart_4681100 : Nat := 118140960795 + 4681100 * 2 ^ 59
def prefixEnd_4681100 : Nat := 4983230072969 + 3 ^ 40 * 4681100 * 2
def baseEnd_4681100 : Nat := 2403654291761740408422019

theorem tailTrace_4681100 : CollatzResearch.WordTrace tailWord_4681100 prefixEnd_4681100 2403654291761740408422019 := by
  unfold tailWord_4681100
  simp only [CollatzResearch.WordTrace]
  refine ⟨85366871670590821538096377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113822495560787762050795169 85366871670590821538096377)
  ·
    refine ⟨64025153752943116153572283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85366871670590821538096377 64025153752943116153572283)
    ·
      refine ⟨96037730629414674230358425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64025153752943116153572283 96037730629414674230358425)
      ·
        refine ⟨72028297972061005672768819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96037730629414674230358425 72028297972061005672768819)
        ·
          refine ⟨108042446958091508509153229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72028297972061005672768819 108042446958091508509153229)
          ·
            refine ⟨40515917609284315690932461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108042446958091508509153229 40515917609284315690932461)
            ·
              refine ⟨15193469103481618384099673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40515917609284315690932461 15193469103481618384099673)
              ·
                refine ⟨11395101827611213788074755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15193469103481618384099673 11395101827611213788074755)
                ·
                  refine ⟨17092652741416820682112133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11395101827611213788074755 17092652741416820682112133)
                  ·
                    refine ⟨3204872389015653877896025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17092652741416820682112133 3204872389015653877896025)
                    ·
                      refine ⟨2403654291761740408422019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204872389015653877896025 2403654291761740408422019)
                      ·
                        rfl

theorem cell23_4681100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_4681100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681100 prefixEnd_4681100 := by exact prefixLift 4681100
  have htrace : WordTrace (prefixWord ++ tailWord_4681100) baseStart_4681100 baseEnd_4681100 := by
    simpa [prefixWord, tailWord_4681100, baseEnd_4681100] using wordTrace_append hprefix tailTrace_4681100
  have hstable : (prefixWord ++ tailWord_4681100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681100).length < 2 ^ (prefixWord ++ tailWord_4681100).sum := by decide
  have hdescent : baseEnd_4681100 < baseStart_4681100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681200 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 3, 4]
def baseStart_4681200 : Nat := 118140960795 + 4681200 * 2 ^ 59
def prefixEnd_4681200 : Nat := 4983230072969 + 3 ^ 40 * 4681200 * 2
def baseEnd_4681200 : Nat := 801235213275730005723853

theorem tailTrace_4681200 : CollatzResearch.WordTrace tailWord_4681200 prefixEnd_4681200 801235213275730005723853 := by
  unfold tailWord_4681200
  simp only [CollatzResearch.WordTrace]
  refine ⟨85368695320409680077416527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113824927093879573436555369 85368695320409680077416527)
  ·
    refine ⟨128053042980614520116124791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85368695320409680077416527 128053042980614520116124791)
    ·
      refine ⟨192079564470921780174187187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128053042980614520116124791 192079564470921780174187187)
      ·
        refine ⟨288119346706382670261280781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192079564470921780174187187 288119346706382670261280781)
        ·
          refine ⟨108044755014893501347980293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288119346706382670261280781 108044755014893501347980293)
          ·
            refine ⟨20258391565292531502746305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108044755014893501347980293 20258391565292531502746305)
            ·
              refine ⟨15193793673969398627059729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20258391565292531502746305 15193793673969398627059729)
              ·
                refine ⟨11395345255477048970294797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15193793673969398627059729 11395345255477048970294797)
                ·
                  refine ⟨4273254470803893363860549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11395345255477048970294797 4273254470803893363860549)
                  ·
                    refine ⟨801235213275730005723853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273254470803893363860549 801235213275730005723853)
                    ·
                      rfl

theorem cell23_4681200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_4681200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681200 prefixEnd_4681200 := by exact prefixLift 4681200
  have htrace : WordTrace (prefixWord ++ tailWord_4681200) baseStart_4681200 baseEnd_4681200 := by
    simpa [prefixWord, tailWord_4681200, baseEnd_4681200] using wordTrace_append hprefix tailTrace_4681200
  have hstable : (prefixWord ++ tailWord_4681200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681200).length < 2 ^ (prefixWord ++ tailWord_4681200).sum := by decide
  have hdescent : baseEnd_4681200 < baseStart_4681200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681210 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_4681210 : Nat := 118140960795 + 4681210 * 2 ^ 59
def prefixEnd_4681210 : Nat := 4983230072969 + 3 ^ 40 * 4681210 * 2
def baseEnd_4681210 : Nat := 2403710774633734978046513

theorem tailTrace_4681210 : CollatzResearch.WordTrace tailWord_4681210 prefixEnd_4681210 2403710774633734978046513 := by
  unfold tailWord_4681210
  simp only [CollatzResearch.WordTrace]
  refine ⟨42684438842695782965674271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113825170247188754575131389 42684438842695782965674271)
  ·
    refine ⟨64026658264043674448511407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42684438842695782965674271 64026658264043674448511407)
    ·
      refine ⟨96039987396065511672767111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64026658264043674448511407 96039987396065511672767111)
      ·
        refine ⟨144059981094098267509150667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96039987396065511672767111 144059981094098267509150667)
        ·
          refine ⟨216089971641147401263726001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144059981094098267509150667 216089971641147401263726001)
          ·
            refine ⟨162067478730860550947794501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216089971641147401263726001 162067478730860550947794501)
            ·
              refine ⟨30387652262036353302711469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162067478730860550947794501 30387652262036353302711469)
              ·
                refine ⟨11395369598263632488516801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30387652262036353302711469 11395369598263632488516801)
                ·
                  refine ⟨8546527198697724366387601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11395369598263632488516801 8546527198697724366387601)
                  ·
                    refine ⟨6409895399023293274790701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8546527198697724366387601 6409895399023293274790701)
                    ·
                      refine ⟨2403710774633734978046513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409895399023293274790701 2403710774633734978046513)
                      ·
                        rfl

theorem cell23_4681210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_4681210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681210 prefixEnd_4681210 := by exact prefixLift 4681210
  have htrace : WordTrace (prefixWord ++ tailWord_4681210) baseStart_4681210 baseEnd_4681210 := by
    simpa [prefixWord, tailWord_4681210, baseEnd_4681210] using wordTrace_append hprefix tailTrace_4681210
  have hstable : (prefixWord ++ tailWord_4681210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681210).length < 2 ^ (prefixWord ++ tailWord_4681210).sum := by decide
  have hdescent : baseEnd_4681210 < baseStart_4681210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681213 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 8]
def baseStart_4681213 : Nat := 118140960795 + 4681213 * 2 ^ 59
def prefixEnd_4681213 : Nat := 4983230072969 + 3 ^ 40 * 4681213 * 2
def baseEnd_4681213 : Nat := 267079146119522051812111

theorem tailTrace_4681213 : CollatzResearch.WordTrace tailWord_4681213 prefixEnd_4681213 267079146119522051812111 := by
  unfold tailWord_4681213
  simp only [CollatzResearch.WordTrace]
  refine ⟨170737864789772263375056293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113825243193181508916704195 170737864789772263375056293)
  ·
    refine ⟨32013349648082299382823055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170737864789772263375056293 32013349648082299382823055)
    ·
      refine ⟨48020024472123449074234583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32013349648082299382823055 48020024472123449074234583)
      ·
        refine ⟨72030036708185173611351875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48020024472123449074234583 72030036708185173611351875)
        ·
          refine ⟨108045055062277760417027813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72030036708185173611351875 108045055062277760417027813)
          ·
            refine ⟨20258447824177080078192715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108045055062277760417027813 20258447824177080078192715)
            ·
              refine ⟨30387671736265620117289073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20258447824177080078192715 30387671736265620117289073)
              ·
                refine ⟨22790753802199215087966805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30387671736265620117289073 22790753802199215087966805)
                ·
                  refine ⟨267079146119522051812111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22790753802199215087966805 267079146119522051812111)
                  ·
                    rfl

theorem cell23_4681213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_4681213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681213 prefixEnd_4681213 := by exact prefixLift 4681213
  have htrace : WordTrace (prefixWord ++ tailWord_4681213) baseStart_4681213 baseEnd_4681213 := by
    simpa [prefixWord, tailWord_4681213, baseEnd_4681213] using wordTrace_append hprefix tailTrace_4681213
  have hstable : (prefixWord ++ tailWord_4681213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681213).length < 2 ^ (prefixWord ++ tailWord_4681213).sum := by decide
  have hdescent : baseEnd_4681213 < baseStart_4681213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681227 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 3]
def baseStart_4681227 : Nat := 118140960795 + 4681227 * 2 ^ 59
def prefixEnd_4681227 : Nat := 4983230072969 + 3 ^ 40 * 4681227 * 2
def baseEnd_4681227 : Nat := 2403719503804861411533935

theorem tailTrace_4681227 : CollatzResearch.WordTrace tailWord_4681227 prefixEnd_4681227 2403719503804861411533935 := by
  unfold tailWord_4681227
  simp only [CollatzResearch.WordTrace]
  refine ⟨170738375411721543766065935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113825583607814362510710623 170738375411721543766065935)
  ·
    refine ⟨256107563117582315649098903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170738375411721543766065935 256107563117582315649098903)
    ·
      refine ⟨384161344676373473473648355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256107563117582315649098903 384161344676373473473648355)
      ·
        refine ⟨576242017014560210210472533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384161344676373473473648355 576242017014560210210472533)
        ·
          refine ⟨6752836136889377463403975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 576242017014560210210472533 6752836136889377463403975)
          ·
            refine ⟨10129254205334066195105963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6752836136889377463403975 10129254205334066195105963)
            ·
              refine ⟨15193881308001099292658945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10129254205334066195105963 15193881308001099292658945)
              ·
                refine ⟨11395410981000824469494209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15193881308001099292658945 11395410981000824469494209)
                ·
                  refine ⟨8546558235750618352120657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11395410981000824469494209 8546558235750618352120657)
                  ·
                    refine ⟨6409918676812963764090493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8546558235750618352120657 6409918676812963764090493)
                    ·
                      refine ⟨2403719503804861411533935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409918676812963764090493 2403719503804861411533935)
                      ·
                        rfl

theorem cell23_4681227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 3].length) (baseStart_4681227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681227 prefixEnd_4681227 := by exact prefixLift 4681227
  have htrace : WordTrace (prefixWord ++ tailWord_4681227) baseStart_4681227 baseEnd_4681227 := by
    simpa [prefixWord, tailWord_4681227, baseEnd_4681227] using wordTrace_append hprefix tailTrace_4681227
  have hstable : (prefixWord ++ tailWord_4681227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681227).length < 2 ^ (prefixWord ++ tailWord_4681227).sum := by decide
  have hdescent : baseEnd_4681227 < baseStart_4681227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681267 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 2, 3, 2]
def baseStart_4681267 : Nat := 118140960795 + 4681267 * 2 ^ 59
def prefixEnd_4681267 : Nat := 4983230072969 + 3 ^ 40 * 4681267 * 2
def baseEnd_4681267 : Nat := 2403740043031041255033751

theorem tailTrace_4681267 : CollatzResearch.WordTrace tailWord_4681267 prefixEnd_4681267 2403740043031041255033751 := by
  unfold tailWord_4681267
  simp only [CollatzResearch.WordTrace]
  refine ⟨170739834331576630597522055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113826556221051087065014703 170739834331576630597522055)
  ·
    refine ⟨256109751497364945896283083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170739834331576630597522055 256109751497364945896283083)
    ·
      refine ⟨384164627246047418844424625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256109751497364945896283083 384164627246047418844424625)
      ·
        refine ⟨288123470434535564133318469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384164627246047418844424625 288123470434535564133318469)
        ·
          refine ⟨54023150706475418274997213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288123470434535564133318469 54023150706475418274997213)
          ·
            refine ⟨20258681514928281853123955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54023150706475418274997213 20258681514928281853123955)
            ·
              refine ⟨30388022272392422779685933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20258681514928281853123955 30388022272392422779685933)
              ·
                refine ⟨11395508352147158542382225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30388022272392422779685933 11395508352147158542382225)
                ·
                  refine ⟨8546631264110368906786669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11395508352147158542382225 8546631264110368906786669)
                  ·
                    refine ⟨3204986724041388340045001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8546631264110368906786669 3204986724041388340045001)
                    ·
                      refine ⟨2403740043031041255033751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3204986724041388340045001 2403740043031041255033751)
                      ·
                        rfl

theorem cell23_4681267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3, 2].length) (baseStart_4681267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681267 prefixEnd_4681267 := by exact prefixLift 4681267
  have htrace : WordTrace (prefixWord ++ tailWord_4681267) baseStart_4681267 baseEnd_4681267 := by
    simpa [prefixWord, tailWord_4681267, baseEnd_4681267] using wordTrace_append hprefix tailTrace_4681267
  have hstable : (prefixWord ++ tailWord_4681267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681267).length < 2 ^ (prefixWord ++ tailWord_4681267).sum := by decide
  have hdescent : baseEnd_4681267 < baseStart_4681267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681274 : List Nat := [3, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3]
def baseStart_4681274 : Nat := 118140960795 + 4681274 * 2 ^ 59
def prefixEnd_4681274 : Nat := 4983230072969 + 3 ^ 40 * 4681274 * 2
def baseEnd_4681274 : Nat := 2403743637395622727646219

theorem tailTrace_4681274 : CollatzResearch.WordTrace tailWord_4681274 prefixEnd_4681274 2403743637395622727646219 := by
  unfold tailWord_4681274
  simp only [CollatzResearch.WordTrace]
  refine ⟨42685022410637817698256719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113826726428367513862017917 42685022410637817698256719)
  ·
    refine ⟨64027533615956726547385079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42685022410637817698256719 64027533615956726547385079)
    ·
      refine ⟨96041300423935089821077619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64027533615956726547385079 96041300423935089821077619)
      ·
        refine ⟨144061950635902634731616429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96041300423935089821077619 144061950635902634731616429)
        ·
          refine ⟨54023231488463488024356161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144061950635902634731616429 54023231488463488024356161)
          ·
            refine ⟨40517423616347616018267121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54023231488463488024356161 40517423616347616018267121)
            ·
              refine ⟨30388067712260712013700341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40517423616347616018267121 30388067712260712013700341)
              ·
                refine ⟨2848881348024441751284407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30388067712260712013700341 2848881348024441751284407)
                ·
                  refine ⟨4273322022036662626926611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848881348024441751284407 4273322022036662626926611)
                  ·
                    refine ⟨6409983033054993940389917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273322022036662626926611 6409983033054993940389917)
                    ·
                      refine ⟨2403743637395622727646219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6409983033054993940389917 2403743637395622727646219)
                      ·
                        rfl

theorem cell23_4681274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_4681274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681274 prefixEnd_4681274 := by exact prefixLift 4681274
  have htrace : WordTrace (prefixWord ++ tailWord_4681274) baseStart_4681274 baseEnd_4681274 := by
    simpa [prefixWord, tailWord_4681274, baseEnd_4681274] using wordTrace_append hprefix tailTrace_4681274
  have hstable : (prefixWord ++ tailWord_4681274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681274).length < 2 ^ (prefixWord ++ tailWord_4681274).sum := by decide
  have hdescent : baseEnd_4681274 < baseStart_4681274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681300 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4681300 : Nat := 118140960795 + 4681300 * 2 ^ 59
def prefixEnd_4681300 : Nat := 4983230072969 + 3 ^ 40 * 4681300 * 2
def baseEnd_4681300 : Nat := 2403756987892639625921099

theorem tailTrace_4681300 : CollatzResearch.WordTrace tailWord_4681300 prefixEnd_4681300 2403756987892639625921099 := by
  unfold tailWord_4681300
  simp only [CollatzResearch.WordTrace]
  refine ⟨85370518970228538616736677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113827358626971384822315569 85370518970228538616736677)
  ·
    refine ⟨16006972306917850990638127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85370518970228538616736677 16006972306917850990638127)
    ·
      refine ⟨24010458460376776485957191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16006972306917850990638127 24010458460376776485957191)
      ·
        refine ⟨36015687690565164728935787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24010458460376776485957191 36015687690565164728935787)
        ·
          refine ⟨54023531535847747093403681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36015687690565164728935787 54023531535847747093403681)
          ·
            refine ⟨40517648651885810320052761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54023531535847747093403681 40517648651885810320052761)
            ·
              refine ⟨30388236488914357740039571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40517648651885810320052761 30388236488914357740039571)
              ·
                refine ⟨45582354733371536610059357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30388236488914357740039571 45582354733371536610059357)
                ·
                  refine ⟨17093383025014326228772259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45582354733371536610059357 17093383025014326228772259)
                  ·
                    refine ⟨25640074537521489343158389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17093383025014326228772259 25640074537521489343158389)
                    ·
                      refine ⟨2403756987892639625921099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25640074537521489343158389 2403756987892639625921099)
                      ·
                        rfl

theorem cell23_4681300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4681300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681300 prefixEnd_4681300 := by exact prefixLift 4681300
  have htrace : WordTrace (prefixWord ++ tailWord_4681300) baseStart_4681300 baseEnd_4681300 := by
    simpa [prefixWord, tailWord_4681300, baseEnd_4681300] using wordTrace_append hprefix tailTrace_4681300
  have hstable : (prefixWord ++ tailWord_4681300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681300).length < 2 ^ (prefixWord ++ tailWord_4681300).sum := by decide
  have hdescent : baseEnd_4681300 < baseStart_4681300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681317 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_4681317 : Nat := 118140960795 + 4681317 * 2 ^ 59
def prefixEnd_4681317 : Nat := 4983230072969 + 3 ^ 40 * 4681317 * 2
def baseEnd_4681317 : Nat := 2403765717063766059408521

theorem tailTrace_4681317 : CollatzResearch.WordTrace tailWord_4681317 prefixEnd_4681317 2403765717063766059408521 := by
  unfold tailWord_4681317
  simp only [CollatzResearch.WordTrace]
  refine ⟨170741657981395489136842205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113827771987596992757894803 170741657981395489136842205)
  ·
    refine ⟨64028121743023308426315827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170741657981395489136842205 64028121743023308426315827)
    ·
      refine ⟨96042182614534962639473741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64028121743023308426315827 96042182614534962639473741)
      ·
        refine ⟨36015818480450610989802653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96042182614534962639473741 36015818480450610989802653)
        ·
          refine ⟨13505931930168979121175995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36015818480450610989802653 13505931930168979121175995)
          ·
            refine ⟨20258897895253468681763993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13505931930168979121175995 20258897895253468681763993)
            ·
              refine ⟨15194173421440101511322995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20258897895253468681763993 15194173421440101511322995)
              ·
                refine ⟨22791260132160152266984493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15194173421440101511322995 22791260132160152266984493)
                ·
                  refine ⟨8546722549560057100119185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22791260132160152266984493 8546722549560057100119185)
                  ·
                    refine ⟨6410041912170042825089389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8546722549560057100119185 6410041912170042825089389)
                    ·
                      refine ⟨2403765717063766059408521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6410041912170042825089389 2403765717063766059408521)
                      ·
                        rfl

theorem cell23_4681317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_4681317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681317 prefixEnd_4681317 := by exact prefixLift 4681317
  have htrace : WordTrace (prefixWord ++ tailWord_4681317) baseStart_4681317 baseEnd_4681317 := by
    simpa [prefixWord, tailWord_4681317, baseEnd_4681317] using wordTrace_append hprefix tailTrace_4681317
  have hstable : (prefixWord ++ tailWord_4681317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681317).length < 2 ^ (prefixWord ++ tailWord_4681317).sum := by decide
  have hdescent : baseEnd_4681317 < baseStart_4681317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681323 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6]
def baseStart_4681323 : Nat := 118140960795 + 4681323 * 2 ^ 59
def prefixEnd_4681323 : Nat := 4983230072969 + 3 ^ 40 * 4681323 * 2
def baseEnd_4681323 : Nat := 2403768797947693035933493

theorem tailTrace_4681323 : CollatzResearch.WordTrace tailWord_4681323 prefixEnd_4681323 2403768797947693035933493 := by
  unfold tailWord_4681323
  simp only [CollatzResearch.WordTrace]
  refine ⟨170741876819373752161560623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113827917879582501441040415 170741876819373752161560623)
  ·
    refine ⟨256112815229060628242340935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170741876819373752161560623 256112815229060628242340935)
    ·
      refine ⟨384169222843590942363511403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256112815229060628242340935 384169222843590942363511403)
      ·
        refine ⟨576253834265386413545267105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384169222843590942363511403 576253834265386413545267105)
        ·
          refine ⟨432190375699039810158950329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576253834265386413545267105 432190375699039810158950329)
          ·
            refine ⟨324142781774279857619212747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432190375699039810158950329 324142781774279857619212747)
            ·
              refine ⟨486214172661419786428819121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324142781774279857619212747 486214172661419786428819121)
              ·
                refine ⟨364660629496064839821614341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486214172661419786428819121 364660629496064839821614341)
                ·
                  refine ⟨68373868030512157466552689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 364660629496064839821614341 68373868030512157466552689)
                  ·
                    refine ⟨51280401022884118099914517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68373868030512157466552689 51280401022884118099914517)
                    ·
                      refine ⟨2403768797947693035933493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51280401022884118099914517 2403768797947693035933493)
                      ·
                        rfl

theorem cell23_4681323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_4681323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681323 prefixEnd_4681323 := by exact prefixLift 4681323
  have htrace : WordTrace (prefixWord ++ tailWord_4681323) baseStart_4681323 baseEnd_4681323 := by
    simpa [prefixWord, tailWord_4681323, baseEnd_4681323] using wordTrace_append hprefix tailTrace_4681323
  have hstable : (prefixWord ++ tailWord_4681323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681323).length < 2 ^ (prefixWord ++ tailWord_4681323).sum := by decide
  have hdescent : baseEnd_4681323 < baseStart_4681323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681400 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_4681400 : Nat := 118140960795 + 4681400 * 2 ^ 59
def prefixEnd_4681400 : Nat := 4983230072969 + 3 ^ 40 * 4681400 * 2
def baseEnd_4681400 : Nat := 2403808335958089234670639

theorem tailTrace_4681400 : CollatzResearch.WordTrace tailWord_4681400 prefixEnd_4681400 2403808335958089234670639 := by
  unfold tailWord_4681400
  simp only [CollatzResearch.WordTrace]
  refine ⟨85372342620047397156056827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113829790160063196208075769 85372342620047397156056827)
  ·
    refine ⟨128058513930071095734085241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85372342620047397156056827 128058513930071095734085241)
    ·
      refine ⟨96043885447553321800563931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128058513930071095734085241 96043885447553321800563931)
      ·
        refine ⟨144065828171329982700845897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96043885447553321800563931 144065828171329982700845897)
        ·
          refine ⟨108049371128497487025634423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144065828171329982700845897 108049371128497487025634423)
          ·
            refine ⟨162074056692746230538451635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108049371128497487025634423 162074056692746230538451635)
            ·
              refine ⟨243111085039119345807677453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162074056692746230538451635 243111085039119345807677453)
              ·
                refine ⟨91166656889669754677879045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243111085039119345807677453 91166656889669754677879045)
                ·
                  refine ⟨17093748166813079002102321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91166656889669754677879045 17093748166813079002102321)
                  ·
                    refine ⟨12820311125109809251576741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17093748166813079002102321 12820311125109809251576741)
                    ·
                      refine ⟨2403808335958089234670639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12820311125109809251576741 2403808335958089234670639)
                      ·
                        rfl

theorem cell23_4681400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_4681400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681400 prefixEnd_4681400 := by exact prefixLift 4681400
  have htrace : WordTrace (prefixWord ++ tailWord_4681400) baseStart_4681400 baseEnd_4681400 := by
    simpa [prefixWord, tailWord_4681400, baseEnd_4681400] using wordTrace_append hprefix tailTrace_4681400
  have hstable : (prefixWord ++ tailWord_4681400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681400).length < 2 ^ (prefixWord ++ tailWord_4681400).sum := by decide
  have hdescent : baseEnd_4681400 < baseStart_4681400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681440 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 1, 7]
def baseStart_4681440 : Nat := 118140960795 + 4681440 * 2 ^ 59
def prefixEnd_4681440 : Nat := 4983230072969 + 3 ^ 40 * 4681440 * 2
def baseEnd_4681440 : Nat := 801276291728089692723485

theorem tailTrace_4681440 : CollatzResearch.WordTrace tailWord_4681440 prefixEnd_4681440 801276291728089692723485 := by
  unfold tailWord_4681440
  simp only [CollatzResearch.WordTrace]
  refine ⟨85373072079974940571784887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113830762773299920762379849 85373072079974940571784887)
  ·
    refine ⟨128059608119962410857677331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85373072079974940571784887 128059608119962410857677331)
    ·
      refine ⟨192089412179943616286515997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128059608119962410857677331 192089412179943616286515997)
      ·
        refine ⟨72033529567478856107443499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192089412179943616286515997 72033529567478856107443499)
        ·
          refine ⟨108050294351218284161165249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72033529567478856107443499 108050294351218284161165249)
          ·
            refine ⟨81037720763413713120873937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108050294351218284161165249 81037720763413713120873937)
            ·
              refine ⟨60778290572560284840655453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81037720763413713120873937 60778290572560284840655453)
              ·
                refine ⟨22791858964710106815245795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60778290572560284840655453 22791858964710106815245795)
                ·
                  refine ⟨34187788447065160222868693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22791858964710106815245795 34187788447065160222868693)
                  ·
                    refine ⟨801276291728089692723485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34187788447065160222868693 801276291728089692723485)
                    ·
                      rfl

theorem cell23_4681440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_4681440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681440 prefixEnd_4681440 := by exact prefixLift 4681440
  have htrace : WordTrace (prefixWord ++ tailWord_4681440) baseStart_4681440 baseEnd_4681440 := by
    simpa [prefixWord, tailWord_4681440, baseEnd_4681440] using wordTrace_append hprefix tailTrace_4681440
  have hstable : (prefixWord ++ tailWord_4681440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681440).length < 2 ^ (prefixWord ++ tailWord_4681440).sum := by decide
  have hdescent : baseEnd_4681440 < baseStart_4681440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681457 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 2, 5]
def baseStart_4681457 : Nat := 118140960795 + 4681457 * 2 ^ 59
def prefixEnd_4681457 : Nat := 4983230072969 + 3 ^ 40 * 4681457 * 2
def baseEnd_4681457 : Nat := 801279201451798503885959

theorem tailTrace_4681457 : CollatzResearch.WordTrace tailWord_4681457 prefixEnd_4681457 801279201451798503885959 := by
  unfold tailWord_4681457
  simp only [CollatzResearch.WordTrace]
  refine ⟨170746764200888293046938625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113831176133925528697959083 170746764200888293046938625)
  ·
    refine ⟨128060073150666219785203969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170746764200888293046938625 128060073150666219785203969)
    ·
      refine ⟨96045054862999664838902977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128060073150666219785203969 96045054862999664838902977)
      ·
        refine ⟨72033791147249748629177233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96045054862999664838902977 72033791147249748629177233)
        ·
          refine ⟨54025343360437311471882925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72033791147249748629177233 54025343360437311471882925)
          ·
            refine ⟨20259503760163991801956097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54025343360437311471882925 20259503760163991801956097)
            ·
              refine ⟨15194627820122993851467073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20259503760163991801956097 15194627820122993851467073)
              ·
                refine ⟨11395970865092245388600305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15194627820122993851467073 11395970865092245388600305)
                ·
                  refine ⟨8546978148819184041450229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11395970865092245388600305 8546978148819184041450229)
                  ·
                    refine ⟨801279201451798503885959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8546978148819184041450229 801279201451798503885959)
                    ·
                      rfl

theorem cell23_4681457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_4681457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681457 prefixEnd_4681457 := by exact prefixLift 4681457
  have htrace : WordTrace (prefixWord ++ tailWord_4681457) baseStart_4681457 baseEnd_4681457 := by
    simpa [prefixWord, tailWord_4681457, baseEnd_4681457] using wordTrace_append hprefix tailTrace_4681457
  have hstable : (prefixWord ++ tailWord_4681457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681457).length < 2 ^ (prefixWord ++ tailWord_4681457).sum := by decide
  have hdescent : baseEnd_4681457 < baseStart_4681457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681521 : List Nat := [1, 2, 2, 3, 2, 2, 2, 4, 1, 4]
def baseStart_4681521 : Nat := 118140960795 + 4681521 * 2 ^ 59
def prefixEnd_4681521 : Nat := 4983230072969 + 3 ^ 40 * 4681521 * 2
def baseEnd_4681521 : Nat := 801290155705761087085861

theorem tailTrace_4681521 : CollatzResearch.WordTrace tailWord_4681521 prefixEnd_4681521 801290155705761087085861 := by
  unfold tailWord_4681521
  simp only [CollatzResearch.WordTrace]
  refine ⟨170749098472656431977268417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113832732315104287984845611 170749098472656431977268417)
  ·
    refine ⟨128061823854492323982951313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170749098472656431977268417 128061823854492323982951313)
    ·
      refine ⟨96046367890869242987213485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128061823854492323982951313 96046367890869242987213485)
      ·
        refine ⟨36017387959075966120205057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96046367890869242987213485 36017387959075966120205057)
        ·
          refine ⟨27013040969306974590153793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36017387959075966120205057 27013040969306974590153793)
          ·
            refine ⟨20259780726980230942615345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27013040969306974590153793 20259780726980230942615345)
            ·
              refine ⟨15194835545235173206961509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20259780726980230942615345 15194835545235173206961509)
              ·
                refine ⟨2849031664731594976305283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15194835545235173206961509 2849031664731594976305283)
                ·
                  refine ⟨4273547497097392464457925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849031664731594976305283 4273547497097392464457925)
                  ·
                    refine ⟨801290155705761087085861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273547497097392464457925 801290155705761087085861)
                    ·
                      rfl

theorem cell23_4681521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_4681521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681521 prefixEnd_4681521 := by exact prefixLift 4681521
  have htrace : WordTrace (prefixWord ++ tailWord_4681521) baseStart_4681521 baseEnd_4681521 := by
    simpa [prefixWord, tailWord_4681521, baseEnd_4681521] using wordTrace_append hprefix tailTrace_4681521
  have hstable : (prefixWord ++ tailWord_4681521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681521).length < 2 ^ (prefixWord ++ tailWord_4681521).sum := by decide
  have hdescent : baseEnd_4681521 < baseStart_4681521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681587 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 3]
def baseStart_4681587 : Nat := 118140960795 + 4681587 * 2 ^ 59
def prefixEnd_4681587 : Nat := 4983230072969 + 3 ^ 40 * 4681587 * 2
def baseEnd_4681587 : Nat := 2403904356840480003032279

theorem tailTrace_4681587 : CollatzResearch.WordTrace tailWord_4681587 prefixEnd_4681587 2403904356840480003032279 := by
  unfold tailWord_4681587
  simp only [CollatzResearch.WordTrace]
  refine ⟨170751505690417325249171015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113834337126944883499447343 170751505690417325249171015)
  ·
    refine ⟨256127258535625987873756523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170751505690417325249171015 256127258535625987873756523)
    ·
      refine ⟨384190887803438981810634785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256127258535625987873756523 384190887803438981810634785)
      ·
        refine ⟨288143165852579236357976089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384190887803438981810634785 288143165852579236357976089)
        ·
          refine ⟨216107374389434427268482067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288143165852579236357976089 216107374389434427268482067)
          ·
            refine ⟨324161061584151640902723101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216107374389434427268482067 324161061584151640902723101)
            ·
              refine ⟨121560398094056865338521163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324161061584151640902723101 121560398094056865338521163)
              ·
                refine ⟨182340597141085298007781745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121560398094056865338521163 182340597141085298007781745)
                ·
                  refine ⟨136755447855813973505836309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182340597141085298007781745 136755447855813973505836309)
                  ·
                    refine ⟨6410411618241280008086077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136755447855813973505836309 6410411618241280008086077)
                    ·
                      refine ⟨2403904356840480003032279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6410411618241280008086077 2403904356840480003032279)
                      ·
                        rfl

theorem cell23_4681587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_4681587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681587 prefixEnd_4681587 := by exact prefixLift 4681587
  have htrace : WordTrace (prefixWord ++ tailWord_4681587) baseStart_4681587 baseEnd_4681587 := by
    simpa [prefixWord, tailWord_4681587, baseEnd_4681587] using wordTrace_append hprefix tailTrace_4681587
  have hstable : (prefixWord ++ tailWord_4681587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681587).length < 2 ^ (prefixWord ++ tailWord_4681587).sum := by decide
  have hdescent : baseEnd_4681587 < baseStart_4681587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681598 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4681598 : Nat := 118140960795 + 4681598 * 2 ^ 59
def prefixEnd_4681598 : Nat := 4983230072969 + 3 ^ 40 * 4681598 * 2
def baseEnd_4681598 : Nat := 801303335042559819998243

theorem tailTrace_4681598 : CollatzResearch.WordTrace tailWord_4681598 prefixEnd_4681598 801303335042559819998243 := by
  unfold tailWord_4681598
  simp only [CollatzResearch.WordTrace]
  refine ⟨21343988361672184265977681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113834604595584982751880965 21343988361672184265977681)
  ·
    refine ⟨16007991271254138199483261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21343988361672184265977681 16007991271254138199483261)
    ·
      refine ⟨6002996726720301824806223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16007991271254138199483261 6002996726720301824806223)
      ·
        refine ⟨9004495090080452737209335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6002996726720301824806223 9004495090080452737209335)
        ·
          refine ⟨13506742635120679105814003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9004495090080452737209335 13506742635120679105814003)
          ·
            refine ⟨20260113952681018658721005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13506742635120679105814003 20260113952681018658721005)
            ·
              refine ⟨7597542732255381997020377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20260113952681018658721005 7597542732255381997020377)
              ·
                refine ⟨5698157049191536497765283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7597542732255381997020377 5698157049191536497765283)
                ·
                  refine ⟨8547235573787304746647925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5698157049191536497765283 8547235573787304746647925)
                  ·
                    refine ⟨801303335042559819998243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8547235573787304746647925 801303335042559819998243)
                    ·
                      rfl

theorem cell23_4681598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4681598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681598 prefixEnd_4681598 := by exact prefixLift 4681598
  have htrace : WordTrace (prefixWord ++ tailWord_4681598) baseStart_4681598 baseEnd_4681598 := by
    simpa [prefixWord, tailWord_4681598, baseEnd_4681598] using wordTrace_append hprefix tailTrace_4681598
  have hstable : (prefixWord ++ tailWord_4681598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681598).length < 2 ^ (prefixWord ++ tailWord_4681598).sum := by decide
  have hdescent : baseEnd_4681598 < baseStart_4681598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681624 : List Nat := [2, 1, 2, 6, 1, 11]
def baseStart_4681624 : Nat := 118140960795 + 4681624 * 2 ^ 59
def prefixEnd_4681624 : Nat := 4983230072969 + 3 ^ 40 * 4681624 * 2
def baseEnd_4681624 : Nat := 9892688706274470610163

theorem tailTrace_4681624 : CollatzResearch.WordTrace tailWord_4681624 prefixEnd_4681624 9892688706274470610163 := by
  unfold tailWord_4681624
  simp only [CollatzResearch.WordTrace]
  refine ⟨85376427595641640284133963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113835236794188853712178617 85376427595641640284133963)
  ·
    refine ⟨128064641393462460426200945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85376427595641640284133963 128064641393462460426200945)
    ·
      refine ⟨96048481045096845319650709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128064641393462460426200945 96048481045096845319650709)
      ·
        refine ⟨4502272548988914624358627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96048481045096845319650709 4502272548988914624358627)
        ·
          refine ⟨6753408823483371936537941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502272548988914624358627 6753408823483371936537941)
          ·
            refine ⟨9892688706274470610163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6753408823483371936537941 9892688706274470610163)
            ·
              rfl

theorem cell23_4681624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 11].length) (baseStart_4681624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681624 prefixEnd_4681624 := by exact prefixLift 4681624
  have htrace : WordTrace (prefixWord ++ tailWord_4681624) baseStart_4681624 baseEnd_4681624 := by
    simpa [prefixWord, tailWord_4681624, baseEnd_4681624] using wordTrace_append hprefix tailTrace_4681624
  have hstable : (prefixWord ++ tailWord_4681624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681624).length < 2 ^ (prefixWord ++ tailWord_4681624).sum := by decide
  have hdescent : baseEnd_4681624 < baseStart_4681624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681628 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_4681628 : Nat := 118140960795 + 4681628 * 2 ^ 59
def prefixEnd_4681628 : Nat := 4983230072969 + 3 ^ 40 * 4681628 * 2
def baseEnd_4681628 : Nat := 801308469849104780873197

theorem tailTrace_4681628 : CollatzResearch.WordTrace tailWord_4681628 prefixEnd_4681628 801308469849104780873197 := by
  unfold tailWord_4681628
  simp only [CollatzResearch.WordTrace]
  refine ⟨85376500541634394625706769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113835334055512526167609025 85376500541634394625706769)
  ·
    refine ⟨64032375406225795969280077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85376500541634394625706769 64032375406225795969280077)
    ·
      refine ⟨24012140777334673488480029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64032375406225795969280077 24012140777334673488480029)
      ·
        refine ⟨9004552791500502558180011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24012140777334673488480029 9004552791500502558180011)
        ·
          refine ⟨13506829187250753837270017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9004552791500502558180011 13506829187250753837270017)
          ·
            refine ⟨10130121890438065377952513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13506829187250753837270017 10130121890438065377952513)
            ·
              refine ⟨7597591417828549033464385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10130121890438065377952513 7597591417828549033464385)
              ·
                refine ⟨5698193563371411775098289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7597591417828549033464385 5698193563371411775098289)
                ·
                  refine ⟨4273645172528558831323717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698193563371411775098289 4273645172528558831323717)
                  ·
                    refine ⟨801308469849104780873197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273645172528558831323717 801308469849104780873197)
                    ·
                      rfl

theorem cell23_4681628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_4681628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681628 prefixEnd_4681628 := by exact prefixLift 4681628
  have htrace : WordTrace (prefixWord ++ tailWord_4681628) baseStart_4681628 baseEnd_4681628 := by
    simpa [prefixWord, tailWord_4681628, baseEnd_4681628] using wordTrace_append hprefix tailTrace_4681628
  have hstable : (prefixWord ++ tailWord_4681628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681628).length < 2 ^ (prefixWord ++ tailWord_4681628).sum := by decide
  have hdescent : baseEnd_4681628 < baseStart_4681628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681644 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 9, 2]
def baseStart_4681644 : Nat := 118140960795 + 4681644 * 2 ^ 59
def prefixEnd_4681644 : Nat := 4983230072969 + 3 ^ 40 * 4681644 * 2
def baseEnd_4681644 : Nat := 2403933625237786280019517

theorem tailTrace_4681644 : CollatzResearch.WordTrace tailWord_4681644 prefixEnd_4681644 2403933625237786280019517 := by
  unfold tailWord_4681644
  simp only [CollatzResearch.WordTrace]
  refine ⟨85376792325605411991997993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113835723100807215989330657 85376792325605411991997993)
  ·
    refine ⟨64032594244204058993998495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85376792325605411991997993 64032594244204058993998495)
    ·
      refine ⟨96048891366306088490997743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64032594244204058993998495 96048891366306088490997743)
      ·
        refine ⟨144073337049459132736496615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96048891366306088490997743 144073337049459132736496615)
        ·
          refine ⟨216110005574188699104744923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144073337049459132736496615 216110005574188699104744923)
          ·
            refine ⟨324165008361283048657117385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216110005574188699104744923 324165008361283048657117385)
            ·
              refine ⟨243123756270962286492838039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324165008361283048657117385 243123756270962286492838039)
              ·
                refine ⟨364685634406443429739257059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243123756270962286492838039 364685634406443429739257059)
                ·
                  refine ⟨547028451609665144608885589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364685634406443429739257059 547028451609665144608885589)
                  ·
                    refine ⟨3205244833650381706692689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 547028451609665144608885589 3205244833650381706692689)
                    ·
                      refine ⟨2403933625237786280019517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205244833650381706692689 2403933625237786280019517)
                      ·
                        rfl

theorem cell23_4681644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_4681644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681644 prefixEnd_4681644 := by exact prefixLift 4681644
  have htrace : WordTrace (prefixWord ++ tailWord_4681644) baseStart_4681644 baseEnd_4681644 := by
    simpa [prefixWord, tailWord_4681644, baseEnd_4681644] using wordTrace_append hprefix tailTrace_4681644
  have hstable : (prefixWord ++ tailWord_4681644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681644).length < 2 ^ (prefixWord ++ tailWord_4681644).sum := by decide
  have hdescent : baseEnd_4681644 < baseStart_4681644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681651 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 3]
def baseStart_4681651 : Nat := 118140960795 + 4681651 * 2 ^ 59
def prefixEnd_4681651 : Nat := 4983230072969 + 3 ^ 40 * 4681651 * 2
def baseEnd_4681651 : Nat := 2403937219602367752631985

theorem tailTrace_4681651 : CollatzResearch.WordTrace tailWord_4681651 prefixEnd_4681651 2403937219602367752631985 := by
  unfold tailWord_4681651
  simp only [CollatzResearch.WordTrace]
  refine ⟨170753839962185464179500807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113835893308123642786333871 170753839962185464179500807)
  ·
    refine ⟨256130759943278196269251211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170753839962185464179500807 256130759943278196269251211)
    ·
      refine ⟨384196139914917294403876817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256130759943278196269251211 384196139914917294403876817)
      ·
        refine ⟨288147104936187970802907613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384196139914917294403876817 288147104936187970802907613)
        ·
          refine ⟨108055164351070489051090355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288147104936187970802907613 108055164351070489051090355)
          ·
            refine ⟨162082746526605733576635533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108055164351070489051090355 162082746526605733576635533)
            ·
              refine ⟨60781029947477150091238325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162082746526605733576635533 60781029947477150091238325)
              ·
                refine ⟨5698221557575982821053593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60781029947477150091238325 5698221557575982821053593)
                ·
                  refine ⟨4273666168181987115790195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698221557575982821053593 4273666168181987115790195)
                  ·
                    refine ⟨6410499252272980673685293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273666168181987115790195 6410499252272980673685293)
                    ·
                      refine ⟨2403937219602367752631985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6410499252272980673685293 2403937219602367752631985)
                      ·
                        rfl

theorem cell23_4681651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 3].length) (baseStart_4681651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681651 prefixEnd_4681651 := by exact prefixLift 4681651
  have htrace : WordTrace (prefixWord ++ tailWord_4681651) baseStart_4681651 baseEnd_4681651 := by
    simpa [prefixWord, tailWord_4681651, baseEnd_4681651] using wordTrace_append hprefix tailTrace_4681651
  have hstable : (prefixWord ++ tailWord_4681651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681651).length < 2 ^ (prefixWord ++ tailWord_4681651).sum := by decide
  have hdescent : baseEnd_4681651 < baseStart_4681651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681652 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_4681652 : Nat := 118140960795 + 4681652 * 2 ^ 59
def prefixEnd_4681652 : Nat := 4983230072969 + 3 ^ 40 * 4681652 * 2
def baseEnd_4681652 : Nat := 2403937733083022248719481

theorem tailTrace_4681652 : CollatzResearch.WordTrace tailWord_4681652 prefixEnd_4681652 2403937733083022248719481 := by
  unfold tailWord_4681652
  simp only [CollatzResearch.WordTrace]
  refine ⟨85376938217590920675143605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113835917623454560900191473 85376938217590920675143605)
  ·
    refine ⟨8004087957899148813294713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85376938217590920675143605 8004087957899148813294713)
    ·
      refine ⟨6003065968424361609971035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8004087957899148813294713 6003065968424361609971035)
      ·
        refine ⟨9004598952636542414956553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6003065968424361609971035 9004598952636542414956553)
        ·
          refine ⟨6753449214477406811217415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9004598952636542414956553 6753449214477406811217415)
          ·
            refine ⟨10130173821716110216826123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6753449214477406811217415 10130173821716110216826123)
            ·
              refine ⟨15195260732574165325239185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10130173821716110216826123 15195260732574165325239185)
              ·
                refine ⟨11396445549430623993929389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15195260732574165325239185 11396445549430623993929389)
                ·
                  refine ⟨4273667081036483997723521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11396445549430623993929389 4273667081036483997723521)
                  ·
                    refine ⟨3205250310777362998292641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4273667081036483997723521 3205250310777362998292641)
                    ·
                      refine ⟨2403937733083022248719481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205250310777362998292641 2403937733083022248719481)
                      ·
                        rfl

theorem cell23_4681652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_4681652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681652 prefixEnd_4681652 := by exact prefixLift 4681652
  have htrace : WordTrace (prefixWord ++ tailWord_4681652) baseStart_4681652 baseEnd_4681652 := by
    simpa [prefixWord, tailWord_4681652, baseEnd_4681652] using wordTrace_append hprefix tailTrace_4681652
  have hstable : (prefixWord ++ tailWord_4681652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681652).length < 2 ^ (prefixWord ++ tailWord_4681652).sum := by decide
  have hdescent : baseEnd_4681652 < baseStart_4681652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681667 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 6, 6]
def baseStart_4681667 : Nat := 118140960795 + 4681667 * 2 ^ 59
def prefixEnd_4681667 : Nat := 4983230072969 + 3 ^ 40 * 4681667 * 2
def baseEnd_4681667 : Nat := 801315145097613230010637

theorem tailTrace_4681667 : CollatzResearch.WordTrace tailWord_4681667 prefixEnd_4681667 801315145097613230010637 := by
  unfold tailWord_4681667
  simp only [CollatzResearch.WordTrace]
  refine ⟨170754423530127498912083255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113836282353418332608055503 170754423530127498912083255)
  ·
    refine ⟨256131635295191248368124883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170754423530127498912083255 256131635295191248368124883)
    ·
      refine ⟨384197452942786872552187325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256131635295191248368124883 384197452942786872552187325)
      ·
        refine ⟨144074044853545077207070247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384197452942786872552187325 144074044853545077207070247)
        ·
          refine ⟨216111067280317615810605371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144074044853545077207070247 216111067280317615810605371)
          ·
            refine ⟨324166600920476423715908057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216111067280317615810605371 324166600920476423715908057)
            ·
              refine ⟨243124950690357317786931043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324166600920476423715908057 243124950690357317786931043)
              ·
                refine ⟨364687426035535976680396565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243124950690357317786931043 364687426035535976680396565)
                ·
                  refine ⟨17094723095415748906893589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 364687426035535976680396565 17094723095415748906893589)
                  ·
                    refine ⟨801315145097613230010637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17094723095415748906893589 801315145097613230010637)
                    ·
                      rfl

theorem cell23_4681667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 6].length) (baseStart_4681667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681667 prefixEnd_4681667 := by exact prefixLift 4681667
  have htrace : WordTrace (prefixWord ++ tailWord_4681667) baseStart_4681667 baseEnd_4681667 := by
    simpa [prefixWord, tailWord_4681667, baseEnd_4681667] using wordTrace_append hprefix tailTrace_4681667
  have hstable : (prefixWord ++ tailWord_4681667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681667).length < 2 ^ (prefixWord ++ tailWord_4681667).sum := by decide
  have hdescent : baseEnd_4681667 < baseStart_4681667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681678 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_4681678 : Nat := 118140960795 + 4681678 * 2 ^ 59
def prefixEnd_4681678 : Nat := 4983230072969 + 3 ^ 40 * 4681678 * 2
def baseEnd_4681678 : Nat := 2403951083580039146994361

theorem tailTrace_4681678 : CollatzResearch.WordTrace tailWord_4681678 prefixEnd_4681678 2403951083580039146994361 := by
  unfold tailWord_4681678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21344353091635955973841711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113836549822058431860489125 21344353091635955973841711)
  ·
    refine ⟨32016529637453933960762567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21344353091635955973841711 32016529637453933960762567)
    ·
      refine ⟨48024794456180900941143851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32016529637453933960762567 48024794456180900941143851)
      ·
        refine ⟨72037191684271351411715777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48024794456180900941143851 72037191684271351411715777)
        ·
          refine ⟨54027893763203513558786833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72037191684271351411715777 54027893763203513558786833)
          ·
            refine ⟨40520920322402635169090125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54027893763203513558786833 40520920322402635169090125)
            ·
              refine ⟨15195345120900988188408797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40520920322402635169090125 15195345120900988188408797)
              ·
                refine ⟨5698254420337870570653299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15195345120900988188408797 5698254420337870570653299)
                ·
                  refine ⟨8547381630506805855979949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5698254420337870570653299 8547381630506805855979949)
                  ·
                    refine ⟨3205268111440052195992481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8547381630506805855979949 3205268111440052195992481)
                    ·
                      refine ⟨2403951083580039146994361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205268111440052195992481 2403951083580039146994361)
                      ·
                        rfl

theorem cell23_4681678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_4681678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681678 prefixEnd_4681678 := by exact prefixLift 4681678
  have htrace : WordTrace (prefixWord ++ tailWord_4681678) baseStart_4681678 baseEnd_4681678 := by
    simpa [prefixWord, tailWord_4681678, baseEnd_4681678] using wordTrace_append hprefix tailTrace_4681678
  have hstable : (prefixWord ++ tailWord_4681678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681678).length < 2 ^ (prefixWord ++ tailWord_4681678).sum := by decide
  have hdescent : baseEnd_4681678 < baseStart_4681678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681684 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_4681684 : Nat := 118140960795 + 4681684 * 2 ^ 59
def prefixEnd_4681684 : Nat := 4983230072969 + 3 ^ 40 * 4681684 * 2
def baseEnd_4681684 : Nat := 801318054821322041173111

theorem tailTrace_4681684 : CollatzResearch.WordTrace tailWord_4681684 prefixEnd_4681684 801318054821322041173111 := by
  unfold tailWord_4681684
  simp only [CollatzResearch.WordTrace]
  refine ⟨85377521785532955407726053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113836695714043940543634737 85377521785532955407726053)
  ·
    refine ⟨16008285334787429138948635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85377521785532955407726053 16008285334787429138948635)
    ·
      refine ⟨24012428002181143708422953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16008285334787429138948635 24012428002181143708422953)
      ·
        refine ⟨18009321001635857781317215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24012428002181143708422953 18009321001635857781317215)
        ·
          refine ⟨27013981502453786671975823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18009321001635857781317215 27013981502453786671975823)
          ·
            refine ⟨40520972253680680007963735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27013981502453786671975823 40520972253680680007963735)
            ·
              refine ⟨60781458380521020011945603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40520972253680680007963735 60781458380521020011945603)
              ·
                refine ⟨91172187570781530017918405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60781458380521020011945603 91172187570781530017918405)
                ·
                  refine ⟨17094785169521536878359701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91172187570781530017918405 17094785169521536878359701)
                  ·
                    refine ⟨801318054821322041173111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17094785169521536878359701 801318054821322041173111)
                    ·
                      rfl

theorem cell23_4681684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_4681684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681684 prefixEnd_4681684 := by exact prefixLift 4681684
  have htrace : WordTrace (prefixWord ++ tailWord_4681684) baseStart_4681684 baseEnd_4681684 := by
    simpa [prefixWord, tailWord_4681684, baseEnd_4681684] using wordTrace_append hprefix tailTrace_4681684
  have hstable : (prefixWord ++ tailWord_4681684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681684).length < 2 ^ (prefixWord ++ tailWord_4681684).sum := by decide
  have hdescent : baseEnd_4681684 < baseStart_4681684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681685 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4681685 : Nat := 118140960795 + 4681685 * 2 ^ 59
def prefixEnd_4681685 : Nat := 4983230072969 + 3 ^ 40 * 4681685 * 2
def baseEnd_4681685 : Nat := 2403954677944620619606829

theorem tailTrace_4681685 : CollatzResearch.WordTrace tailWord_4681685 prefixEnd_4681685 2403954677944620619606829 := by
  unfold tailWord_4681685
  simp only [CollatzResearch.WordTrace]
  refine ⟨170755080044062287986238509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113836720029374858657492339 170755080044062287986238509)
  ·
    refine ⟨64033155016523357994839441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170755080044062287986238509 64033155016523357994839441)
    ·
      refine ⟨48024866262392518496129581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64033155016523357994839441 48024866262392518496129581)
      ·
        refine ⟨18009324848397194436048593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48024866262392518496129581 18009324848397194436048593)
        ·
          refine ⟨13506993636297895827036445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18009324848397194436048593 13506993636297895827036445)
          ·
            refine ⟨5065122613611710935138667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13506993636297895827036445 5065122613611710935138667)
            ·
              refine ⟨7597683920417566402708001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065122613611710935138667 7597683920417566402708001)
              ·
                refine ⟨5698262940313174802031001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7597683920417566402708001 5698262940313174802031001)
                ·
                  refine ⟨4273697205234881101523251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698262940313174802031001 4273697205234881101523251)
                  ·
                    refine ⟨6410545807852321652284877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273697205234881101523251 6410545807852321652284877)
                    ·
                      refine ⟨2403954677944620619606829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6410545807852321652284877 2403954677944620619606829)
                      ·
                        rfl

theorem cell23_4681685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4681685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681685 prefixEnd_4681685 := by exact prefixLift 4681685
  have htrace : WordTrace (prefixWord ++ tailWord_4681685) baseStart_4681685 baseEnd_4681685 := by
    simpa [prefixWord, tailWord_4681685, baseEnd_4681685] using wordTrace_append hprefix tailTrace_4681685
  have hstable : (prefixWord ++ tailWord_4681685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681685).length < 2 ^ (prefixWord ++ tailWord_4681685).sum := by decide
  have hdescent : baseEnd_4681685 < baseStart_4681685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681707 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9]
def baseStart_4681707 : Nat := 118140960795 + 4681707 * 2 ^ 59
def prefixEnd_4681707 : Nat := 4983230072969 + 3 ^ 40 * 4681707 * 2
def baseEnd_4681707 : Nat := 2403965974519019533531727

theorem tailTrace_4681707 : CollatzResearch.WordTrace tailWord_4681707 prefixEnd_4681707 2403965974519019533531727 := by
  unfold tailWord_4681707
  simp only [CollatzResearch.WordTrace]
  refine ⟨170755882449982585743539375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113837254966655057162359583 170755882449982585743539375)
  ·
    refine ⟨256133823674973878615309063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170755882449982585743539375 256133823674973878615309063)
    ·
      refine ⟨384200735512460817922963595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256133823674973878615309063 384200735512460817922963595)
      ·
        refine ⟨576301103268691226884445393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384200735512460817922963595 576301103268691226884445393)
        ·
          refine ⟨432225827451518420163334045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576301103268691226884445393 432225827451518420163334045)
          ·
            refine ⟨162084685294319407561250267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 432225827451518420163334045 162084685294319407561250267)
            ·
              refine ⟨243127027941479111341875401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162084685294319407561250267 243127027941479111341875401)
              ·
                refine ⟨182345270956109333506406551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243127027941479111341875401 182345270956109333506406551)
                ·
                  refine ⟨273517906434164000259609827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182345270956109333506406551 273517906434164000259609827)
                  ·
                    refine ⟨410276859651246000389414741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 273517906434164000259609827 410276859651246000389414741)
                    ·
                      refine ⟨2403965974519019533531727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 410276859651246000389414741 2403965974519019533531727)
                      ·
                        rfl

theorem cell23_4681707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_4681707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681707 prefixEnd_4681707 := by exact prefixLift 4681707
  have htrace : WordTrace (prefixWord ++ tailWord_4681707) baseStart_4681707 baseEnd_4681707 := by
    simpa [prefixWord, tailWord_4681707, baseEnd_4681707] using wordTrace_append hprefix tailTrace_4681707
  have hstable : (prefixWord ++ tailWord_4681707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681707).length < 2 ^ (prefixWord ++ tailWord_4681707).sum := by decide
  have hdescent : baseEnd_4681707 < baseStart_4681707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681708 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 2, 2, 2]
def baseStart_4681708 : Nat := 118140960795 + 4681708 * 2 ^ 59
def prefixEnd_4681708 : Nat := 4983230072969 + 3 ^ 40 * 4681708 * 2
def baseEnd_4681708 : Nat := 2403966487999674029619223

theorem tailTrace_4681708 : CollatzResearch.WordTrace tailWord_4681708 prefixEnd_4681708 2403966487999674029619223 := by
  unfold tailWord_4681708
  simp only [CollatzResearch.WordTrace]
  refine ⟨85377959461489481457162889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113837279281985975276217185 85377959461489481457162889)
  ·
    refine ⟨64033469596117111092872167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85377959461489481457162889 64033469596117111092872167)
    ·
      refine ⟨96050204394175666639308251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64033469596117111092872167 96050204394175666639308251)
      ·
        refine ⟨144075306591263499958962377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96050204394175666639308251 144075306591263499958962377)
        ·
          refine ⟨108056479943447624969221783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144075306591263499958962377 108056479943447624969221783)
          ·
            refine ⟨162084719915171437453832675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108056479943447624969221783 162084719915171437453832675)
            ·
              refine ⟨243127079872757156180749013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162084719915171437453832675 243127079872757156180749013)
              ·
                refine ⟨5698290934517745847986305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 243127079872757156180749013 5698290934517745847986305)
                ·
                  refine ⟨4273718200888309385989729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698290934517745847986305 4273718200888309385989729)
                  ·
                    refine ⟨3205288650666232039492297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4273718200888309385989729 3205288650666232039492297)
                    ·
                      refine ⟨2403966487999674029619223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205288650666232039492297 2403966487999674029619223)
                      ·
                        rfl

theorem cell23_4681708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_4681708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681708 prefixEnd_4681708 := by exact prefixLift 4681708
  have htrace : WordTrace (prefixWord ++ tailWord_4681708) baseStart_4681708 baseEnd_4681708 := by
    simpa [prefixWord, tailWord_4681708, baseEnd_4681708] using wordTrace_append hprefix tailTrace_4681708
  have hstable : (prefixWord ++ tailWord_4681708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681708).length < 2 ^ (prefixWord ++ tailWord_4681708).sum := by decide
  have hdescent : baseEnd_4681708 < baseStart_4681708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681744 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 2, 5]
def baseStart_4681744 : Nat := 118140960795 + 4681744 * 2 ^ 59
def prefixEnd_4681744 : Nat := 4983230072969 + 3 ^ 40 * 4681744 * 2
def baseEnd_4681744 : Nat := 801328324434411962923019

theorem tailTrace_4681744 : CollatzResearch.WordTrace tailWord_4681744 prefixEnd_4681744 801328324434411962923019 := by
  unfold tailWord_4681744
  simp only [CollatzResearch.WordTrace]
  refine ⟨85378615975424270531318143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113838154633899027375090857 85378615975424270531318143)
  ·
    refine ⟨128067923963136405796977215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85378615975424270531318143 128067923963136405796977215)
    ·
      refine ⟨192101885944704608695465823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128067923963136405796977215 192101885944704608695465823)
      ·
        refine ⟨288152828917056913043198735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192101885944704608695465823 288152828917056913043198735)
        ·
          refine ⟨432229243375585369564798103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288152828917056913043198735 432229243375585369564798103)
          ·
            refine ⟨648343865063378054347197155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432229243375585369564798103 648343865063378054347197155)
            ·
              refine ⟨972515797595067081520795733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648343865063378054347197155 972515797595067081520795733)
              ·
                refine ⟨11396669503067192361571825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 972515797595067081520795733 11396669503067192361571825)
                ·
                  refine ⟨8547502127300394271178869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11396669503067192361571825 8547502127300394271178869)
                  ·
                    refine ⟨801328324434411962923019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8547502127300394271178869 801328324434411962923019)
                    ·
                      rfl

theorem cell23_4681744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_4681744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681744 prefixEnd_4681744 := by exact prefixLift 4681744
  have htrace : WordTrace (prefixWord ++ tailWord_4681744) baseStart_4681744 baseEnd_4681744 := by
    simpa [prefixWord, tailWord_4681744, baseEnd_4681744] using wordTrace_append hprefix tailTrace_4681744
  have hstable : (prefixWord ++ tailWord_4681744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681744).length < 2 ^ (prefixWord ++ tailWord_4681744).sum := by decide
  have hdescent : baseEnd_4681744 < baseStart_4681744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681754 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_4681754 : Nat := 118140960795 + 4681754 * 2 ^ 59
def prefixEnd_4681754 : Nat := 4983230072969 + 3 ^ 40 * 4681754 * 2
def baseEnd_4681754 : Nat := 2403990108109780849644011

theorem tailTrace_4681754 : CollatzResearch.WordTrace tailWord_4681754 prefixEnd_4681754 2403990108109780849644011 := by
  unfold tailWord_4681754
  simp only [CollatzResearch.WordTrace]
  refine ⟨42689399170203078192625079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113838397787208208513666877 42689399170203078192625079)
  ·
    refine ⟨64034098755304617288937619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42689399170203078192625079 64034098755304617288937619)
    ·
      refine ⟨96051148132956925933406429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64034098755304617288937619 96051148132956925933406429)
      ·
        refine ⟨36019180549858847225027411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96051148132956925933406429 36019180549858847225027411)
        ·
          refine ⟨54028770824788270837541117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36019180549858847225027411 54028770824788270837541117)
          ·
            refine ⟨20260789059295601564077919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54028770824788270837541117 20260789059295601564077919)
            ·
              refine ⟨30391183588943402346116879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20260789059295601564077919 30391183588943402346116879)
              ·
                refine ⟨45586775383415103519175319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30391183588943402346116879 45586775383415103519175319)
                ·
                  refine ⟨68380163075122655278762979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45586775383415103519175319 68380163075122655278762979)
                  ·
                    refine ⟨102570244612683982918144469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68380163075122655278762979 102570244612683982918144469)
                    ·
                      refine ⟨2403990108109780849644011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102570244612683982918144469 2403990108109780849644011)
                      ·
                        rfl

theorem cell23_4681754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_4681754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681754 prefixEnd_4681754 := by exact prefixLift 4681754
  have htrace : WordTrace (prefixWord ++ tailWord_4681754) baseStart_4681754 baseEnd_4681754 := by
    simpa [prefixWord, tailWord_4681754, baseEnd_4681754] using wordTrace_append hprefix tailTrace_4681754
  have hstable : (prefixWord ++ tailWord_4681754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681754).length < 2 ^ (prefixWord ++ tailWord_4681754).sum := by decide
  have hdescent : baseEnd_4681754 < baseStart_4681754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681781 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4681781 : Nat := 118140960795 + 4681781 * 2 ^ 59
def prefixEnd_4681781 : Nat := 4983230072969 + 3 ^ 40 * 4681781 * 2
def baseEnd_4681781 : Nat := 2404003972087452244006387

theorem tailTrace_4681781 : CollatzResearch.WordTrace tailWord_4681781 prefixEnd_4681781 2404003972087452244006387 := by
  unfold tailWord_4681781
  simp only [CollatzResearch.WordTrace]
  refine ⟨170758581451714496381733197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113839054301142997587822131 170758581451714496381733197)
  ·
    refine ⟨64034468044392936143149949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170758581451714496381733197 64034468044392936143149949)
    ·
      refine ⟨24012925516647351053681231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64034468044392936143149949 24012925516647351053681231)
      ·
        refine ⟨36019388274971026580521847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24012925516647351053681231 36019388274971026580521847)
        ·
          refine ⟨54029082412456539870782771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36019388274971026580521847 54029082412456539870782771)
          ·
            refine ⟨81043623618684809806174157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54029082412456539870782771 81043623618684809806174157)
            ·
              refine ⟨30391358857006803677315309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81043623618684809806174157 30391358857006803677315309)
              ·
                refine ⟨11396759571377551378993241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30391358857006803677315309 11396759571377551378993241)
                ·
                  refine ⟨8547569678533163534244931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11396759571377551378993241 8547569678533163534244931)
                  ·
                    refine ⟨12821354517799745301367397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8547569678533163534244931 12821354517799745301367397)
                    ·
                      refine ⟨2404003972087452244006387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12821354517799745301367397 2404003972087452244006387)
                      ·
                        rfl

theorem cell23_4681781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4681781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681781 prefixEnd_4681781 := by exact prefixLift 4681781
  have htrace : WordTrace (prefixWord ++ tailWord_4681781) baseStart_4681781 baseEnd_4681781 := by
    simpa [prefixWord, tailWord_4681781, baseEnd_4681781] using wordTrace_append hprefix tailTrace_4681781
  have hstable : (prefixWord ++ tailWord_4681781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681781).length < 2 ^ (prefixWord ++ tailWord_4681781).sum := by decide
  have hdescent : baseEnd_4681781 < baseStart_4681781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681801 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 3]
def baseStart_4681801 : Nat := 118140960795 + 4681801 * 2 ^ 59
def prefixEnd_4681801 : Nat := 4983230072969 + 3 ^ 40 * 4681801 * 2
def baseEnd_4681801 : Nat := 2404014241700542165756295

theorem tailTrace_4681801 : CollatzResearch.WordTrace tailWord_4681801 prefixEnd_4681801 2404014241700542165756295 := by
  unfold tailWord_4681801
  simp only [CollatzResearch.WordTrace]
  refine ⟨170759310911642039797461257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113839540607761359864974171 170759310911642039797461257)
  ·
    refine ⟨128069483183731529848095943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170759310911642039797461257 128069483183731529848095943)
    ·
      refine ⟨192104224775597294772143915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128069483183731529848095943 192104224775597294772143915)
      ·
        refine ⟨288156337163395942158215873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192104224775597294772143915 288156337163395942158215873)
        ·
          refine ⟨216117252872546956618661905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288156337163395942158215873 216117252872546956618661905)
          ·
            refine ⟨162087939654410217463996429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216117252872546956618661905 162087939654410217463996429)
            ·
              refine ⟨60782977370403831548998661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162087939654410217463996429 60782977370403831548998661)
              ·
                refine ⟨11396808256950718415437249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60782977370403831548998661 11396808256950718415437249)
                ·
                  refine ⟨8547606192713038811577937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11396808256950718415437249 8547606192713038811577937)
                  ·
                    refine ⟨6410704644534779108683453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8547606192713038811577937 6410704644534779108683453)
                    ·
                      refine ⟨2404014241700542165756295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6410704644534779108683453 2404014241700542165756295)
                      ·
                        rfl

theorem cell23_4681801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_4681801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681801 prefixEnd_4681801 := by exact prefixLift 4681801
  have htrace : WordTrace (prefixWord ++ tailWord_4681801) baseStart_4681801 baseEnd_4681801 := by
    simpa [prefixWord, tailWord_4681801, baseEnd_4681801] using wordTrace_append hprefix tailTrace_4681801
  have hstable : (prefixWord ++ tailWord_4681801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681801).length < 2 ^ (prefixWord ++ tailWord_4681801).sum := by decide
  have hdescent : baseEnd_4681801 < baseStart_4681801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681804 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 8]
def baseStart_4681804 : Nat := 118140960795 + 4681804 * 2 ^ 59
def prefixEnd_4681804 : Nat := 4983230072969 + 3 ^ 40 * 4681804 * 2
def baseEnd_4681804 : Nat := 267112864682500628224309

theorem tailTrace_4681804 : CollatzResearch.WordTrace tailWord_4681804 prefixEnd_4681804 267112864682500628224309 := by
  unfold tailWord_4681804
  simp only [CollatzResearch.WordTrace]
  refine ⟨85379710165315585654910233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113839613553754114206546977 85379710165315585654910233)
  ·
    refine ⟨64034782623986689241182675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85379710165315585654910233 64034782623986689241182675)
    ·
      refine ⟨96052173935980033861774013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64034782623986689241182675 96052173935980033861774013)
      ·
        refine ⟨36019565225992512698165255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96052173935980033861774013 36019565225992512698165255)
        ·
          refine ⟨54029347838988769047247883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36019565225992512698165255 54029347838988769047247883)
          ·
            refine ⟨81044021758483153570871825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54029347838988769047247883 81044021758483153570871825)
            ·
              refine ⟨60783016318862365178153869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81044021758483153570871825 60783016318862365178153869)
              ·
                refine ⟨22793631119573386941807701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60783016318862365178153869 22793631119573386941807701)
                ·
                  refine ⟨267112864682500628224309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22793631119573386941807701 267112864682500628224309)
                  ·
                    rfl

theorem cell23_4681804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_4681804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681804 prefixEnd_4681804 := by exact prefixLift 4681804
  have htrace : WordTrace (prefixWord ++ tailWord_4681804) baseStart_4681804 baseEnd_4681804 := by
    simpa [prefixWord, tailWord_4681804, baseEnd_4681804] using wordTrace_append hprefix tailTrace_4681804
  have hstable : (prefixWord ++ tailWord_4681804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681804).length < 2 ^ (prefixWord ++ tailWord_4681804).sum := by decide
  have hdescent : baseEnd_4681804 < baseStart_4681804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681865 : List Nat := [1, 2, 1, 1, 4, 2, 1, 6, 1, 1, 3]
def baseStart_4681865 : Nat := 118140960795 + 4681865 * 2 ^ 59
def prefixEnd_4681865 : Nat := 4983230072969 + 3 ^ 40 * 4681865 * 2
def baseEnd_4681865 : Nat := 2404047104462429915356001

theorem tailTrace_4681865 : CollatzResearch.WordTrace tailWord_4681865 prefixEnd_4681865 2404047104462429915356001 := by
  unfold tailWord_4681865
  simp only [CollatzResearch.WordTrace]
  refine ⟨170761645183410178727791049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113841096788940119151860699 170761645183410178727791049)
  ·
    refine ⟨128071233887557634045843287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170761645183410178727791049 128071233887557634045843287)
    ·
      refine ⟨192106850831336451068764931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128071233887557634045843287 192106850831336451068764931)
      ·
        refine ⟨288160276247004676603147397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192106850831336451068764931 288160276247004676603147397)
        ·
          refine ⟨54030051796313376863090137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288160276247004676603147397 54030051796313376863090137)
          ·
            refine ⟨40522538847235032647317603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54030051796313376863090137 40522538847235032647317603)
            ·
              refine ⟨60783808270852548970976405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40522538847235032647317603 60783808270852548970976405)
              ·
                refine ⟨2849241012696213233014519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60783808270852548970976405 2849241012696213233014519)
                ·
                  refine ⟨4273861519044319849521779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849241012696213233014519 4273861519044319849521779)
                  ·
                    refine ⟨6410792278566479774282669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273861519044319849521779 6410792278566479774282669)
                    ·
                      refine ⟨2404047104462429915356001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6410792278566479774282669 2404047104462429915356001)
                      ·
                        rfl

theorem cell23_4681865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 1, 3].length) (baseStart_4681865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681865 prefixEnd_4681865 := by exact prefixLift 4681865
  have htrace : WordTrace (prefixWord ++ tailWord_4681865) baseStart_4681865 baseEnd_4681865 := by
    simpa [prefixWord, tailWord_4681865, baseEnd_4681865] using wordTrace_append hprefix tailTrace_4681865
  have hstable : (prefixWord ++ tailWord_4681865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681865).length < 2 ^ (prefixWord ++ tailWord_4681865).sum := by decide
  have hdescent : baseEnd_4681865 < baseStart_4681865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681888 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4]
def baseStart_4681888 : Nat := 118140960795 + 4681888 * 2 ^ 59
def prefixEnd_4681888 : Nat := 4983230072969 + 3 ^ 40 * 4681888 * 2
def baseEnd_4681888 : Nat := 2404058914517483325368395

theorem tailTrace_4681888 : CollatzResearch.WordTrace tailWord_4681888 prefixEnd_4681888 2404058914517483325368395 := by
  unfold tailWord_4681888
  simp only [CollatzResearch.WordTrace]
  refine ⟨85381242031163426827939159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113841656041551235770585545 85381242031163426827939159)
  ·
    refine ⟨128071863046745140241908739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85381242031163426827939159 128071863046745140241908739)
    ·
      refine ⟨192107794570117710362863109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128071863046745140241908739 192107794570117710362863109)
      ·
        refine ⟨36020211481897070693036833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192107794570117710362863109 36020211481897070693036833)
        ·
          refine ⟨27015158611422803019777625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36020211481897070693036833 27015158611422803019777625)
          ·
            refine ⟨20261368958567102264833219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27015158611422803019777625 20261368958567102264833219)
            ·
              refine ⟨30392053437850653397249829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20261368958567102264833219 30392053437850653397249829)
              ·
                refine ⟨5698510019596997511984343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30392053437850653397249829 5698510019596997511984343)
                ·
                  refine ⟨8547765029395496267976515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5698510019596997511984343 8547765029395496267976515)
                  ·
                    refine ⟨12821647544093244401964773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8547765029395496267976515 12821647544093244401964773)
                    ·
                      refine ⟨2404058914517483325368395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12821647544093244401964773 2404058914517483325368395)
                      ·
                        rfl

theorem cell23_4681888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_4681888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681888 prefixEnd_4681888 := by exact prefixLift 4681888
  have htrace : WordTrace (prefixWord ++ tailWord_4681888) baseStart_4681888 baseEnd_4681888 := by
    simpa [prefixWord, tailWord_4681888, baseEnd_4681888] using wordTrace_append hprefix tailTrace_4681888
  have hstable : (prefixWord ++ tailWord_4681888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681888).length < 2 ^ (prefixWord ++ tailWord_4681888).sum := by decide
  have hdescent : baseEnd_4681888 < baseStart_4681888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681911 : List Nat := [1, 1, 3, 1, 4, 4, 9]
def baseStart_4681911 : Nat := 118140960795 + 4681911 * 2 ^ 59
def prefixEnd_4681911 : Nat := 4983230072969 + 3 ^ 40 * 4681911 * 2
def baseEnd_4681911 : Nat := 29679885488549836239269

theorem tailTrace_4681911 : CollatzResearch.WordTrace tailWord_4681911 prefixEnd_4681911 29679885488549836239269 := by
  unfold tailWord_4681911
  simp only [CollatzResearch.WordTrace]
  refine ⟨170763322941243528583965587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113842215294162352389310391 170763322941243528583965587)
  ·
    refine ⟨256144984411865292875948381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170763322941243528583965587 256144984411865292875948381)
    ·
      refine ⟨96054369154449484828480643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256144984411865292875948381 96054369154449484828480643)
      ·
        refine ⟨144081553731674227242720965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96054369154449484828480643 144081553731674227242720965)
        ·
          refine ⟨27015291324688917608010181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144081553731674227242720965 27015291324688917608010181)
          ·
            refine ⟨5065367123379172051501909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27015291324688917608010181 5065367123379172051501909)
            ·
              refine ⟨29679885488549836239269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5065367123379172051501909 29679885488549836239269)
              ·
                rfl

theorem cell23_4681911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 9].length) (baseStart_4681911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681911 prefixEnd_4681911 := by exact prefixLift 4681911
  have htrace : WordTrace (prefixWord ++ tailWord_4681911) baseStart_4681911 baseEnd_4681911 := by
    simpa [prefixWord, tailWord_4681911, baseEnd_4681911] using wordTrace_append hprefix tailTrace_4681911
  have hstable : (prefixWord ++ tailWord_4681911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681911).length < 2 ^ (prefixWord ++ tailWord_4681911).sum := by decide
  have hdescent : baseEnd_4681911 < baseStart_4681911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681932 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_4681932 : Nat := 118140960795 + 4681932 * 2 ^ 59
def prefixEnd_4681932 : Nat := 4983230072969 + 3 ^ 40 * 4681932 * 2
def baseEnd_4681932 : Nat := 801360502555427051072731

theorem tailTrace_4681932 : CollatzResearch.WordTrace tailWord_4681932 prefixEnd_4681932 801360502555427051072731 := by
  unfold tailWord_4681932
  simp only [CollatzResearch.WordTrace]
  refine ⟨85382044437083724585240025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113842725916111632780320033 85382044437083724585240025)
  ·
    refine ⟨64036533327812793438930019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85382044437083724585240025 64036533327812793438930019)
    ·
      refine ⟨96054799991719190158395029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64036533327812793438930019 96054799991719190158395029)
      ·
        refine ⟨4502568749611837038674767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96054799991719190158395029 4502568749611837038674767)
        ·
          refine ⟨6753853124417755558012151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502568749611837038674767 6753853124417755558012151)
          ·
            refine ⟨10130779686626633337018227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6753853124417755558012151 10130779686626633337018227)
            ·
              refine ⟨15196169529939950005527341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10130779686626633337018227 15196169529939950005527341)
              ·
                refine ⟨5698563573727481252072753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15196169529939950005527341 5698563573727481252072753)
                ·
                  refine ⟨4273922680295610939054565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698563573727481252072753 4273922680295610939054565)
                  ·
                    refine ⟨801360502555427051072731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273922680295610939054565 801360502555427051072731)
                    ·
                      rfl

theorem cell23_4681932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_4681932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681932 prefixEnd_4681932 := by exact prefixLift 4681932
  have htrace : WordTrace (prefixWord ++ tailWord_4681932) baseStart_4681932 baseEnd_4681932 := by
    simpa [prefixWord, tailWord_4681932, baseEnd_4681932] using wordTrace_append hprefix tailTrace_4681932
  have hstable : (prefixWord ++ tailWord_4681932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681932).length < 2 ^ (prefixWord ++ tailWord_4681932).sum := by decide
  have hdescent : baseEnd_4681932 < baseStart_4681932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681942 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4681942 : Nat := 118140960795 + 4681942 * 2 ^ 59
def prefixEnd_4681942 : Nat := 4983230072969 + 3 ^ 40 * 4681942 * 2
def baseEnd_4681942 : Nat := 2404086642472826114093147

theorem tailTrace_4681942 : CollatzResearch.WordTrace tailWord_4681942 prefixEnd_4681942 2404086642472826114093147 := by
  unfold tailWord_4681942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10672778350258201304896505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113842969069420813918896053 10672778350258201304896505)
  ·
    refine ⟨8004583762693650978672379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10672778350258201304896505 8004583762693650978672379)
    ·
      refine ⟨12006875644040476468008569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8004583762693650978672379 12006875644040476468008569)
      ·
        refine ⟨9005156733030357351006427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12006875644040476468008569 9005156733030357351006427)
        ·
          refine ⟨13507735099545536026509641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9005156733030357351006427 13507735099545536026509641)
          ·
            refine ⟨10130801324659152019882231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13507735099545536026509641 10130801324659152019882231)
            ·
              refine ⟨15196201986988728029823347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10130801324659152019882231 15196201986988728029823347)
              ·
                refine ⟨22794302980483092044735021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15196201986988728029823347 22794302980483092044735021)
                ·
                  refine ⟨8547863617681159516775633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22794302980483092044735021 8547863617681159516775633)
                  ·
                    refine ⟨6410897713260869637581725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8547863617681159516775633 6410897713260869637581725)
                    ·
                      refine ⟨2404086642472826114093147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6410897713260869637581725 2404086642472826114093147)
                      ·
                        rfl

theorem cell23_4681942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4681942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681942 prefixEnd_4681942 := by exact prefixLift 4681942
  have htrace : WordTrace (prefixWord ++ tailWord_4681942) baseStart_4681942 baseEnd_4681942 := by
    simpa [prefixWord, tailWord_4681942, baseEnd_4681942] using wordTrace_append hprefix tailTrace_4681942
  have hstable : (prefixWord ++ tailWord_4681942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681942).length < 2 ^ (prefixWord ++ tailWord_4681942).sum := by decide
  have hdescent : baseEnd_4681942 < baseStart_4681942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681971 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 2, 6]
def baseStart_4681971 : Nat := 118140960795 + 4681971 * 2 ^ 59
def prefixEnd_4681971 : Nat := 4983230072969 + 3 ^ 40 * 4681971 * 2
def baseEnd_4681971 : Nat := 801367177803935500210171

theorem tailTrace_4681971 : CollatzResearch.WordTrace tailWord_4681971 prefixEnd_4681971 801367177803935500210171 := by
  unfold tailWord_4681971
  simp only [CollatzResearch.WordTrace]
  refine ⟨170765511321026158831149767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113843674214017439220766511 170765511321026158831149767)
  ·
    refine ⟨256148266981539238246724651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170765511321026158831149767 256148266981539238246724651)
    ·
      refine ⟨384222400472308857370086977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256148266981539238246724651 384222400472308857370086977)
      ·
        refine ⟨288166800354231643027565233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384222400472308857370086977 288166800354231643027565233)
        ·
          refine ⟨216125100265673732270673925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288166800354231643027565233 216125100265673732270673925)
          ·
            refine ⟨40523456299813824800751361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216125100265673732270673925 40523456299813824800751361)
            ·
              refine ⟨30392592224860368600563521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40523456299813824800751361 30392592224860368600563521)
              ·
                refine ⟨22794444168645276450422641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30392592224860368600563521 22794444168645276450422641)
                ·
                  refine ⟨17095833126483957337816981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22794444168645276450422641 17095833126483957337816981)
                  ·
                    refine ⟨801367177803935500210171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17095833126483957337816981 801367177803935500210171)
                    ·
                      rfl

theorem cell23_4681971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 6].length) (baseStart_4681971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681971 prefixEnd_4681971 := by exact prefixLift 4681971
  have htrace : WordTrace (prefixWord ++ tailWord_4681971) baseStart_4681971 baseEnd_4681971 := by
    simpa [prefixWord, tailWord_4681971, baseEnd_4681971] using wordTrace_append hprefix tailTrace_4681971
  have hstable : (prefixWord ++ tailWord_4681971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681971).length < 2 ^ (prefixWord ++ tailWord_4681971).sum := by decide
  have hdescent : baseEnd_4681971 < baseStart_4681971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681981 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_4681981 : Nat := 118140960795 + 4681981 * 2 ^ 59
def prefixEnd_4681981 : Nat := 4983230072969 + 3 ^ 40 * 4681981 * 2
def baseEnd_4681981 : Nat := 2404106668218351461505467

theorem tailTrace_4681981 : CollatzResearch.WordTrace tailWord_4681981 prefixEnd_4681981 2404106668218351461505467 := by
  unfold tailWord_4681981
  simp only [CollatzResearch.WordTrace]
  refine ⟨170765876050989930539013797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113843917367326620359342531 170765876050989930539013797)
  ·
    refine ⟨32018601759560611976065087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170765876050989930539013797 32018601759560611976065087)
    ·
      refine ⟨48027902639340917964097631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32018601759560611976065087 48027902639340917964097631)
      ·
        refine ⟨72041853959011376946146447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48027902639340917964097631 72041853959011376946146447)
        ·
          refine ⟨108062780938517065419219671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72041853959011376946146447 108062780938517065419219671)
          ·
            refine ⟨162094171407775598128829507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108062780938517065419219671 162094171407775598128829507)
            ·
              refine ⟨243141257111663397193244261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162094171407775598128829507 243141257111663397193244261)
              ·
                refine ⟨45588985708436886973733299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243141257111663397193244261 45588985708436886973733299)
                ·
                  refine ⟨68383478562655330460599949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45588985708436886973733299 68383478562655330460599949)
                  ·
                    refine ⟨25643804460995748922724981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68383478562655330460599949 25643804460995748922724981)
                    ·
                      refine ⟨2404106668218351461505467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25643804460995748922724981 2404106668218351461505467)
                      ·
                        rfl

theorem cell23_4681981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_4681981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681981 prefixEnd_4681981 := by exact prefixLift 4681981
  have htrace : WordTrace (prefixWord ++ tailWord_4681981) baseStart_4681981 baseEnd_4681981 := by
    simpa [prefixWord, tailWord_4681981, baseEnd_4681981] using wordTrace_append hprefix tailTrace_4681981
  have hstable : (prefixWord ++ tailWord_4681981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681981).length < 2 ^ (prefixWord ++ tailWord_4681981).sum := by decide
  have hdescent : baseEnd_4681981 < baseStart_4681981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681995 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 1, 4, 2]
def baseStart_4681995 : Nat := 118140960795 + 4681995 * 2 ^ 59
def prefixEnd_4681995 : Nat := 4983230072969 + 3 ^ 40 * 4681995 * 2
def baseEnd_4681995 : Nat := 2404113856947514406730403

theorem tailTrace_4681995 : CollatzResearch.WordTrace tailWord_4681995 prefixEnd_4681995 2404113856947514406730403 := by
  unfold tailWord_4681995
  simp only [CollatzResearch.WordTrace]
  refine ⟨170766386672939210930023439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113844257781959473953348959 170766386672939210930023439)
  ·
    refine ⟨256149580009408816395035159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170766386672939210930023439 256149580009408816395035159)
    ·
      refine ⟨384224370014113224592552739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256149580009408816395035159 384224370014113224592552739)
      ·
        refine ⟨576336555021169836888829109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384224370014113224592552739 576336555021169836888829109)
        ·
          refine ⟨54031552033234672208327729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 576336555021169836888829109 54031552033234672208327729)
          ·
            refine ⟨40523664024926004156245797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54031552033234672208327729 40523664024926004156245797)
            ·
              refine ⟨7598187004673625779296087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40523664024926004156245797 7598187004673625779296087)
              ·
                refine ⟨11397280507010438668944131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7598187004673625779296087 11397280507010438668944131)
                ·
                  refine ⟨17095920760515658003416197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11397280507010438668944131 17095920760515658003416197)
                  ·
                    refine ⟨3205485142596685875640537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17095920760515658003416197 3205485142596685875640537)
                    ·
                      refine ⟨2404113856947514406730403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205485142596685875640537 2404113856947514406730403)
                      ·
                        rfl

theorem cell23_4681995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4, 2].length) (baseStart_4681995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681995 prefixEnd_4681995 := by exact prefixLift 4681995
  have htrace : WordTrace (prefixWord ++ tailWord_4681995) baseStart_4681995 baseEnd_4681995 := by
    simpa [prefixWord, tailWord_4681995, baseEnd_4681995] using wordTrace_append hprefix tailTrace_4681995
  have hstable : (prefixWord ++ tailWord_4681995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681995).length < 2 ^ (prefixWord ++ tailWord_4681995).sum := by decide
  have hdescent : baseEnd_4681995 < baseStart_4681995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4681998 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_4681998 : Nat := 118140960795 + 4681998 * 2 ^ 59
def prefixEnd_4681998 : Nat := 4983230072969 + 3 ^ 40 * 4681998 * 2
def baseEnd_4681998 : Nat := 2404115397389477894992889

theorem tailTrace_4681998 : CollatzResearch.WordTrace tailWord_4681998 prefixEnd_4681998 2404115397389477894992889 := by
  unfold tailWord_4681998
  simp only [CollatzResearch.WordTrace]
  refine ⟨21345812011491042805297831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113844330727952228294921765 21345812011491042805297831)
  ·
    refine ⟨32018718017236564207946747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21345812011491042805297831 32018718017236564207946747)
    ·
      refine ⟨48028077025854846311920121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32018718017236564207946747 48028077025854846311920121)
      ·
        refine ⟨36021057769391134733940091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48028077025854846311920121 36021057769391134733940091)
        ·
          refine ⟨54031586654086702100910137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36021057769391134733940091 54031586654086702100910137)
          ·
            refine ⟨40523689990565026575682603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54031586654086702100910137 40523689990565026575682603)
            ·
              refine ⟨60785534985847539863523905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40523689990565026575682603 60785534985847539863523905)
              ·
                refine ⟨45589151239385654897642929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60785534985847539863523905 45589151239385654897642929)
                ·
                  refine ⟨34191863429539241173232197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45589151239385654897642929 34191863429539241173232197)
                  ·
                    refine ⟨6410974393038607719981037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34191863429539241173232197 6410974393038607719981037)
                    ·
                      refine ⟨2404115397389477894992889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6410974393038607719981037 2404115397389477894992889)
                      ·
                        rfl

theorem cell23_4681998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_4681998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4681998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4681998 prefixEnd_4681998 := by exact prefixLift 4681998
  have htrace : WordTrace (prefixWord ++ tailWord_4681998) baseStart_4681998 baseEnd_4681998 := by
    simpa [prefixWord, tailWord_4681998, baseEnd_4681998] using wordTrace_append hprefix tailTrace_4681998
  have hstable : (prefixWord ++ tailWord_4681998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4681998).length < 2 ^ (prefixWord ++ tailWord_4681998).sum := by decide
  have hdescent : baseEnd_4681998 < baseStart_4681998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4681998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682001 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 9]
def baseStart_4682001 : Nat := 118140960795 + 4682001 * 2 ^ 59
def prefixEnd_4682001 : Nat := 4983230072969 + 3 ^ 40 * 4682001 * 2
def baseEnd_4682001 : Nat := 267124104203493487028375

theorem tailTrace_4682001 : CollatzResearch.WordTrace tailWord_4682001 prefixEnd_4682001 267124104203493487028375 := by
  unfold tailWord_4682001
  simp only [CollatzResearch.WordTrace]
  refine ⟨170766605510917473954741857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113844403673944982636494571 170766605510917473954741857)
  ·
    refine ⟨128074954133188105466056393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170766605510917473954741857 128074954133188105466056393)
    ·
      refine ⟨96056215599891079099542295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128074954133188105466056393 96056215599891079099542295)
      ·
        refine ⟨144084323399836618649313443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96056215599891079099542295 144084323399836618649313443)
        ·
          refine ⟨216126485099754927973970165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144084323399836618649313443 216126485099754927973970165)
          ·
            refine ⟨20261857978102024497559703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 216126485099754927973970165 20261857978102024497559703)
            ·
              refine ⟨30392786967153036746339555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20261857978102024497559703 30392786967153036746339555)
              ·
                refine ⟨45589180450729555119509333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30392786967153036746339555 45589180450729555119509333)
                ·
                  refine ⟨267124104203493487028375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45589180450729555119509333 267124104203493487028375)
                  ·
                    rfl

theorem cell23_4682001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 9].length) (baseStart_4682001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682001 prefixEnd_4682001 := by exact prefixLift 4682001
  have htrace : WordTrace (prefixWord ++ tailWord_4682001) baseStart_4682001 baseEnd_4682001 := by
    simpa [prefixWord, tailWord_4682001, baseEnd_4682001] using wordTrace_append hprefix tailTrace_4682001
  have hstable : (prefixWord ++ tailWord_4682001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682001).length < 2 ^ (prefixWord ++ tailWord_4682001).sum := by decide
  have hdescent : baseEnd_4682001 < baseStart_4682001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682023 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4682023 : Nat := 118140960795 + 4682023 * 2 ^ 59
def prefixEnd_4682023 : Nat := 4983230072969 + 3 ^ 40 * 4682023 * 2
def baseEnd_4682023 : Nat := 2404128234405840297180275

theorem tailTrace_4682023 : CollatzResearch.WordTrace tailWord_4682023 prefixEnd_4682023 2404128234405840297180275 := by
  unfold tailWord_4682023
  simp only [CollatzResearch.WordTrace]
  refine ⟨170767407916837771712042723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113844938611225181141361815 170767407916837771712042723)
  ·
    refine ⟨256151111875256657568064085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170767407916837771712042723 256151111875256657568064085)
    ·
      refine ⟨3001770842288163955875751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 256151111875256657568064085 3001770842288163955875751)
      ·
        refine ⟨4502656263432245933813627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001770842288163955875751 4502656263432245933813627)
        ·
          refine ⟨6753984395148368900720441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502656263432245933813627 6753984395148368900720441)
          ·
            refine ⟨5065488296361276675540331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6753984395148368900720441 5065488296361276675540331)
            ·
              refine ⟨7598232444541915013310497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065488296361276675540331 7598232444541915013310497)
              ·
                refine ⟨5698674333406436259982873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7598232444541915013310497 5698674333406436259982873)
                ·
                  refine ⟨4274005750054827194987155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698674333406436259982873 4274005750054827194987155)
                  ·
                    refine ⟨6411008625082240792480733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4274005750054827194987155 6411008625082240792480733)
                    ·
                      refine ⟨2404128234405840297180275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6411008625082240792480733 2404128234405840297180275)
                      ·
                        rfl

theorem cell23_4682023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4682023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682023 prefixEnd_4682023 := by exact prefixLift 4682023
  have htrace : WordTrace (prefixWord ++ tailWord_4682023) baseStart_4682023 baseEnd_4682023 := by
    simpa [prefixWord, tailWord_4682023, baseEnd_4682023] using wordTrace_append hprefix tailTrace_4682023
  have hstable : (prefixWord ++ tailWord_4682023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682023).length < 2 ^ (prefixWord ++ tailWord_4682023).sum := by decide
  have hdescent : baseEnd_4682023 < baseStart_4682023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682028 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_4682028 : Nat := 118140960795 + 4682028 * 2 ^ 59
def prefixEnd_4682028 : Nat := 4983230072969 + 3 ^ 40 * 4682028 * 2
def baseEnd_4682028 : Nat := 2404130801809112777617751

theorem tailTrace_4682028 : CollatzResearch.WordTrace tailWord_4682028 prefixEnd_4682028 2404130801809112777617751 := by
  unfold tailWord_4682028
  simp only [CollatzResearch.WordTrace]
  refine ⟨85383795140909828782987369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113845060187879771710649825 85383795140909828782987369)
  ·
    refine ⟨64037846355682371587240527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85383795140909828782987369 64037846355682371587240527)
    ·
      refine ⟨96056769533523557380860791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64037846355682371587240527 96056769533523557380860791)
      ·
        refine ⟨144085154300285336071291187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96056769533523557380860791 144085154300285336071291187)
        ·
          refine ⟨216127731450428004106936781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144085154300285336071291187 216127731450428004106936781)
          ·
            refine ⟨81047899293910501540101293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216127731450428004106936781 81047899293910501540101293)
            ·
              refine ⟨30392962235216438077537985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81047899293910501540101293 30392962235216438077537985)
              ·
                refine ⟨22794721676412328558153489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30392962235216438077537985 22794721676412328558153489)
                ·
                  refine ⟨17096041257309246418615117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22794721676412328558153489 17096041257309246418615117)
                  ·
                    refine ⟨6411015471490967406980669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17096041257309246418615117 6411015471490967406980669)
                    ·
                      refine ⟨2404130801809112777617751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6411015471490967406980669 2404130801809112777617751)
                      ·
                        rfl

theorem cell23_4682028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_4682028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682028 prefixEnd_4682028 := by exact prefixLift 4682028
  have htrace : WordTrace (prefixWord ++ tailWord_4682028) baseStart_4682028 baseEnd_4682028 := by
    simpa [prefixWord, tailWord_4682028, baseEnd_4682028] using wordTrace_append hprefix tailTrace_4682028
  have hstable : (prefixWord ++ tailWord_4682028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682028).length < 2 ^ (prefixWord ++ tailWord_4682028).sum := by decide
  have hdescent : baseEnd_4682028 < baseStart_4682028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682046 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_4682046 : Nat := 118140960795 + 4682046 * 2 ^ 59
def prefixEnd_4682046 : Nat := 4983230072969 + 3 ^ 40 * 4682046 * 2
def baseEnd_4682046 : Nat := 2404140044460893707192669

theorem tailTrace_4682046 : CollatzResearch.WordTrace tailWord_4682046 prefixEnd_4682046 2404140044460893707192669 := by
  unfold tailWord_4682046
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346030849469305830016249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113845497863836297760086661 21346030849469305830016249)
  ·
    refine ⟨16009523137101979372512187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21346030849469305830016249 16009523137101979372512187)
    ·
      refine ⟨24014284705652969058768281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16009523137101979372512187 24014284705652969058768281)
      ·
        refine ⟨18010713529239726794076211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24014284705652969058768281 18010713529239726794076211)
        ·
          refine ⟨27016070293859590191114317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18010713529239726794076211 27016070293859590191114317)
          ·
            refine ⟨10131026360197346321667869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27016070293859590191114317 10131026360197346321667869)
            ·
              refine ⟨3799134885074004870625451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10131026360197346321667869 3799134885074004870625451)
              ·
                refine ⟨5698702327611007305938177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799134885074004870625451 5698702327611007305938177)
                ·
                  refine ⟨4274026745708255479453633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698702327611007305938177 4274026745708255479453633)
                  ·
                    refine ⟨3205520059281191609590225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274026745708255479453633 3205520059281191609590225)
                    ·
                      refine ⟨2404140044460893707192669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205520059281191609590225 2404140044460893707192669)
                      ·
                        rfl

theorem cell23_4682046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_4682046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682046 prefixEnd_4682046 := by exact prefixLift 4682046
  have htrace : WordTrace (prefixWord ++ tailWord_4682046) baseStart_4682046 baseEnd_4682046 := by
    simpa [prefixWord, tailWord_4682046, baseEnd_4682046] using wordTrace_append hprefix tailTrace_4682046
  have hstable : (prefixWord ++ tailWord_4682046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682046).length < 2 ^ (prefixWord ++ tailWord_4682046).sum := by decide
  have hdescent : baseEnd_4682046 < baseStart_4682046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682069 : List Nat := [1, 3, 2, 2, 5, 1, 1, 3, 5]
def baseStart_4682069 : Nat := 118140960795 + 4682069 * 2 ^ 59
def prefixEnd_4682069 : Nat := 4983230072969 + 3 ^ 40 * 4682069 * 2
def baseEnd_4682069 : Nat := 267127983835105235245007

theorem tailTrace_4682069 : CollatzResearch.WordTrace tailWord_4682069 prefixEnd_4682069 267127983835105235245007 := by
  unfold tailWord_4682069
  simp only [CollatzResearch.WordTrace]
  refine ⟨170769085674671121568217261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113846057116447414378811507 170769085674671121568217261)
  ·
    refine ⟨64038407128001670588081473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170769085674671121568217261 64038407128001670588081473)
    ·
      refine ⟨48028805346001252941061105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64038407128001670588081473 48028805346001252941061105)
      ·
        refine ⟨36021604009500939705795829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48028805346001252941061105 36021604009500939705795829)
        ·
          refine ⟨3377025375890713097418359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36021604009500939705795829 3377025375890713097418359)
          ·
            refine ⟨5065538063836069646127539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377025375890713097418359 5065538063836069646127539)
            ·
              refine ⟨7598307095754104469191309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065538063836069646127539 7598307095754104469191309)
              ·
                refine ⟨2849365160907789175946741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7598307095754104469191309 2849365160907789175946741)
                ·
                  refine ⟨267127983835105235245007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2849365160907789175946741 267127983835105235245007)
                  ·
                    rfl

theorem cell23_4682069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_4682069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682069 prefixEnd_4682069 := by exact prefixLift 4682069
  have htrace : WordTrace (prefixWord ++ tailWord_4682069) baseStart_4682069 baseEnd_4682069 := by
    simpa [prefixWord, tailWord_4682069, baseEnd_4682069] using wordTrace_append hprefix tailTrace_4682069
  have hstable : (prefixWord ++ tailWord_4682069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682069).length < 2 ^ (prefixWord ++ tailWord_4682069).sum := by decide
  have hdescent : baseEnd_4682069 < baseStart_4682069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682085 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_4682085 : Nat := 118140960795 + 4682085 * 2 ^ 59
def prefixEnd_4682085 : Nat := 4983230072969 + 3 ^ 40 * 4682085 * 2
def baseEnd_4682085 : Nat := 2404160070206419054604989

theorem tailTrace_4682085 : CollatzResearch.WordTrace tailWord_4682085 prefixEnd_4682085 2404160070206419054604989 := by
  unfold tailWord_4682085
  simp only [CollatzResearch.WordTrace]
  refine ⟨170769669242613156300799709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113846446161742104200533139 170769669242613156300799709)
  ·
    refine ⟨64038625965979933612799891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170769669242613156300799709 64038625965979933612799891)
    ·
      refine ⟨96057938948969900419199837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64038625965979933612799891 96057938948969900419199837)
      ·
        refine ⟨36021727105863712657199939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96057938948969900419199837 36021727105863712657199939)
        ·
          refine ⟨54032590658795568985799909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36021727105863712657199939 54032590658795568985799909)
          ·
            refine ⟨10131110748524169184837483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54032590658795568985799909 10131110748524169184837483)
            ·
              refine ⟨15196666122786253777256225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10131110748524169184837483 15196666122786253777256225)
              ·
                refine ⟨11397499592089690332942169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15196666122786253777256225 11397499592089690332942169)
                ·
                  refine ⟨8548124694067267749706627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11397499592089690332942169 8548124694067267749706627)
                  ·
                    refine ⟨12822187041100901624559941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8548124694067267749706627 12822187041100901624559941)
                    ·
                      refine ⟨2404160070206419054604989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12822187041100901624559941 2404160070206419054604989)
                      ·
                        rfl

theorem cell23_4682085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_4682085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682085 prefixEnd_4682085 := by exact prefixLift 4682085
  have htrace : WordTrace (prefixWord ++ tailWord_4682085) baseStart_4682085 baseEnd_4682085 := by
    simpa [prefixWord, tailWord_4682085, baseEnd_4682085] using wordTrace_append hprefix tailTrace_4682085
  have hstable : (prefixWord ++ tailWord_4682085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682085).length < 2 ^ (prefixWord ++ tailWord_4682085).sum := by decide
  have hdescent : baseEnd_4682085 < baseStart_4682085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682142 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_4682142 : Nat := 118140960795 + 4682142 * 2 ^ 59
def prefixEnd_4682142 : Nat := 4983230072969 + 3 ^ 40 * 4682142 * 2
def baseEnd_4682142 : Nat := 267132148733747259065803

theorem tailTrace_4682142 : CollatzResearch.WordTrace tailWord_4682142 prefixEnd_4682142 267132148733747259065803 := by
  unfold tailWord_4682142
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346468525425831879453085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113847832135604436690416453 21346468525425831879453085)
  ·
    refine ⟨8004925697034686954794907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21346468525425831879453085 8004925697034686954794907)
    ·
      refine ⟨12007388545552030432192361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8004925697034686954794907 12007388545552030432192361)
      ·
        refine ⟨9005541409164022824144271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12007388545552030432192361 9005541409164022824144271)
        ·
          refine ⟨13508312113746034236216407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9005541409164022824144271 13508312113746034236216407)
          ·
            refine ⟨20262468170619051354324611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13508312113746034236216407 20262468170619051354324611)
            ·
              refine ⟨30393702255928577031486917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20262468170619051354324611 30393702255928577031486917)
              ·
                refine ⟨5698819172986608193403797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30393702255928577031486917 5698819172986608193403797)
                ·
                  refine ⟨267132148733747259065803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5698819172986608193403797 267132148733747259065803)
                  ·
                    rfl

theorem cell23_4682142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_4682142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682142 prefixEnd_4682142 := by exact prefixLift 4682142
  have htrace : WordTrace (prefixWord ++ tailWord_4682142) baseStart_4682142 baseEnd_4682142 := by
    simpa [prefixWord, tailWord_4682142, baseEnd_4682142] using wordTrace_append hprefix tailTrace_4682142
  have hstable : (prefixWord ++ tailWord_4682142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682142).length < 2 ^ (prefixWord ++ tailWord_4682142).sum := by decide
  have hdescent : baseEnd_4682142 < baseStart_4682142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682205 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4682205 : Nat := 118140960795 + 4682205 * 2 ^ 59
def prefixEnd_4682205 : Nat := 4983230072969 + 3 ^ 40 * 4682205 * 2
def baseEnd_4682205 : Nat := 2404221687884958585104437

theorem tailTrace_4682205 : CollatzResearch.WordTrace tailWord_4682205 prefixEnd_4682205 2404221687884958585104437 := by
  unfold tailWord_4682205
  simp only [CollatzResearch.WordTrace]
  refine ⟨170774046002178416795168069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113849364001452277863445379 170774046002178416795168069)
  ·
    refine ⟨32020133625408453149094013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170774046002178416795168069 32020133625408453149094013)
    ·
      refine ⟨12007550109528169930910255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32020133625408453149094013 12007550109528169930910255)
      ·
        refine ⟨18011325164292254896365383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12007550109528169930910255 18011325164292254896365383)
        ·
          refine ⟨27016987746438382344548075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18011325164292254896365383 27016987746438382344548075)
          ·
            refine ⟨40525481619657573516822113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27016987746438382344548075 40525481619657573516822113)
            ·
              refine ⟨30394111214743180137616585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40525481619657573516822113 30394111214743180137616585)
              ·
                refine ⟨22795583411057385103212439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30394111214743180137616585 22795583411057385103212439)
                ·
                  refine ⟨34193375116586077654818659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22795583411057385103212439 34193375116586077654818659)
                  ·
                    refine ⟨51290062674879116482227989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34193375116586077654818659 51290062674879116482227989)
                    ·
                      refine ⟨2404221687884958585104437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51290062674879116482227989 2404221687884958585104437)
                      ·
                        rfl

theorem cell23_4682205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4682205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682205 prefixEnd_4682205 := by exact prefixLift 4682205
  have htrace : WordTrace (prefixWord ++ tailWord_4682205) baseStart_4682205 baseEnd_4682205 := by
    simpa [prefixWord, tailWord_4682205, baseEnd_4682205] using wordTrace_append hprefix tailTrace_4682205
  have hstable : (prefixWord ++ tailWord_4682205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682205).length < 2 ^ (prefixWord ++ tailWord_4682205).sum := by decide
  have hdescent : baseEnd_4682205 < baseStart_4682205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682209 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_4682209 : Nat := 118140960795 + 4682209 * 2 ^ 59
def prefixEnd_4682209 : Nat := 4983230072969 + 3 ^ 40 * 4682209 * 2
def baseEnd_4682209 : Nat := 2404223741807576569454419

theorem tailTrace_4682209 : CollatzResearch.WordTrace tailWord_4682209 prefixEnd_4682209 2404223741807576569454419 := by
  unfold tailWord_4682209
  simp only [CollatzResearch.WordTrace]
  refine ⟨170774191894163925478313681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113849461262775950318875787 170774191894163925478313681)
  ·
    refine ⟨128080643920622944108735261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170774191894163925478313681 128080643920622944108735261)
    ·
      refine ⟨48030241470233604040775723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128080643920622944108735261 48030241470233604040775723)
      ·
        refine ⟨72045362205350406061163585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48030241470233604040775723 72045362205350406061163585)
        ·
          refine ⟨54034021654012804545872689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72045362205350406061163585 54034021654012804545872689)
          ·
            refine ⟨40525516240509603409404517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54034021654012804545872689 40525516240509603409404517)
            ·
              refine ⟨7598534295095550639263347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40525516240509603409404517 7598534295095550639263347)
              ·
                refine ⟨11397801442643325958895021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7598534295095550639263347 11397801442643325958895021)
                ·
                  refine ⟨4274175540991247234585633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11397801442643325958895021 4274175540991247234585633)
                  ·
                    refine ⟨3205631655743435425939225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274175540991247234585633 3205631655743435425939225)
                    ·
                      refine ⟨2404223741807576569454419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205631655743435425939225 2404223741807576569454419)
                      ·
                        rfl

theorem cell23_4682209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_4682209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682209 prefixEnd_4682209 := by exact prefixLift 4682209
  have htrace : WordTrace (prefixWord ++ tailWord_4682209) baseStart_4682209 baseEnd_4682209 := by
    simpa [prefixWord, tailWord_4682209, baseEnd_4682209] using wordTrace_append hprefix tailTrace_4682209
  have hstable : (prefixWord ++ tailWord_4682209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682209).length < 2 ^ (prefixWord ++ tailWord_4682209).sum := by decide
  have hdescent : baseEnd_4682209 < baseStart_4682209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682222 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_4682222 : Nat := 118140960795 + 4682222 * 2 ^ 59
def prefixEnd_4682222 : Nat := 4983230072969 + 3 ^ 40 * 4682222 * 2
def baseEnd_4682222 : Nat := 2404230417056085018591859

theorem tailTrace_4682222 : CollatzResearch.WordTrace tailWord_4682222 prefixEnd_4682222 2404230417056085018591859 := by
  unfold tailWord_4682222
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346833255389603587317115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113849777362077885799024613 21346833255389603587317115)
  ·
    refine ⟨32020249883084405380975673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21346833255389603587317115 32020249883084405380975673)
    ·
      refine ⟨24015187412313304035731755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32020249883084405380975673 24015187412313304035731755)
      ·
        refine ⟨36022781118469956053597633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24015187412313304035731755 36022781118469956053597633)
        ·
          refine ⟨27017085838852467040198225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36022781118469956053597633 27017085838852467040198225)
          ·
            refine ⟨20262814379139350280148669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27017085838852467040198225 20262814379139350280148669)
            ·
              refine ⟨7598555392177256355055751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20262814379139350280148669 7598555392177256355055751)
              ·
                refine ⟨11397833088265884532583627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7598555392177256355055751 11397833088265884532583627)
                ·
                  refine ⟨17096749632398826798875441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11397833088265884532583627 17096749632398826798875441)
                  ·
                    refine ⟨12822562224299120099156581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17096749632398826798875441 12822562224299120099156581)
                    ·
                      refine ⟨2404230417056085018591859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12822562224299120099156581 2404230417056085018591859)
                      ·
                        rfl

theorem cell23_4682222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_4682222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682222 prefixEnd_4682222 := by exact prefixLift 4682222
  have htrace : WordTrace (prefixWord ++ tailWord_4682222) baseStart_4682222 baseEnd_4682222 := by
    simpa [prefixWord, tailWord_4682222, baseEnd_4682222] using wordTrace_append hprefix tailTrace_4682222
  have hstable : (prefixWord ++ tailWord_4682222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682222).length < 2 ^ (prefixWord ++ tailWord_4682222).sum := by decide
  have hdescent : baseEnd_4682222 < baseStart_4682222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682246 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4682246 : Nat := 118140960795 + 4682246 * 2 ^ 59
def prefixEnd_4682246 : Nat := 4983230072969 + 3 ^ 40 * 4682246 * 2
def baseEnd_4682246 : Nat := 2404242740591792924691749

theorem tailTrace_4682246 : CollatzResearch.WordTrace tailWord_4682246 prefixEnd_4682246 2404242740591792924691749 := by
  unfold tailWord_4682246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336735668594683774919081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113850360930019920531607061 5336735668594683774919081)
  ·
    refine ⟨4002551751446012831189311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5336735668594683774919081 4002551751446012831189311)
    ·
      refine ⟨6003827627169019246783967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002551751446012831189311 6003827627169019246783967)
      ·
        refine ⟨9005741440753528870175951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6003827627169019246783967 9005741440753528870175951)
        ·
          refine ⟨13508612161130293305263927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9005741440753528870175951 13508612161130293305263927)
          ·
            refine ⟨20262918241695439957895891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13508612161130293305263927 20262918241695439957895891)
            ·
              refine ⟨30394377362543159936843837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20262918241695439957895891 30394377362543159936843837)
              ·
                refine ⟨11397891510953684976316439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30394377362543159936843837 11397891510953684976316439)
                ·
                  refine ⟨17096837266430527464474659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11397891510953684976316439 17096837266430527464474659)
                  ·
                    refine ⟨25645255899645791196711989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17096837266430527464474659 25645255899645791196711989)
                    ·
                      refine ⟨2404242740591792924691749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25645255899645791196711989 2404242740591792924691749)
                      ·
                        rfl

theorem cell23_4682246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4682246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682246 prefixEnd_4682246 := by exact prefixLift 4682246
  have htrace : WordTrace (prefixWord ++ tailWord_4682246) baseStart_4682246 baseEnd_4682246 := by
    simpa [prefixWord, tailWord_4682246, baseEnd_4682246] using wordTrace_append hprefix tailTrace_4682246
  have hstable : (prefixWord ++ tailWord_4682246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682246).length < 2 ^ (prefixWord ++ tailWord_4682246).sum := by decide
  have hdescent : baseEnd_4682246 < baseStart_4682246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682286 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_4682286 : Nat := 118140960795 + 4682286 * 2 ^ 59
def prefixEnd_4682286 : Nat := 4983230072969 + 3 ^ 40 * 4682286 * 2
def baseEnd_4682286 : Nat := 2404263279817972768191565

theorem tailTrace_4682286 : CollatzResearch.WordTrace tailWord_4682286 prefixEnd_4682286 2404263279817972768191565 := by
  unfold tailWord_4682286
  simp only [CollatzResearch.WordTrace]
  refine ⟨21347125039360620953608339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113851333543256645085911141 21347125039360620953608339)
  ·
    refine ⟨32020687559040931430412509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21347125039360620953608339 32020687559040931430412509)
    ·
      refine ⟨12007757834640349286404691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32020687559040931430412509 12007757834640349286404691)
      ·
        refine ⟨18011636751960523929607037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12007757834640349286404691 18011636751960523929607037)
        ·
          refine ⟨6754363781985196473602639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18011636751960523929607037 6754363781985196473602639)
          ·
            refine ⟨10131545672977794710403959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6754363781985196473602639 10131545672977794710403959)
            ·
              refine ⟨15197318509466692065605939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10131545672977794710403959 15197318509466692065605939)
              ·
                refine ⟨22795977764200038098408909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15197318509466692065605939 22795977764200038098408909)
                ·
                  refine ⟨8548491661575014286903341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22795977764200038098408909 8548491661575014286903341)
                  ·
                    refine ⟨3205684373090630357588753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8548491661575014286903341 3205684373090630357588753)
                    ·
                      refine ⟨2404263279817972768191565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205684373090630357588753 2404263279817972768191565)
                      ·
                        rfl

theorem cell23_4682286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_4682286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682286 prefixEnd_4682286 := by exact prefixLift 4682286
  have htrace : WordTrace (prefixWord ++ tailWord_4682286) baseStart_4682286 baseEnd_4682286 := by
    simpa [prefixWord, tailWord_4682286, baseEnd_4682286] using wordTrace_append hprefix tailTrace_4682286
  have hstable : (prefixWord ++ tailWord_4682286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682286).length < 2 ^ (prefixWord ++ tailWord_4682286).sum := by decide
  have hdescent : baseEnd_4682286 < baseStart_4682286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682316 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 2, 2, 2]
def baseStart_4682316 : Nat := 118140960795 + 4682316 * 2 ^ 59
def prefixEnd_4682316 : Nat := 4983230072969 + 3 ^ 40 * 4682316 * 2
def baseEnd_4682316 : Nat := 2404278684237607650816427

theorem tailTrace_4682316 : CollatzResearch.WordTrace tailWord_4682316 prefixEnd_4682316 2404278684237607650816427 := by
  unfold tailWord_4682316
  simp only [CollatzResearch.WordTrace]
  refine ⟨85389047252388141376229401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113852063003184188501639201 85389047252388141376229401)
  ·
    refine ⟨64041785439291106032172051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85389047252388141376229401 64041785439291106032172051)
    ·
      refine ⟨96062678158936659048258077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64041785439291106032172051 96062678158936659048258077)
      ·
        refine ⟨36023504309601247143096779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96062678158936659048258077 36023504309601247143096779)
        ·
          refine ⟨54035256464401870714645169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36023504309601247143096779 54035256464401870714645169)
          ·
            refine ⟨40526442348301403035983877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54035256464401870714645169 40526442348301403035983877)
            ·
              refine ⟨7598707940306513069246977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40526442348301403035983877 7598707940306513069246977)
              ·
                refine ⟨5699030955229884801935233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7598707940306513069246977 5699030955229884801935233)
                ·
                  refine ⟨4274273216422413601451425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5699030955229884801935233 4274273216422413601451425)
                  ·
                    refine ⟨3205704912316810201088569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274273216422413601451425 3205704912316810201088569)
                    ·
                      refine ⟨2404278684237607650816427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205704912316810201088569 2404278684237607650816427)
                      ·
                        rfl

theorem cell23_4682316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_4682316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682316 prefixEnd_4682316 := by exact prefixLift 4682316
  have htrace : WordTrace (prefixWord ++ tailWord_4682316) baseStart_4682316 baseEnd_4682316 := by
    simpa [prefixWord, tailWord_4682316, baseEnd_4682316] using wordTrace_append hprefix tailTrace_4682316
  have hstable : (prefixWord ++ tailWord_4682316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682316).length < 2 ^ (prefixWord ++ tailWord_4682316).sum := by decide
  have hdescent : baseEnd_4682316 < baseStart_4682316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682335 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 4, 5]
def baseStart_4682335 : Nat := 118140960795 + 4682335 * 2 ^ 59
def prefixEnd_4682335 : Nat := 4983230072969 + 3 ^ 40 * 4682335 * 2
def baseEnd_4682335 : Nat := 801429480123347692159613

theorem tailTrace_4682335 : CollatzResearch.WordTrace tailWord_4682335 prefixEnd_4682335 801429480123347692159613 := by
  unfold tailWord_4682335
  simp only [CollatzResearch.WordTrace]
  refine ⟨170778787491707448997400459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113852524994471632664933639 170778787491707448997400459)
  ·
    refine ⟨256168181237561173496100689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170778787491707448997400459 256168181237561173496100689)
    ·
      refine ⟨192126135928170880122075517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256168181237561173496100689 192126135928170880122075517)
      ·
        refine ⟨72047300973064080045778319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192126135928170880122075517 72047300973064080045778319)
        ·
          refine ⟨108070951459596120068667479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72047300973064080045778319 108070951459596120068667479)
          ·
            refine ⟨162106427189394180103001219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108070951459596120068667479 162106427189394180103001219)
            ·
              refine ⟨243159640784091270154501829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162106427189394180103001219 243159640784091270154501829)
              ·
                refine ⟨45592432647017113153969093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243159640784091270154501829 45592432647017113153969093)
                ·
                  refine ⟨8548581121315708716369205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45592432647017113153969093 8548581121315708716369205)
                  ·
                    refine ⟨801429480123347692159613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8548581121315708716369205 801429480123347692159613)
                    ·
                      rfl

theorem cell23_4682335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_4682335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682335 prefixEnd_4682335 := by exact prefixLift 4682335
  have htrace : WordTrace (prefixWord ++ tailWord_4682335) baseStart_4682335 baseEnd_4682335 := by
    simpa [prefixWord, tailWord_4682335, baseEnd_4682335] using wordTrace_append hprefix tailTrace_4682335
  have hstable : (prefixWord ++ tailWord_4682335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682335).length < 2 ^ (prefixWord ++ tailWord_4682335).sum := by decide
  have hdescent : baseEnd_4682335 < baseStart_4682335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682352 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 1, 7]
def baseStart_4682352 : Nat := 118140960795 + 4682352 * 2 ^ 59
def prefixEnd_4682352 : Nat := 4983230072969 + 3 ^ 40 * 4682352 * 2
def baseEnd_4682352 : Nat := 801432389847056503322087

theorem tailTrace_4682352 : CollatzResearch.WordTrace tailWord_4682352 prefixEnd_4682352 801432389847056503322087 := by
  unfold tailWord_4682352
  simp only [CollatzResearch.WordTrace]
  refine ⟨85389703766322930450384655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113852938355097240600512873 85389703766322930450384655)
  ·
    refine ⟨128084555649484395675576983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85389703766322930450384655 128084555649484395675576983)
    ·
      refine ⟨192126833474226593513365475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128084555649484395675576983 192126833474226593513365475)
      ·
        refine ⟨288190250211339890270048213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192126833474226593513365475 288190250211339890270048213)
        ·
          refine ⟨6754458989328278678204255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 288190250211339890270048213 6754458989328278678204255)
          ·
            refine ⟨10131688483992418017306383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6754458989328278678204255 10131688483992418017306383)
            ·
              refine ⟨15197532725988627025959575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10131688483992418017306383 15197532725988627025959575)
              ·
                refine ⟨22796299088982940538939363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15197532725988627025959575 22796299088982940538939363)
                ·
                  refine ⟨34194448633474410808409045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22796299088982940538939363 34194448633474410808409045)
                  ·
                    refine ⟨801432389847056503322087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34194448633474410808409045 801432389847056503322087)
                    ·
                      rfl

theorem cell23_4682352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_4682352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682352 prefixEnd_4682352 := by exact prefixLift 4682352
  have htrace : WordTrace (prefixWord ++ tailWord_4682352) baseStart_4682352 baseEnd_4682352 := by
    simpa [prefixWord, tailWord_4682352, baseEnd_4682352] using wordTrace_append hprefix tailTrace_4682352
  have hstable : (prefixWord ++ tailWord_4682352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682352).length < 2 ^ (prefixWord ++ tailWord_4682352).sum := by decide
  have hdescent : baseEnd_4682352 < baseStart_4682352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682392 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_4682392 : Nat := 118140960795 + 4682392 * 2 ^ 59
def prefixEnd_4682392 : Nat := 4983230072969 + 3 ^ 40 * 4682392 * 2
def baseEnd_4682392 : Nat := 2404317708767349353466077

theorem tailTrace_4682392 : CollatzResearch.WordTrace tailWord_4682392 prefixEnd_4682392 2404317708767349353466077 := by
  unfold tailWord_4682392
  simp only [CollatzResearch.WordTrace]
  refine ⟨85390433226250473866112715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113853910968333965154816953 85390433226250473866112715)
  ·
    refine ⟨128085649839375710799169073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85390433226250473866112715 128085649839375710799169073)
    ·
      refine ⟨96064237379531783099376805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128085649839375710799169073 96064237379531783099376805)
      ·
        refine ⟨18012044508662209331133151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96064237379531783099376805 18012044508662209331133151)
        ·
          refine ⟨27018066762993313996699727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18012044508662209331133151 27018066762993313996699727)
          ·
            refine ⟨40527100144489970995049591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27018066762993313996699727 40527100144489970995049591)
            ·
              refine ⟨60790650216734956492574387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40527100144489970995049591 60790650216734956492574387)
              ·
                refine ⟨91185975325102434738861581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60790650216734956492574387 91185975325102434738861581)
                ·
                  refine ⟨34194740746913413027073093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91185975325102434738861581 34194740746913413027073093)
                  ·
                    refine ⟨6411513890046264942576205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34194740746913413027073093 6411513890046264942576205)
                    ·
                      refine ⟨2404317708767349353466077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6411513890046264942576205 2404317708767349353466077)
                      ·
                        rfl

theorem cell23_4682392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_4682392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682392 prefixEnd_4682392 := by exact prefixLift 4682392
  have htrace : WordTrace (prefixWord ++ tailWord_4682392) baseStart_4682392 baseEnd_4682392 := by
    simpa [prefixWord, tailWord_4682392, baseEnd_4682392] using wordTrace_append hprefix tailTrace_4682392
  have hstable : (prefixWord ++ tailWord_4682392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682392).length < 2 ^ (prefixWord ++ tailWord_4682392).sum := by decide
  have hdescent : baseEnd_4682392 < baseStart_4682392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682439 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_4682439 : Nat := 118140960795 + 4682439 * 2 ^ 59
def prefixEnd_4682439 : Nat := 4983230072969 + 3 ^ 40 * 4682439 * 2
def baseEnd_4682439 : Nat := 2404341842358110669578361

theorem tailTrace_4682439 : CollatzResearch.WordTrace tailWord_4682439 prefixEnd_4682439 2404341842358110669578361 := by
  unfold tailWord_4682439
  simp only [CollatzResearch.WordTrace]
  refine ⟨170782580683330674759186371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113855053788887116506124247 170782580683330674759186371)
  ·
    refine ⟨256173871024996012138779557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170782580683330674759186371 256173871024996012138779557)
    ·
      refine ⟨48032600817186752276021167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256173871024996012138779557 48032600817186752276021167)
      ·
        refine ⟨72048901225780128414031751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48032600817186752276021167 72048901225780128414031751)
        ·
          refine ⟨108073351838670192621047627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72048901225780128414031751 108073351838670192621047627)
          ·
            refine ⟨162110027758005288931571441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108073351838670192621047627 162110027758005288931571441)
            ·
              refine ⟨121582520818503966698678581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162110027758005288931571441 121582520818503966698678581)
              ·
                refine ⟨11398361326734746878001117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121582520818503966698678581 11398361326734746878001117)
                ·
                  refine ⟨4274385497525530079250419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11398361326734746878001117 4274385497525530079250419)
                  ·
                    refine ⟨6411578246288295118875629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4274385497525530079250419 6411578246288295118875629)
                    ·
                      refine ⟨2404341842358110669578361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6411578246288295118875629 2404341842358110669578361)
                      ·
                        rfl

theorem cell23_4682439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_4682439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682439 prefixEnd_4682439 := by exact prefixLift 4682439
  have htrace : WordTrace (prefixWord ++ tailWord_4682439) baseStart_4682439 baseEnd_4682439 := by
    simpa [prefixWord, tailWord_4682439, baseEnd_4682439] using wordTrace_append hprefix tailTrace_4682439
  have hstable : (prefixWord ++ tailWord_4682439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682439).length < 2 ^ (prefixWord ++ tailWord_4682439).sum := by decide
  have hdescent : baseEnd_4682439 < baseStart_4682439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682446 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_4682446 : Nat := 118140960795 + 4682446 * 2 ^ 59
def prefixEnd_4682446 : Nat := 4983230072969 + 3 ^ 40 * 4682446 * 2
def baseEnd_4682446 : Nat := 267149492969188015798981

theorem tailTrace_4682446 : CollatzResearch.WordTrace tailWord_4682446 prefixEnd_4682446 267149492969188015798981 := by
  unfold tailWord_4682446
  simp only [CollatzResearch.WordTrace]
  refine ⟨21347854499288164369336399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113855223996203543303127461 21347854499288164369336399)
  ·
    refine ⟨32021781748932246554004599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21347854499288164369336399 32021781748932246554004599)
    ·
      refine ⟨48032672623398369831006899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32021781748932246554004599 48032672623398369831006899)
      ·
        refine ⟨72049008935097554746510349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48032672623398369831006899 72049008935097554746510349)
        ·
          refine ⟨27018378350661583029941381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72049008935097554746510349 27018378350661583029941381)
          ·
            refine ⟨5065945940749046818114009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27018378350661583029941381 5065945940749046818114009)
            ·
              refine ⟨3799459455561785113585507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5065945940749046818114009 3799459455561785113585507)
              ·
                refine ⟨5699189183342677670378261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799459455561785113585507 5699189183342677670378261)
                ·
                  refine ⟨267149492969188015798981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5699189183342677670378261 267149492969188015798981)
                  ·
                    rfl

theorem cell23_4682446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_4682446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682446 prefixEnd_4682446 := by exact prefixLift 4682446
  have htrace : WordTrace (prefixWord ++ tailWord_4682446) baseStart_4682446 baseEnd_4682446 := by
    simpa [prefixWord, tailWord_4682446, baseEnd_4682446] using wordTrace_append hprefix tailTrace_4682446
  have hstable : (prefixWord ++ tailWord_4682446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682446).length < 2 ^ (prefixWord ++ tailWord_4682446).sum := by decide
  have hdescent : baseEnd_4682446 < baseStart_4682446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682449 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 4, 3, 2]
def baseStart_4682449 : Nat := 118140960795 + 4682449 * 2 ^ 59
def prefixEnd_4682449 : Nat := 4983230072969 + 3 ^ 40 * 4682449 * 2
def baseEnd_4682449 : Nat := 2404346977164655630453315

theorem tailTrace_4682449 : CollatzResearch.WordTrace tailWord_4682449 prefixEnd_4682449 2404346977164655630453315 := by
  unfold tailWord_4682449
  simp only [CollatzResearch.WordTrace]
  refine ⟨170782945413294446467050401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113855296942196297644700267 170782945413294446467050401)
  ·
    refine ⟨128087209059970834850287801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170782945413294446467050401 128087209059970834850287801)
    ·
      refine ⟨96065406794978126137715851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128087209059970834850287801 96065406794978126137715851)
      ·
        refine ⟨144098110192467189206573777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96065406794978126137715851 144098110192467189206573777)
        ·
          refine ⟨108073582644350391904930333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144098110192467189206573777 108073582644350391904930333)
          ·
            refine ⟨40527593491631396964348875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108073582644350391904930333 40527593491631396964348875)
            ·
              refine ⟨60791390237447095446523313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40527593491631396964348875 60791390237447095446523313)
              ·
                refine ⟨45593542678085321584892485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60791390237447095446523313 45593542678085321584892485)
                ·
                  refine ⟨8548789252140997797167341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45593542678085321584892485 8548789252140997797167341)
                  ·
                    refine ⟨3205795969552874173937753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8548789252140997797167341 3205795969552874173937753)
                    ·
                      refine ⟨2404346977164655630453315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205795969552874173937753 2404346977164655630453315)
                      ·
                        rfl

theorem cell23_4682449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_4682449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682449 prefixEnd_4682449 := by exact prefixLift 4682449
  have htrace : WordTrace (prefixWord ++ tailWord_4682449) baseStart_4682449 baseEnd_4682449 := by
    simpa [prefixWord, tailWord_4682449, baseEnd_4682449] using wordTrace_append hprefix tailTrace_4682449
  have hstable : (prefixWord ++ tailWord_4682449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682449).length < 2 ^ (prefixWord ++ tailWord_4682449).sum := by decide
  have hdescent : baseEnd_4682449 < baseStart_4682449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682484 : List Nat := [2, 6, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4682484 : Nat := 118140960795 + 4682484 * 2 ^ 59
def prefixEnd_4682484 : Nat := 4983230072969 + 3 ^ 40 * 4682484 * 2
def baseEnd_4682484 : Nat := 801454982995854331171885

theorem tailTrace_4682484 : CollatzResearch.WordTrace tailWord_4682484 prefixEnd_4682484 801454982995854331171885 := by
  unfold tailWord_4682484
  simp only [CollatzResearch.WordTrace]
  refine ⟨85392110984083823722287253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113856147978778431629716337 85392110984083823722287253)
  ·
    refine ⟨4002755202378929236982215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85392110984083823722287253 4002755202378929236982215)
    ·
      refine ⟨6004132803568393855473323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002755202378929236982215 6004132803568393855473323)
      ·
        refine ⟨9006199205352590783209985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004132803568393855473323 9006199205352590783209985)
        ·
          refine ⟨6754649404014443087407489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9006199205352590783209985 6754649404014443087407489)
          ·
            refine ⟨5065987053010832315555617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6754649404014443087407489 5065987053010832315555617)
            ·
              refine ⟨3799490289758124236666713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5065987053010832315555617 3799490289758124236666713)
              ·
                refine ⟨2849617717318593177500035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799490289758124236666713 2849617717318593177500035)
                ·
                  refine ⟨4274426575977889766250053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849617717318593177500035 4274426575977889766250053)
                  ·
                    refine ⟨801454982995854331171885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4274426575977889766250053 801454982995854331171885)
                    ·
                      rfl

theorem cell23_4682484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4682484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682484 prefixEnd_4682484 := by exact prefixLift 4682484
  have htrace : WordTrace (prefixWord ++ tailWord_4682484) baseStart_4682484 baseEnd_4682484 := by
    simpa [prefixWord, tailWord_4682484, baseEnd_4682484] using wordTrace_append hprefix tailTrace_4682484
  have hstable : (prefixWord ++ tailWord_4682484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682484).length < 2 ^ (prefixWord ++ tailWord_4682484).sum := by decide
  have hdescent : baseEnd_4682484 < baseStart_4682484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682529 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_4682529 : Nat := 118140960795 + 4682529 * 2 ^ 59
def prefixEnd_4682529 : Nat := 4983230072969 + 3 ^ 40 * 4682529 * 2
def baseEnd_4682529 : Nat := 2404388055617015317452947

theorem tailTrace_4682529 : CollatzResearch.WordTrace tailWord_4682529 prefixEnd_4682529 2404388055617015317452947 := by
  unfold tailWord_4682529
  simp only [CollatzResearch.WordTrace]
  refine ⟨170785863253004620129962641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113857242168669746753308427 170785863253004620129962641)
  ·
    refine ⟨128089397439753465097471981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170785863253004620129962641 128089397439753465097471981)
    ·
      refine ⟨48033524039907549411551993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128089397439753465097471981 48033524039907549411551993)
      ·
        refine ⟨36025143029930662058663995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48033524039907549411551993 36025143029930662058663995)
        ·
          refine ⟨54037714544895993087995993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36025143029930662058663995 54037714544895993087995993)
          ·
            refine ⟨40528285908671994815996995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54037714544895993087995993 40528285908671994815996995)
            ·
              refine ⟨60792428863007992223995493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40528285908671994815996995 60792428863007992223995493)
              ·
                refine ⟨11398580411813998541999155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60792428863007992223995493 11398580411813998541999155)
                ·
                  refine ⟨17097870617720997812998733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11398580411813998541999155 17097870617720997812998733)
                  ·
                    refine ⟨6411701481645374179874525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17097870617720997812998733 6411701481645374179874525)
                    ·
                      refine ⟨2404388055617015317452947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6411701481645374179874525 2404388055617015317452947)
                      ·
                        rfl

theorem cell23_4682529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_4682529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682529 prefixEnd_4682529 := by exact prefixLift 4682529
  have htrace : WordTrace (prefixWord ++ tailWord_4682529) baseStart_4682529 baseEnd_4682529 := by
    simpa [prefixWord, tailWord_4682529, baseEnd_4682529] using wordTrace_append hprefix tailTrace_4682529
  have hstable : (prefixWord ++ tailWord_4682529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682529).length < 2 ^ (prefixWord ++ tailWord_4682529).sum := by decide
  have hdescent : baseEnd_4682529 < baseStart_4682529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682530 : List Nat := [3, 3, 1, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_4682530 : Nat := 118140960795 + 4682530 * 2 ^ 59
def prefixEnd_4682530 : Nat := 4983230072969 + 3 ^ 40 * 4682530 * 2
def baseEnd_4682530 : Nat := 2404388569097669813540443

theorem tailTrace_4682530 : CollatzResearch.WordTrace tailWord_4682530 prefixEnd_4682530 2404388569097669813540443 := by
  unfold tailWord_4682530
  simp only [CollatzResearch.WordTrace]
  refine ⟨42696474931500249325187261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113857266484000664867166029 42696474931500249325187261)
  ·
    refine ⟨16011178099312593496945223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42696474931500249325187261 16011178099312593496945223)
    ·
      refine ⟨24016767148968890245417835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16011178099312593496945223 24016767148968890245417835)
      ·
        refine ⟨36025150723453335368126753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24016767148968890245417835 36025150723453335368126753)
        ·
          refine ⟨27018863042590001526095065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36025150723453335368126753 27018863042590001526095065)
          ·
            refine ⟨20264147281942501144571299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27018863042590001526095065 20264147281942501144571299)
            ·
              refine ⟨30396220922913751716856949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20264147281942501144571299 30396220922913751716856949)
              ·
                refine ⟨2849645711523164223455339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30396220922913751716856949 2849645711523164223455339)
                ·
                  refine ⟨4274468567284746335183009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849645711523164223455339 4274468567284746335183009)
                  ·
                    refine ⟨3205851425463559751387257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274468567284746335183009 3205851425463559751387257)
                    ·
                      refine ⟨2404388569097669813540443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205851425463559751387257 2404388569097669813540443)
                      ·
                        rfl

theorem cell23_4682530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_4682530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682530 prefixEnd_4682530 := by exact prefixLift 4682530
  have htrace : WordTrace (prefixWord ++ tailWord_4682530) baseStart_4682530 baseEnd_4682530 := by
    simpa [prefixWord, tailWord_4682530, baseEnd_4682530] using wordTrace_append hprefix tailTrace_4682530
  have hstable : (prefixWord ++ tailWord_4682530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682530).length < 2 ^ (prefixWord ++ tailWord_4682530).sum := by decide
  have hdescent : baseEnd_4682530 < baseStart_4682530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682546 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_4682546 : Nat := 118140960795 + 4682546 * 2 ^ 59
def prefixEnd_4682546 : Nat := 4983230072969 + 3 ^ 40 * 4682546 * 2
def baseEnd_4682546 : Nat := 2404396784788141750940369

theorem tailTrace_4682546 : CollatzResearch.WordTrace tailWord_4682546 prefixEnd_4682546 2404396784788141750940369 := by
  unfold tailWord_4682546
  simp only [CollatzResearch.WordTrace]
  refine ⟨42696620823485758008332873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113857655529295354688887661 42696620823485758008332873)
  ·
    refine ⟨32022465617614318506249655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42696620823485758008332873 32022465617614318506249655)
    ·
      refine ⟨48033698426421477759374483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32022465617614318506249655 48033698426421477759374483)
      ·
        refine ⟨72050547639632216639061725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48033698426421477759374483 72050547639632216639061725)
        ·
          refine ⟨27018955364862081239648147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72050547639632216639061725 27018955364862081239648147)
          ·
            refine ⟨40528433047293121859472221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27018955364862081239648147 40528433047293121859472221)
            ·
              refine ⟨15198162392734920697302083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40528433047293121859472221 15198162392734920697302083)
              ·
                refine ⟨22797243589102381045953125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15198162392734920697302083 22797243589102381045953125)
                ·
                  refine ⟨4274483172956696446116211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22797243589102381045953125 4274483172956696446116211)
                  ·
                    refine ⟨6411724759435044669174317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4274483172956696446116211 6411724759435044669174317)
                    ·
                      refine ⟨2404396784788141750940369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6411724759435044669174317 2404396784788141750940369)
                      ·
                        rfl

theorem cell23_4682546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_4682546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682546 prefixEnd_4682546 := by exact prefixLift 4682546
  have htrace : WordTrace (prefixWord ++ tailWord_4682546) baseStart_4682546 baseEnd_4682546 := by
    simpa [prefixWord, tailWord_4682546, baseEnd_4682546] using wordTrace_append hprefix tailTrace_4682546
  have hstable : (prefixWord ++ tailWord_4682546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682546).length < 2 ^ (prefixWord ++ tailWord_4682546).sum := by decide
  have hdescent : baseEnd_4682546 < baseStart_4682546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682563 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 2, 1, 3]
def baseStart_4682563 : Nat := 118140960795 + 4682563 * 2 ^ 59
def prefixEnd_4682563 : Nat := 4983230072969 + 3 ^ 40 * 4682563 * 2
def baseEnd_4682563 : Nat := 2404405513959268184427791

theorem tailTrace_4682563 : CollatzResearch.WordTrace tailWord_4682563 prefixEnd_4682563 2404405513959268184427791 := by
  unfold tailWord_4682563
  simp only [CollatzResearch.WordTrace]
  refine ⟨170787103334881443936700343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113858068889920962624466895 170787103334881443936700343)
  ·
    refine ⟨256180655002322165905050515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170787103334881443936700343 256180655002322165905050515)
    ·
      refine ⟨384270982503483248857575773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256180655002322165905050515 384270982503483248857575773)
      ·
        refine ⟨144101618438806218321590915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384270982503483248857575773 144101618438806218321590915)
        ·
          refine ⟨216152427658209327482386373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144101618438806218321590915 216152427658209327482386373)
          ·
            refine ⟨40528580185914248902947445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216152427658209327482386373 40528580185914248902947445)
            ·
              refine ⟨3799554392429460834651323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40528580185914248902947445 3799554392429460834651323)
              ·
                refine ⟨5699331588644191251976985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799554392429460834651323 5699331588644191251976985)
                ·
                  refine ⟨4274498691483143438982739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5699331588644191251976985 4274498691483143438982739)
                  ·
                    refine ⟨6411748037224715158474109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4274498691483143438982739 6411748037224715158474109)
                    ·
                      refine ⟨2404405513959268184427791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6411748037224715158474109 2404405513959268184427791)
                      ·
                        rfl

theorem cell23_4682563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_4682563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682563 prefixEnd_4682563 := by exact prefixLift 4682563
  have htrace : WordTrace (prefixWord ++ tailWord_4682563) baseStart_4682563 baseEnd_4682563 := by
    simpa [prefixWord, tailWord_4682563, baseEnd_4682563] using wordTrace_append hprefix tailTrace_4682563
  have hstable : (prefixWord ++ tailWord_4682563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682563).length < 2 ^ (prefixWord ++ tailWord_4682563).sum := by decide
  have hdescent : baseEnd_4682563 < baseStart_4682563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682609 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 7]
def baseStart_4682609 : Nat := 118140960795 + 4682609 * 2 ^ 59
def prefixEnd_4682609 : Nat := 4983230072969 + 3 ^ 40 * 4682609 * 2
def baseEnd_4682609 : Nat := 267158792674375000494731

theorem tailTrace_4682609 : CollatzResearch.WordTrace tailWord_4682609 prefixEnd_4682609 267158792674375000494731 := by
  unfold tailWord_4682609
  simp only [CollatzResearch.WordTrace]
  refine ⟨170788781092714793792874881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113859187395143195861916587 170788781092714793792874881)
  ·
    refine ⟨128091585819536095344656161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170788781092714793792874881 128091585819536095344656161)
    ·
      refine ⟨96068689364652071508492121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128091585819536095344656161 96068689364652071508492121)
      ·
        refine ⟨72051517023489053631369091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96068689364652071508492121 72051517023489053631369091)
        ·
          refine ⟨108077275535233580447053637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72051517023489053631369091 108077275535233580447053637)
          ·
            refine ⟨20264489162856296333822557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108077275535233580447053637 20264489162856296333822557)
            ·
              refine ⟨7599183436071111125183459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20264489162856296333822557 7599183436071111125183459)
              ·
                refine ⟨11398775154106666687775189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7599183436071111125183459 11398775154106666687775189)
                ·
                  refine ⟨267158792674375000494731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11398775154106666687775189 267158792674375000494731)
                  ·
                    rfl

theorem cell23_4682609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 7].length) (baseStart_4682609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682609 prefixEnd_4682609 := by exact prefixLift 4682609
  have htrace : WordTrace (prefixWord ++ tailWord_4682609) baseStart_4682609 baseEnd_4682609 := by
    simpa [prefixWord, tailWord_4682609, baseEnd_4682609] using wordTrace_append hprefix tailTrace_4682609
  have hstable : (prefixWord ++ tailWord_4682609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682609).length < 2 ^ (prefixWord ++ tailWord_4682609).sum := by decide
  have hdescent : baseEnd_4682609 < baseStart_4682609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682619 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 3]
def baseStart_4682619 : Nat := 118140960795 + 4682619 * 2 ^ 59
def prefixEnd_4682619 : Nat := 4983230072969 + 3 ^ 40 * 4682619 * 2
def baseEnd_4682619 : Nat := 2404434268875919965327533

theorem tailTrace_4682619 : CollatzResearch.WordTrace tailWord_4682619 prefixEnd_4682619 2404434268875919965327533 := by
  unfold tailWord_4682619
  simp only [CollatzResearch.WordTrace]
  refine ⟨170789145822678565500738911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113859430548452377000492607 170789145822678565500738911)
  ·
    refine ⟨256183718734017848251108367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170789145822678565500738911 256183718734017848251108367)
    ·
      refine ⟨384275578101026772376662551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256183718734017848251108367 384275578101026772376662551)
      ·
        refine ⟨576413367151540158564993827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384275578101026772376662551 576413367151540158564993827)
        ·
          refine ⟨864620050727310237847490741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576413367151540158564993827 864620050727310237847490741)
          ·
            refine ⟨81058129755685334798202257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 864620050727310237847490741 81058129755685334798202257)
            ·
              refine ⟨60793597316764001098651693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81058129755685334798202257 60793597316764001098651693)
              ·
                refine ⟨22797598993786500411994385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60793597316764001098651693 22797598993786500411994385)
                ·
                  refine ⟨17098199245339875308995789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22797598993786500411994385 17098199245339875308995789)
                  ·
                    refine ⟨6411824717002453240873421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17098199245339875308995789 6411824717002453240873421)
                    ·
                      refine ⟨2404434268875919965327533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6411824717002453240873421 2404434268875919965327533)
                      ·
                        rfl

theorem cell23_4682619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 3].length) (baseStart_4682619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682619 prefixEnd_4682619 := by exact prefixLift 4682619
  have htrace : WordTrace (prefixWord ++ tailWord_4682619) baseStart_4682619 baseEnd_4682619 := by
    simpa [prefixWord, tailWord_4682619, baseEnd_4682619] using wordTrace_append hprefix tailTrace_4682619
  have hstable : (prefixWord ++ tailWord_4682619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682619).length < 2 ^ (prefixWord ++ tailWord_4682619).sum := by decide
  have hdescent : baseEnd_4682619 < baseStart_4682619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682703 : List Nat := [1, 1, 2, 1, 1, 6, 1, 5, 1, 4]
def baseStart_4682703 : Nat := 118140960795 + 4682703 * 2 ^ 59
def prefixEnd_4682703 : Nat := 4983230072969 + 3 ^ 40 * 4682703 * 2
def baseEnd_4682703 : Nat := 801492467083632545559049

theorem tailTrace_4682703 : CollatzResearch.WordTrace tailWord_4682703 prefixEnd_4682703 801492467083632545559049 := by
  unfold tailWord_4682703
  simp only [CollatzResearch.WordTrace]
  refine ⟨170792209554374247846796763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113861473036249498564531175 170792209554374247846796763)
  ·
    refine ⟨256188314331561371770195145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170792209554374247846796763 256188314331561371770195145)
    ·
      refine ⟨192141235748671028827646359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256188314331561371770195145 192141235748671028827646359)
      ·
        refine ⟨288211853623006543241469539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192141235748671028827646359 288211853623006543241469539)
        ·
          refine ⟨432317780434509814862204309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288211853623006543241469539 432317780434509814862204309)
          ·
            refine ⟨20264895957867647571665827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 432317780434509814862204309 20264895957867647571665827)
            ·
              refine ⟨30397343936801471357498741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20264895957867647571665827 30397343936801471357498741)
              ·
                refine ⟨2849750994075137939765507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30397343936801471357498741 2849750994075137939765507)
                ·
                  refine ⟨4274626491112706909648261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849750994075137939765507 4274626491112706909648261)
                  ·
                    refine ⟨801492467083632545559049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4274626491112706909648261 801492467083632545559049)
                    ·
                      rfl

theorem cell23_4682703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 4].length) (baseStart_4682703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682703 prefixEnd_4682703 := by exact prefixLift 4682703
  have htrace : WordTrace (prefixWord ++ tailWord_4682703) baseStart_4682703 baseEnd_4682703 := by
    simpa [prefixWord, tailWord_4682703, baseEnd_4682703] using wordTrace_append hprefix tailTrace_4682703
  have hstable : (prefixWord ++ tailWord_4682703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682703).length < 2 ^ (prefixWord ++ tailWord_4682703).sum := by decide
  have hdescent : baseEnd_4682703 < baseStart_4682703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682706 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4682706 : Nat := 118140960795 + 4682706 * 2 ^ 59
def prefixEnd_4682706 : Nat := 4983230072969 + 3 ^ 40 * 4682706 * 2
def baseEnd_4682706 : Nat := 2404478941692861124939633

theorem tailTrace_4682706 : CollatzResearch.WordTrace tailWord_4682706 prefixEnd_4682706 2404478941692861124939633 := by
  unfold tailWord_4682706
  simp only [CollatzResearch.WordTrace]
  refine ⟨42698079743340844839788993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113861545982242252906103981 42698079743340844839788993)
  ·
    refine ⟨32023559807505633629841745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42698079743340844839788993 32023559807505633629841745)
    ·
      refine ⟨24017669855629225222381309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32023559807505633629841745 24017669855629225222381309)
      ·
        refine ⟨9006626195860959458392991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24017669855629225222381309 9006626195860959458392991)
        ·
          refine ⟨13509939293791439187589487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006626195860959458392991 13509939293791439187589487)
          ·
            refine ⟨20264908940687158781384231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13509939293791439187589487 20264908940687158781384231)
            ·
              refine ⟨30397363411030738172076347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20264908940687158781384231 30397363411030738172076347)
              ·
                refine ⟨45596045116546107258114521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30397363411030738172076347 45596045116546107258114521)
                ·
                  refine ⟨34197033837409580443585891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45596045116546107258114521 34197033837409580443585891)
                  ·
                    refine ⟨51295550756114370665378837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34197033837409580443585891 51295550756114370665378837)
                    ·
                      refine ⟨2404478941692861124939633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51295550756114370665378837 2404478941692861124939633)
                      ·
                        rfl

theorem cell23_4682706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4682706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682706 prefixEnd_4682706 := by exact prefixLift 4682706
  have htrace : WordTrace (prefixWord ++ tailWord_4682706) baseStart_4682706 baseEnd_4682706 := by
    simpa [prefixWord, tailWord_4682706, baseEnd_4682706] using wordTrace_append hprefix tailTrace_4682706
  have hstable : (prefixWord ++ tailWord_4682706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682706).length < 2 ^ (prefixWord ++ tailWord_4682706).sum := by decide
  have hdescent : baseEnd_4682706 < baseStart_4682706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682710 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_4682710 : Nat := 118140960795 + 4682710 * 2 ^ 59
def prefixEnd_4682710 : Nat := 4983230072969 + 3 ^ 40 * 4682710 * 2
def baseEnd_4682710 : Nat := 2404480995615479109289615

theorem tailTrace_4682710 : CollatzResearch.WordTrace tailWord_4682710 prefixEnd_4682710 2404480995615479109289615 := by
  unfold tailWord_4682710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674529054084305502643849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113861643243565925361534389 10674529054084305502643849)
  ·
    refine ⟨8005896790563229126982887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10674529054084305502643849 8005896790563229126982887)
    ·
      refine ⟨12008845185844843690474331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8005896790563229126982887 12008845185844843690474331)
      ·
        refine ⟨18013267778767265535711497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12008845185844843690474331 18013267778767265535711497)
        ·
          refine ⟨13509950834075449151783623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18013267778767265535711497 13509950834075449151783623)
          ·
            refine ⟨20264926251113173727675435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13509950834075449151783623 20264926251113173727675435)
            ·
              refine ⟨30397389376669760591513153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20264926251113173727675435 30397389376669760591513153)
              ·
                refine ⟨22798042032502320443634865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30397389376669760591513153 22798042032502320443634865)
                ·
                  refine ⟨17098531524376740332726149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22798042032502320443634865 17098531524376740332726149)
                  ·
                    refine ⟨3205974660820638812386153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17098531524376740332726149 3205974660820638812386153)
                    ·
                      refine ⟨2404480995615479109289615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3205974660820638812386153 2404480995615479109289615)
                      ·
                        rfl

theorem cell23_4682710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_4682710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682710 prefixEnd_4682710 := by exact prefixLift 4682710
  have htrace : WordTrace (prefixWord ++ tailWord_4682710) baseStart_4682710 baseEnd_4682710 := by
    simpa [prefixWord, tailWord_4682710, baseEnd_4682710] using wordTrace_append hprefix tailTrace_4682710
  have hstable : (prefixWord ++ tailWord_4682710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682710).length < 2 ^ (prefixWord ++ tailWord_4682710).sum := by decide
  have hdescent : baseEnd_4682710 < baseStart_4682710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682753 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_4682753 : Nat := 118140960795 + 4682753 * 2 ^ 59
def prefixEnd_4682753 : Nat := 4983230072969 + 3 ^ 40 * 4682753 * 2
def baseEnd_4682753 : Nat := 2404503075283622441051917

theorem tailTrace_4682753 : CollatzResearch.WordTrace tailWord_4682753 prefixEnd_4682753 2404503075283622441051917 := by
  unfold tailWord_4682753
  simp only [CollatzResearch.WordTrace]
  refine ⟨170794033204193106386116913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113862688802795404257411275 170794033204193106386116913)
  ·
    refine ⟨128095524903144829789587685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170794033204193106386116913 128095524903144829789587685)
    ·
      refine ⟨24017910919339655585547691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128095524903144829789587685 24017910919339655585547691)
      ·
        refine ⟨36026866379009483378321537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24017910919339655585547691 36026866379009483378321537)
        ·
          refine ⟨27020149784257112533741153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36026866379009483378321537 27020149784257112533741153)
          ·
            refine ⟨20265112338192834400305865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27020149784257112533741153 20265112338192834400305865)
            ·
              refine ⟨15198834253644625800229399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20265112338192834400305865 15198834253644625800229399)
              ·
                refine ⟨22798251380466938700344099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15198834253644625800229399 22798251380466938700344099)
                ·
                  refine ⟨34197377070700408050516149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22798251380466938700344099 34197377070700408050516149)
                  ·
                    refine ⟨3206004100378163254735889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34197377070700408050516149 3206004100378163254735889)
                    ·
                      refine ⟨2404503075283622441051917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206004100378163254735889 2404503075283622441051917)
                      ·
                        rfl

theorem cell23_4682753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_4682753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682753 prefixEnd_4682753 := by exact prefixLift 4682753
  have htrace : WordTrace (prefixWord ++ tailWord_4682753) baseStart_4682753 baseEnd_4682753 := by
    simpa [prefixWord, tailWord_4682753, baseEnd_4682753] using wordTrace_append hprefix tailTrace_4682753
  have hstable : (prefixWord ++ tailWord_4682753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682753).length < 2 ^ (prefixWord ++ tailWord_4682753).sum := by decide
  have hdescent : baseEnd_4682753 < baseStart_4682753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682796 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_4682796 : Nat := 118140960795 + 4682796 * 2 ^ 59
def prefixEnd_4682796 : Nat := 4983230072969 + 3 ^ 40 * 4682796 * 2
def baseEnd_4682796 : Nat := 2404525154951765772814219

theorem tailTrace_4682796 : CollatzResearch.WordTrace tailWord_4682796 prefixEnd_4682796 2404525154951765772814219 := by
  unfold tailWord_4682796
  simp only [CollatzResearch.WordTrace]
  refine ⟨85397800771518662364966121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113863734362024883153288161 85397800771518662364966121)
  ·
    refine ⟨64048350578638996773724591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85397800771518662364966121 64048350578638996773724591)
    ·
      refine ⟨96072525867958495160586887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64048350578638996773724591 96072525867958495160586887)
      ·
        refine ⟨144108788801937742740880331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96072525867958495160586887 144108788801937742740880331)
        ·
          refine ⟨216163183202906614111320497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144108788801937742740880331 216163183202906614111320497)
          ·
            refine ⟨162122387402179960583490373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216163183202906614111320497 162122387402179960583490373)
            ·
              refine ⟨30397947637908742609404445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162122387402179960583490373 30397947637908742609404445)
              ·
                refine ⟨11399230364215778478526667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30397947637908742609404445 11399230364215778478526667)
                ·
                  refine ⟨17098845546323667717790001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11399230364215778478526667 17098845546323667717790001)
                  ·
                    refine ⟨12824134159742750788342501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17098845546323667717790001 12824134159742750788342501)
                    ·
                      refine ⟨2404525154951765772814219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12824134159742750788342501 2404525154951765772814219)
                      ·
                        rfl

theorem cell23_4682796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_4682796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682796 prefixEnd_4682796 := by exact prefixLift 4682796
  have htrace : WordTrace (prefixWord ++ tailWord_4682796) baseStart_4682796 baseEnd_4682796 := by
    simpa [prefixWord, tailWord_4682796, baseEnd_4682796] using wordTrace_append hprefix tailTrace_4682796
  have hstable : (prefixWord ++ tailWord_4682796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682796).length < 2 ^ (prefixWord ++ tailWord_4682796).sum := by decide
  have hdescent : baseEnd_4682796 < baseStart_4682796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682813 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4682813 : Nat := 118140960795 + 4682813 * 2 ^ 59
def prefixEnd_4682813 : Nat := 4983230072969 + 3 ^ 40 * 4682813 * 2
def baseEnd_4682813 : Nat := 2404533884122892206301641

theorem tailTrace_4682813 : CollatzResearch.WordTrace tailWord_4682813 prefixEnd_4682813 2404533884122892206301641 := by
  unfold tailWord_4682813
  simp only [CollatzResearch.WordTrace]
  refine ⟨170796221583975736633301093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113864147722650491088867395 170796221583975736633301093)
  ·
    refine ⟨32024291546995450618743955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170796221583975736633301093 32024291546995450618743955)
    ·
      refine ⟨48036437320493175928115933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32024291546995450618743955 48036437320493175928115933)
      ·
        refine ⟨18013663995184940973043475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48036437320493175928115933 18013663995184940973043475)
        ·
          refine ⟨27020495992777411459565213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18013663995184940973043475 27020495992777411459565213)
          ·
            refine ⟨10132685997291529297336955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27020495992777411459565213 10132685997291529297336955)
            ·
              refine ⟨15199028995937293946005433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10132685997291529297336955 15199028995937293946005433)
              ·
                refine ⟨11399271746952970459504075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15199028995937293946005433 11399271746952970459504075)
                ·
                  refine ⟨17098907620429455689256113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11399271746952970459504075 17098907620429455689256113)
                  ·
                    refine ⟨12824180715322091766942085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17098907620429455689256113 12824180715322091766942085)
                    ·
                      refine ⟨2404533884122892206301641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12824180715322091766942085 2404533884122892206301641)
                      ·
                        rfl

theorem cell23_4682813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4682813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682813 prefixEnd_4682813 := by exact prefixLift 4682813
  have htrace : WordTrace (prefixWord ++ tailWord_4682813) baseStart_4682813 baseEnd_4682813 := by
    simpa [prefixWord, tailWord_4682813, baseEnd_4682813] using wordTrace_append hprefix tailTrace_4682813
  have hstable : (prefixWord ++ tailWord_4682813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682813).length < 2 ^ (prefixWord ++ tailWord_4682813).sum := by decide
  have hdescent : baseEnd_4682813 < baseStart_4682813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682817 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_4682817 : Nat := 118140960795 + 4682817 * 2 ^ 59
def prefixEnd_4682817 : Nat := 4983230072969 + 3 ^ 40 * 4682817 * 2
def baseEnd_4682817 : Nat := 2404535938045510190651623

theorem tailTrace_4682817 : CollatzResearch.WordTrace tailWord_4682817 prefixEnd_4682817 2404535938045510190651623 := by
  unfold tailWord_4682817
  simp only [CollatzResearch.WordTrace]
  refine ⟨170796367475961245316446705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113864244983974163544297803 170796367475961245316446705)
  ·
    refine ⟨128097275606970933987335029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170796367475961245316446705 128097275606970933987335029)
    ·
      refine ⟨12009119588153525061312659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128097275606970933987335029 12009119588153525061312659)
      ·
        refine ⟨18013679382230287591968989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12009119588153525061312659 18013679382230287591968989)
        ·
          refine ⟨6755129768336357846988371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18013679382230287591968989 6755129768336357846988371)
          ·
            refine ⟨10132694652504536770482557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6755129768336357846988371 10132694652504536770482557)
            ·
              refine ⟨3799760494689201288930959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10132694652504536770482557 3799760494689201288930959)
              ·
                refine ⟨5699640742033801933396439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799760494689201288930959 5699640742033801933396439)
                ·
                  refine ⟨8549461113050702900094659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699640742033801933396439 8549461113050702900094659)
                  ·
                    refine ⟨12824191669576054350141989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8549461113050702900094659 12824191669576054350141989)
                    ·
                      refine ⟨2404535938045510190651623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12824191669576054350141989 2404535938045510190651623)
                      ·
                        rfl

theorem cell23_4682817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_4682817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682817 prefixEnd_4682817 := by exact prefixLift 4682817
  have htrace : WordTrace (prefixWord ++ tailWord_4682817) baseStart_4682817 baseEnd_4682817 := by
    simpa [prefixWord, tailWord_4682817, baseEnd_4682817] using wordTrace_append hprefix tailTrace_4682817
  have hstable : (prefixWord ++ tailWord_4682817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682817).length < 2 ^ (prefixWord ++ tailWord_4682817).sum := by decide
  have hdescent : baseEnd_4682817 < baseStart_4682817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682833 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_4682833 : Nat := 118140960795 + 4682833 * 2 ^ 59
def prefixEnd_4682833 : Nat := 4983230072969 + 3 ^ 40 * 4682833 * 2
def baseEnd_4682833 : Nat := 2404544153735982128051549

theorem tailTrace_4682833 : CollatzResearch.WordTrace tailWord_4682833 prefixEnd_4682833 2404544153735982128051549 := by
  unfold tailWord_4682833
  simp only [CollatzResearch.WordTrace]
  refine ⟨170796951043903280049029153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113864634029268853366019435 170796951043903280049029153)
  ·
    refine ⟨128097713282927460036771865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170796951043903280049029153 128097713282927460036771865)
    ·
      refine ⟨96073284962195595027578899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128097713282927460036771865 96073284962195595027578899)
      ·
        refine ⟨144109927443293392541368349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96073284962195595027578899 144109927443293392541368349)
        ·
          refine ⟨54041222791235022203013131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144109927443293392541368349 54041222791235022203013131)
          ·
            refine ⟨81061834186852533304519697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54041222791235022203013131 81061834186852533304519697)
            ·
              refine ⟨60796375640139399978389773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81061834186852533304519697 60796375640139399978389773)
              ·
                refine ⟨22798640865052274991896165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60796375640139399978389773 22798640865052274991896165)
                ·
                  refine ⟨4274745162197301560980531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22798640865052274991896165 4274745162197301560980531)
                  ·
                    refine ⟨6412117743295952341470797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4274745162197301560980531 6412117743295952341470797)
                    ·
                      refine ⟨2404544153735982128051549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6412117743295952341470797 2404544153735982128051549)
                      ·
                        rfl

theorem cell23_4682833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_4682833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682833 prefixEnd_4682833 := by exact prefixLift 4682833
  have htrace : WordTrace (prefixWord ++ tailWord_4682833) baseStart_4682833 baseEnd_4682833 := by
    simpa [prefixWord, tailWord_4682833, baseEnd_4682833] using wordTrace_append hprefix tailTrace_4682833
  have hstable : (prefixWord ++ tailWord_4682833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682833).length < 2 ^ (prefixWord ++ tailWord_4682833).sum := by decide
  have hdescent : baseEnd_4682833 < baseStart_4682833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682834 : List Nat := [3, 2, 2, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_4682834 : Nat := 118140960795 + 4682834 * 2 ^ 59
def prefixEnd_4682834 : Nat := 4983230072969 + 3 ^ 40 * 4682834 * 2
def baseEnd_4682834 : Nat := 2404544667216636624139045

theorem tailTrace_4682834 : CollatzResearch.WordTrace tailWord_4682834 prefixEnd_4682834 2404544667216636624139045 := by
  unfold tailWord_4682834
  simp only [CollatzResearch.WordTrace]
  refine ⟨42699246879224914304953889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113864658344599771479877037 42699246879224914304953889)
  ·
    refine ⟨32024435159418685728715417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42699246879224914304953889 32024435159418685728715417)
    ·
      refine ⟨24018326369564014296536563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32024435159418685728715417 24018326369564014296536563)
      ·
        refine ⟨36027489554346021444804845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24018326369564014296536563 36027489554346021444804845)
        ·
          refine ⟨13510308582879758041801817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36027489554346021444804845 13510308582879758041801817)
          ·
            refine ⟨10132731437159818531351363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13510308582879758041801817 10132731437159818531351363)
            ·
              refine ⟨15199097155739727797027045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10132731437159818531351363 15199097155739727797027045)
              ·
                refine ⟨2849830716701198961942571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15199097155739727797027045 2849830716701198961942571)
                ·
                  refine ⟨4274746075051798442913857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849830716701198961942571 4274746075051798442913857)
                  ·
                    refine ⟨3206059556288848832185393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274746075051798442913857 3206059556288848832185393)
                    ·
                      refine ⟨2404544667216636624139045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206059556288848832185393 2404544667216636624139045)
                      ·
                        rfl

theorem cell23_4682834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_4682834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682834 prefixEnd_4682834 := by exact prefixLift 4682834
  have htrace : WordTrace (prefixWord ++ tailWord_4682834) baseStart_4682834 baseEnd_4682834 := by
    simpa [prefixWord, tailWord_4682834, baseEnd_4682834] using wordTrace_append hprefix tailTrace_4682834
  have hstable : (prefixWord ++ tailWord_4682834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682834).length < 2 ^ (prefixWord ++ tailWord_4682834).sum := by decide
  have hdescent : baseEnd_4682834 < baseStart_4682834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682836 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_4682836 : Nat := 118140960795 + 4682836 * 2 ^ 59
def prefixEnd_4682836 : Nat := 4983230072969 + 3 ^ 40 * 4682836 * 2
def baseEnd_4682836 : Nat := 801515231392648538771345

theorem tailTrace_4682836 : CollatzResearch.WordTrace tailWord_4682836 prefixEnd_4682836 801515231392648538771345 := by
  unfold tailWord_4682836
  simp only [CollatzResearch.WordTrace]
  refine ⟨85398530231446205780694181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113864706975261607707592241 85398530231446205780694181)
  ·
    refine ⟨16012224418396163583880159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85398530231446205780694181 16012224418396163583880159)
    ·
      refine ⟨24018336627594245375820239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16012224418396163583880159 24018336627594245375820239)
      ·
        refine ⟨36027504941391368063730359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24018336627594245375820239 36027504941391368063730359)
        ·
          refine ⟨54041257412087052095595539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36027504941391368063730359 54041257412087052095595539)
          ·
            refine ⟨81061886118130578143393309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54041257412087052095595539 81061886118130578143393309)
            ·
              refine ⟨30398207294298966803772491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81061886118130578143393309 30398207294298966803772491)
              ·
                refine ⟨45597310941448450205658737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30398207294298966803772491 45597310941448450205658737)
                ·
                  refine ⟨34197983206086337654244053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45597310941448450205658737 34197983206086337654244053)
                  ·
                    refine ⟨801515231392648538771345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34197983206086337654244053 801515231392648538771345)
                    ·
                      rfl

theorem cell23_4682836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_4682836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682836 prefixEnd_4682836 := by exact prefixLift 4682836
  have htrace : WordTrace (prefixWord ++ tailWord_4682836) baseStart_4682836 baseEnd_4682836 := by
    simpa [prefixWord, tailWord_4682836, baseEnd_4682836] using wordTrace_append hprefix tailTrace_4682836
  have hstable : (prefixWord ++ tailWord_4682836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682836).length < 2 ^ (prefixWord ++ tailWord_4682836).sum := by decide
  have hdescent : baseEnd_4682836 < baseStart_4682836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682850 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4682850 : Nat := 118140960795 + 4682850 * 2 ^ 59
def prefixEnd_4682850 : Nat := 4983230072969 + 3 ^ 40 * 4682850 * 2
def baseEnd_4682850 : Nat := 2404552882907108561538971

theorem tailTrace_4682850 : CollatzResearch.WordTrace tailWord_4682850 prefixEnd_4682850 2404552882907108561538971 := by
  unfold tailWord_4682850
  simp only [CollatzResearch.WordTrace]
  refine ⟨42699392771210422988099501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113865047389894461301598669 42699392771210422988099501)
  ·
    refine ⟨16012272289203908620537313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42699392771210422988099501 16012272289203908620537313)
    ·
      refine ⟨12009204216902931465402985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16012272289203908620537313 12009204216902931465402985)
      ·
        refine ⟨9006903162677198599052239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12009204216902931465402985 9006903162677198599052239)
        ·
          refine ⟨13510354744015797898578359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006903162677198599052239 13510354744015797898578359)
          ·
            refine ⟨20265532116023696847867539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13510354744015797898578359 20265532116023696847867539)
            ·
              refine ⟨30398298174035545271801309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20265532116023696847867539 30398298174035545271801309)
              ·
                refine ⟨11399361815263329476925491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30398298174035545271801309 11399361815263329476925491)
                ·
                  refine ⟨17099042722894994215388237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11399361815263329476925491 17099042722894994215388237)
                  ·
                    refine ⟨6412141021085622830770589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17099042722894994215388237 6412141021085622830770589)
                    ·
                      refine ⟨2404552882907108561538971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6412141021085622830770589 2404552882907108561538971)
                      ·
                        rfl

theorem cell23_4682850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4682850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682850 prefixEnd_4682850 := by exact prefixLift 4682850
  have htrace : WordTrace (prefixWord ++ tailWord_4682850) baseStart_4682850 baseEnd_4682850 := by
    simpa [prefixWord, tailWord_4682850, baseEnd_4682850] using wordTrace_append hprefix tailTrace_4682850
  have hstable : (prefixWord ++ tailWord_4682850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682850).length < 2 ^ (prefixWord ++ tailWord_4682850).sum := by decide
  have hdescent : baseEnd_4682850 < baseStart_4682850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682860 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 1, 3, 2]
def baseStart_4682860 : Nat := 118140960795 + 4682860 * 2 ^ 59
def prefixEnd_4682860 : Nat := 4983230072969 + 3 ^ 40 * 4682860 * 2
def baseEnd_4682860 : Nat := 2404558017713653522413925

theorem tailTrace_4682860 : CollatzResearch.WordTrace tailWord_4682860 prefixEnd_4682860 2404558017713653522413925 := by
  unfold tailWord_4682860
  simp only [CollatzResearch.WordTrace]
  refine ⟨85398967907402731830131017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113865290543203642440174689 85398967907402731830131017)
  ·
    refine ⟨64049225930552048872598263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85398967907402731830131017 64049225930552048872598263)
    ·
      refine ⟨96073838895828073308897395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64049225930552048872598263 96073838895828073308897395)
      ·
        refine ⟨144110758343742109963346093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96073838895828073308897395 144110758343742109963346093)
        ·
          refine ⟨54041534378903291236254785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144110758343742109963346093 54041534378903291236254785)
          ·
            refine ⟨40531150784177468427191089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54041534378903291236254785 40531150784177468427191089)
            ·
              refine ⟨30398363088133101320393317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40531150784177468427191089 30398363088133101320393317)
              ·
                refine ⟨5699693079024956497573747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30398363088133101320393317 5699693079024956497573747)
                ·
                  refine ⟨8549539618537434746360621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699693079024956497573747 8549539618537434746360621)
                  ·
                    refine ⟨3206077356951538029885233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8549539618537434746360621 3206077356951538029885233)
                    ·
                      refine ⟨2404558017713653522413925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206077356951538029885233 2404558017713653522413925)
                      ·
                        rfl

theorem cell23_4682860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_4682860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682860 prefixEnd_4682860 := by exact prefixLift 4682860
  have htrace : WordTrace (prefixWord ++ tailWord_4682860) baseStart_4682860 baseEnd_4682860 := by
    simpa [prefixWord, tailWord_4682860, baseEnd_4682860] using wordTrace_append hprefix tailTrace_4682860
  have hstable : (prefixWord ++ tailWord_4682860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682860).length < 2 ^ (prefixWord ++ tailWord_4682860).sum := by decide
  have hdescent : baseEnd_4682860 < baseStart_4682860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682866 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_4682866 : Nat := 118140960795 + 4682866 * 2 ^ 59
def prefixEnd_4682866 : Nat := 4983230072969 + 3 ^ 40 * 4682866 * 2
def baseEnd_4682866 : Nat := 801520366199193499646299

theorem tailTrace_4682866 : CollatzResearch.WordTrace tailWord_4682866 prefixEnd_4682866 801520366199193499646299 := by
  unfold tailWord_4682866
  simp only [CollatzResearch.WordTrace]
  refine ⟨42699538663195931671245113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113865436435189151123320301 42699538663195931671245113)
  ·
    refine ⟨32024653997396948753433835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42699538663195931671245113 32024653997396948753433835)
    ·
      refine ⟨48036980996095423130150753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32024653997396948753433835 48036980996095423130150753)
      ·
        refine ⟨36027735747071567347613065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48036980996095423130150753 36027735747071567347613065)
        ·
          refine ⟨27020801810303675510709799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36027735747071567347613065 27020801810303675510709799)
          ·
            refine ⟨40531202715455513266064699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27020801810303675510709799 40531202715455513266064699)
            ·
              refine ⟨60796804073183269899097049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40531202715455513266064699 60796804073183269899097049)
              ·
                refine ⟨45597603054887452424322787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60796804073183269899097049 45597603054887452424322787)
                ·
                  refine ⟨68396404582331178636484181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45597603054887452424322787 68396404582331178636484181)
                  ·
                    refine ⟨801520366199193499646299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68396404582331178636484181 801520366199193499646299)
                    ·
                      rfl

theorem cell23_4682866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_4682866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682866 prefixEnd_4682866 := by exact prefixLift 4682866
  have htrace : WordTrace (prefixWord ++ tailWord_4682866) baseStart_4682866 baseEnd_4682866 := by
    simpa [prefixWord, tailWord_4682866, baseEnd_4682866] using wordTrace_append hprefix tailTrace_4682866
  have hstable : (prefixWord ++ tailWord_4682866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682866).length < 2 ^ (prefixWord ++ tailWord_4682866).sum := by decide
  have hdescent : baseEnd_4682866 < baseStart_4682866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682876 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_4682876 : Nat := 118140960795 + 4682876 * 2 ^ 59
def prefixEnd_4682876 : Nat := 4983230072969 + 3 ^ 40 * 4682876 * 2
def baseEnd_4682876 : Nat := 2404566233404125459813851

theorem tailTrace_4682876 : CollatzResearch.WordTrace tailWord_4682876 prefixEnd_4682876 2404566233404125459813851 := by
  unfold tailWord_4682876
  simp only [CollatzResearch.WordTrace]
  refine ⟨85399259691373749196422241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113865679588498332261896321 85399259691373749196422241)
  ·
    refine ⟨64049444768530311897316681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85399259691373749196422241 64049444768530311897316681)
    ·
      refine ⟨48037083576397733922987511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64049444768530311897316681 48037083576397733922987511)
      ·
        refine ⟨72055625364596600884481267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48037083576397733922987511 72055625364596600884481267)
        ·
          refine ⟨108083438046894901326721901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72055625364596600884481267 108083438046894901326721901)
          ·
            refine ⟨40531289267585587997520713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108083438046894901326721901 40531289267585587997520713)
            ·
              refine ⟨30398466950689190998140535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40531289267585587997520713 30398466950689190998140535)
              ·
                refine ⟨45597700426033786497210803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30398466950689190998140535 45597700426033786497210803)
                ·
                  refine ⟨68396550639050679745816205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45597700426033786497210803 68396550639050679745816205)
                  ·
                    refine ⟨25648706489644004904681077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68396550639050679745816205 25648706489644004904681077)
                    ·
                      refine ⟨2404566233404125459813851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25648706489644004904681077 2404566233404125459813851)
                      ·
                        rfl

theorem cell23_4682876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_4682876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682876 prefixEnd_4682876 := by exact prefixLift 4682876
  have htrace : WordTrace (prefixWord ++ tailWord_4682876) baseStart_4682876 baseEnd_4682876 := by
    simpa [prefixWord, tailWord_4682876, baseEnd_4682876] using wordTrace_append hprefix tailTrace_4682876
  have hstable : (prefixWord ++ tailWord_4682876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682876).length < 2 ^ (prefixWord ++ tailWord_4682876).sum := by decide
  have hdescent : baseEnd_4682876 < baseStart_4682876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682878 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4682878 : Nat := 118140960795 + 4682878 * 2 ^ 59
def prefixEnd_4682878 : Nat := 4983230072969 + 3 ^ 40 * 4682878 * 2
def baseEnd_4682878 : Nat := 801522420121811483996281

theorem tailTrace_4682878 : CollatzResearch.WordTrace tailWord_4682878 prefixEnd_4682878 801522420121811483996281 := by
  unfold tailWord_4682878
  simp only [CollatzResearch.WordTrace]
  refine ⟨21349824041092531591802161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113865728219160168489611525 21349824041092531591802161)
  ·
    refine ⟨16012368030819398693851621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21349824041092531591802161 16012368030819398693851621)
    ·
      refine ⟨3002319005778637255097179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16012368030819398693851621 3002319005778637255097179)
      ·
        refine ⟨4503478508667955882645769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3002319005778637255097179 4503478508667955882645769)
        ·
          refine ⟨3377608881500966911984327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4503478508667955882645769 3377608881500966911984327)
          ·
            refine ⟨5066413322251450367976491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377608881500966911984327 5066413322251450367976491)
            ·
              refine ⟨7599619983377175551964737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066413322251450367976491 7599619983377175551964737)
              ·
                refine ⟨5699714987532881663973553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7599619983377175551964737 5699714987532881663973553)
                ·
                  refine ⟨4274786240649661247980165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5699714987532881663973553 4274786240649661247980165)
                  ·
                    refine ⟨801522420121811483996281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4274786240649661247980165 801522420121811483996281)
                    ·
                      rfl

theorem cell23_4682878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4682878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682878 prefixEnd_4682878 := by exact prefixLift 4682878
  have htrace : WordTrace (prefixWord ++ tailWord_4682878) baseStart_4682878 baseEnd_4682878 := by
    simpa [prefixWord, tailWord_4682878, baseEnd_4682878] using wordTrace_append hprefix tailTrace_4682878
  have hstable : (prefixWord ++ tailWord_4682878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682878).length < 2 ^ (prefixWord ++ tailWord_4682878).sum := by decide
  have hdescent : baseEnd_4682878 < baseStart_4682878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682903 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_4682903 : Nat := 118140960795 + 4682903 * 2 ^ 59
def prefixEnd_4682903 : Nat := 4983230072969 + 3 ^ 40 * 4682903 * 2
def baseEnd_4682903 : Nat := 2404580097381796854176227

theorem tailTrace_4682903 : CollatzResearch.WordTrace tailWord_4682903 prefixEnd_4682903 2404580097381796854176227 := by
  unfold tailWord_4682903
  simp only [CollatzResearch.WordTrace]
  refine ⟨170799504153649682004077363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113866336102433121336051575 170799504153649682004077363)
  ·
    refine ⟨256199256230474523006116045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170799504153649682004077363 256199256230474523006116045)
    ·
      refine ⟨96074721086427946127293517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256199256230474523006116045 96074721086427946127293517)
      ·
        refine ⟨36028020407410479797735069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96074721086427946127293517 36028020407410479797735069)
        ·
          refine ⟨13510507652778929924150651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36028020407410479797735069 13510507652778929924150651)
          ·
            refine ⟨20265761479168394886225977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13510507652778929924150651 20265761479168394886225977)
            ·
              refine ⟨15199321109376296164669483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20265761479168394886225977 15199321109376296164669483)
              ·
                refine ⟨22798981664064444247004225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15199321109376296164669483 22798981664064444247004225)
                ·
                  refine ⟨17099236248048333185253169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22798981664064444247004225 17099236248048333185253169)
                  ·
                    refine ⟨12824427186036249888939877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17099236248048333185253169 12824427186036249888939877)
                    ·
                      refine ⟨2404580097381796854176227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12824427186036249888939877 2404580097381796854176227)
                      ·
                        rfl

theorem cell23_4682903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_4682903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682903 prefixEnd_4682903 := by exact prefixLift 4682903
  have htrace : WordTrace (prefixWord ++ tailWord_4682903) baseStart_4682903 baseEnd_4682903 := by
    simpa [prefixWord, tailWord_4682903, baseEnd_4682903] using wordTrace_append hprefix tailTrace_4682903
  have hstable : (prefixWord ++ tailWord_4682903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682903).length < 2 ^ (prefixWord ++ tailWord_4682903).sum := by decide
  have hdescent : baseEnd_4682903 < baseStart_4682903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682930 : List Nat := [3, 2, 1, 1, 1, 4, 3, 3, 5]
def baseStart_4682930 : Nat := 118140960795 + 4682930 * 2 ^ 59
def prefixEnd_4682930 : Nat := 4983230072969 + 3 ^ 40 * 4682930 * 2
def baseEnd_4682930 : Nat := 267177106817718694282067

theorem tailTrace_4682930 : CollatzResearch.WordTrace tailWord_4682930 prefixEnd_4682930 267177106817718694282067 := by
  unfold tailWord_4682930
  simp only [CollatzResearch.WordTrace]
  refine ⟨42700122231137966403827561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113866992616367910410206829 42700122231137966403827561)
  ·
    refine ⟨32025091673353474802870671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42700122231137966403827561 32025091673353474802870671)
    ·
      refine ⟨48037637510030212204306007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32025091673353474802870671 48037637510030212204306007)
      ·
        refine ⟨72056456265045318306459011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48037637510030212204306007 72056456265045318306459011)
        ·
          refine ⟨108084684397567977459688517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72056456265045318306459011 108084684397567977459688517)
          ·
            refine ⟨20265878324543995773691597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108084684397567977459688517 20265878324543995773691597)
            ·
              refine ⟨7599704371703998415134349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20265878324543995773691597 7599704371703998415134349)
              ·
                refine ⟨2849889139388999405675381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7599704371703998415134349 2849889139388999405675381)
                ·
                  refine ⟨267177106817718694282067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2849889139388999405675381 267177106817718694282067)
                  ·
                    rfl

theorem cell23_4682930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_4682930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682930 prefixEnd_4682930 := by exact prefixLift 4682930
  have htrace : WordTrace (prefixWord ++ tailWord_4682930) baseStart_4682930 baseEnd_4682930 := by
    simpa [prefixWord, tailWord_4682930, baseEnd_4682930] using wordTrace_append hprefix tailTrace_4682930
  have hstable : (prefixWord ++ tailWord_4682930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682930).length < 2 ^ (prefixWord ++ tailWord_4682930).sum := by decide
  have hdescent : baseEnd_4682930 < baseStart_4682930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4682958 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_4682958 : Nat := 118140960795 + 4682958 * 2 ^ 59
def prefixEnd_4682958 : Nat := 4983230072969 + 3 ^ 40 * 4682958 * 2
def baseEnd_4682958 : Nat := 2404608338817794138988475

theorem tailTrace_4682958 : CollatzResearch.WordTrace tailWord_4682958 prefixEnd_4682958 2404608338817794138988475 := by
  unfold tailWord_4682958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21350188771056303299666191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113867673445633617598219685 21350188771056303299666191)
  ·
    refine ⟨32025283156584454949499287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21350188771056303299666191 32025283156584454949499287)
    ·
      refine ⟨48037924734876682424248931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32025283156584454949499287 48037924734876682424248931)
      ·
        refine ⟨72056887102315023636373397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48037924734876682424248931 72056887102315023636373397)
        ·
          refine ⟨3377666582921016732955003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72056887102315023636373397 3377666582921016732955003)
          ·
            refine ⟨5066499874381525099432505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377666582921016732955003 5066499874381525099432505)
            ·
              refine ⟨3799874905786143824574379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5066499874381525099432505 3799874905786143824574379)
              ·
                refine ⟨5699812358679215736861569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799874905786143824574379 5699812358679215736861569)
                ·
                  refine ⟨4274859269009411802646177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5699812358679215736861569 4274859269009411802646177)
                  ·
                    refine ⟨3206144451757058851984633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274859269009411802646177 3206144451757058851984633)
                    ·
                      refine ⟨2404608338817794138988475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206144451757058851984633 2404608338817794138988475)
                      ·
                        rfl

theorem cell23_4682958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_4682958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4682958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4682958 prefixEnd_4682958 := by exact prefixLift 4682958
  have htrace : WordTrace (prefixWord ++ tailWord_4682958) baseStart_4682958 baseEnd_4682958 := by
    simpa [prefixWord, tailWord_4682958, baseEnd_4682958] using wordTrace_append hprefix tailTrace_4682958
  have hstable : (prefixWord ++ tailWord_4682958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4682958).length < 2 ^ (prefixWord ++ tailWord_4682958).sum := by decide
  have hdescent : baseEnd_4682958 < baseStart_4682958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4682958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683007 : List Nat := [1, 1, 2, 2, 1, 6, 1, 4, 1, 4]
def baseStart_4683007 : Nat := 118140960795 + 4683007 * 2 ^ 59
def prefixEnd_4683007 : Nat := 4983230072969 + 3 ^ 40 * 4683007 * 2
def baseEnd_4683007 : Nat := 801544499789954815758583

theorem tailTrace_4683007 : CollatzResearch.WordTrace tailWord_4683007 prefixEnd_4683007 801544499789954815758583 := by
  unfold tailWord_4683007
  simp only [CollatzResearch.WordTrace]
  refine ⟨170803297345272907765863275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113868864896848605177242183 170803297345272907765863275)
  ·
    refine ⟨256204946017909361648794913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170803297345272907765863275 256204946017909361648794913)
    ·
      refine ⟨192153709513432021236596185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256204946017909361648794913 192153709513432021236596185)
      ·
        refine ⟨144115282135074015927447139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192153709513432021236596185 144115282135074015927447139)
        ·
          refine ⟨216172923202611023891170709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144115282135074015927447139 216172923202611023891170709)
          ·
            refine ⟨10133105775122391744898627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 216172923202611023891170709 10133105775122391744898627)
            ·
              refine ⟨15199658662683587617347941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10133105775122391744898627 15199658662683587617347941)
              ·
                refine ⟨2849935999253172678252739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15199658662683587617347941 2849935999253172678252739)
                ·
                  refine ⟨4274903998879759017379109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849935999253172678252739 4274903998879759017379109)
                  ·
                    refine ⟨801544499789954815758583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4274903998879759017379109 801544499789954815758583)
                    ·
                      rfl

theorem cell23_4683007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 4].length) (baseStart_4683007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683007 prefixEnd_4683007 := by exact prefixLift 4683007
  have htrace : WordTrace (prefixWord ++ tailWord_4683007) baseStart_4683007 baseEnd_4683007 := by
    simpa [prefixWord, tailWord_4683007, baseEnd_4683007] using wordTrace_append hprefix tailTrace_4683007
  have hstable : (prefixWord ++ tailWord_4683007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683007).length < 2 ^ (prefixWord ++ tailWord_4683007).sum := by decide
  have hdescent : baseEnd_4683007 < baseStart_4683007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683107 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 3]
def baseStart_4683107 : Nat := 118140960795 + 4683107 * 2 ^ 59
def prefixEnd_4683107 : Nat := 4983230072969 + 3 ^ 40 * 4683107 * 2
def baseEnd_4683107 : Nat := 2404684847435314056025289

theorem tailTrace_4683107 : CollatzResearch.WordTrace tailWord_4683107 prefixEnd_4683107 2404684847435314056025289 := by
  unfold tailWord_4683107
  simp only [CollatzResearch.WordTrace]
  refine ⟨170806944644910624844503575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113871296429940416563002383 170806944644910624844503575)
  ·
    refine ⟨256210416967365937266755363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170806944644910624844503575 256210416967365937266755363)
    ·
      refine ⟨384315625451048905900133045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256210416967365937266755363 384315625451048905900133045)
      ·
        refine ⟨36029589886035834928137473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 384315625451048905900133045 36029589886035834928137473)
        ·
          refine ⟨27022192414526876196103105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36029589886035834928137473 27022192414526876196103105)
          ·
            refine ⟨20266644310895157147077329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27022192414526876196103105 20266644310895157147077329)
            ·
              refine ⟨15199983233171367860307997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20266644310895157147077329 15199983233171367860307997)
              ·
                refine ⟨5699993712439262947615499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15199983233171367860307997 5699993712439262947615499)
                ·
                  refine ⟨8549990568658894421423249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699993712439262947615499 8549990568658894421423249)
                  ·
                    refine ⟨6412492926494170816067437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8549990568658894421423249 6412492926494170816067437)
                    ·
                      refine ⟨2404684847435314056025289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6412492926494170816067437 2404684847435314056025289)
                      ·
                        rfl

theorem cell23_4683107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_4683107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683107 prefixEnd_4683107 := by exact prefixLift 4683107
  have htrace : WordTrace (prefixWord ++ tailWord_4683107) baseStart_4683107 baseEnd_4683107 := by
    simpa [prefixWord, tailWord_4683107, baseEnd_4683107] using wordTrace_append hprefix tailTrace_4683107
  have hstable : (prefixWord ++ tailWord_4683107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683107).length < 2 ^ (prefixWord ++ tailWord_4683107).sum := by decide
  have hdescent : baseEnd_4683107 < baseStart_4683107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683147 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 3, 3, 2]
def baseStart_4683147 : Nat := 118140960795 + 4683147 * 2 ^ 59
def prefixEnd_4683147 : Nat := 4983230072969 + 3 ^ 40 * 4683147 * 2
def baseEnd_4683147 : Nat := 2404705386661493899525105

theorem tailTrace_4683147 : CollatzResearch.WordTrace tailWord_4683147 prefixEnd_4683147 2404705386661493899525105 := by
  unfold tailWord_4683147
  simp only [CollatzResearch.WordTrace]
  refine ⟨170808403564765711675959695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113872269043177141117306463 170808403564765711675959695)
  ·
    refine ⟨256212605347148567513939543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170808403564765711675959695 256212605347148567513939543)
    ·
      refine ⟨384318908020722851270909315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256212605347148567513939543 384318908020722851270909315)
      ·
        refine ⟨576478362031084276906363973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384318908020722851270909315 576478362031084276906363973)
        ·
          refine ⟨108089692880828301919943245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 576478362031084276906363973 108089692880828301919943245)
          ·
            refine ⟨40533634830310613219978717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108089692880828301919943245 40533634830310613219978717)
            ·
              refine ⟨15200113061366479957492019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40533634830310613219978717 15200113061366479957492019)
              ·
                refine ⟨22800169592049719936238029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15200113061366479957492019 22800169592049719936238029)
                ·
                  refine ⟨8550063597018644976089261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22800169592049719936238029 8550063597018644976089261)
                  ·
                    refine ⟨3206273848881991866033473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8550063597018644976089261 3206273848881991866033473)
                    ·
                      refine ⟨2404705386661493899525105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206273848881991866033473 2404705386661493899525105)
                      ·
                        rfl

theorem cell23_4683147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3, 2].length) (baseStart_4683147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683147 prefixEnd_4683147 := by exact prefixLift 4683147
  have htrace : WordTrace (prefixWord ++ tailWord_4683147) baseStart_4683147 baseEnd_4683147 := by
    simpa [prefixWord, tailWord_4683147, baseEnd_4683147] using wordTrace_append hprefix tailTrace_4683147
  have hstable : (prefixWord ++ tailWord_4683147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683147).length < 2 ^ (prefixWord ++ tailWord_4683147).sum := by decide
  have hdescent : baseEnd_4683147 < baseStart_4683147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683153 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 1, 8]
def baseStart_4683153 : Nat := 118140960795 + 4683153 * 2 ^ 59
def prefixEnd_4683153 : Nat := 4983230072969 + 3 ^ 40 * 4683153 * 2
def baseEnd_4683153 : Nat := 801569489181806958683359

theorem tailTrace_4683153 : CollatzResearch.WordTrace tailWord_4683153 prefixEnd_4683153 801569489181806958683359 := by
  unfold tailWord_4683153
  simp only [CollatzResearch.WordTrace]
  refine ⟨170808622402743974700678113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113872414935162649800452075 170808622402743974700678113)
  ·
    refine ⟨128106466802057981025508585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170808622402743974700678113 128106466802057981025508585)
    ·
      refine ⟨96079850101543485769131439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128106466802057981025508585 96079850101543485769131439)
      ·
        refine ⟨144119775152315228653697159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96079850101543485769131439 144119775152315228653697159)
        ·
          refine ⟨216179662728472842980545739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144119775152315228653697159 216179662728472842980545739)
          ·
            refine ⟨324269494092709264470818609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216179662728472842980545739 324269494092709264470818609)
            ·
              refine ⟨243202120569531948353113957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324269494092709264470818609 243202120569531948353113957)
              ·
                refine ⟨45600397606787240316208867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243202120569531948353113957 45600397606787240316208867)
                ·
                  refine ⟨68400596410180860474313301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45600397606787240316208867 68400596410180860474313301)
                  ·
                    refine ⟨801569489181806958683359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68400596410180860474313301 801569489181806958683359)
                    ·
                      rfl

theorem cell23_4683153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_4683153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683153 prefixEnd_4683153 := by exact prefixLift 4683153
  have htrace : WordTrace (prefixWord ++ tailWord_4683153) baseStart_4683153 baseEnd_4683153 := by
    simpa [prefixWord, tailWord_4683153, baseEnd_4683153] using wordTrace_append hprefix tailTrace_4683153
  have hstable : (prefixWord ++ tailWord_4683153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683153).length < 2 ^ (prefixWord ++ tailWord_4683153).sum := by decide
  have hdescent : baseEnd_4683153 < baseStart_4683153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683180 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_4683180 : Nat := 118140960795 + 4683180 * 2 ^ 59
def prefixEnd_4683180 : Nat := 4983230072969 + 3 ^ 40 * 4683180 * 2
def baseEnd_4683180 : Nat := 2404722331523092270412453

theorem tailTrace_4683180 : CollatzResearch.WordTrace tailWord_4683180 prefixEnd_4683180 2404722331523092270412453 := by
  unfold tailWord_4683180
  simp only [CollatzResearch.WordTrace]
  refine ⟨85404803586823079155955497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113873071449097438874607329 85404803586823079155955497)
  ·
    refine ⟨64053602690117309366966623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85404803586823079155955497 64053602690117309366966623)
    ·
      refine ⟨96080404035175964050449935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64053602690117309366966623 96080404035175964050449935)
      ·
        refine ⟨144120606052763946075674903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96080404035175964050449935 144120606052763946075674903)
        ·
          refine ⟨216180909079145919113512355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144120606052763946075674903 216180909079145919113512355)
          ·
            refine ⟨324271363618718878670268533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216180909079145919113512355 324271363618718878670268533)
            ·
              refine ⟨30400440339254894875337675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324271363618718878670268533 30400440339254894875337675)
              ·
                refine ⟨45600660508882342313006513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30400440339254894875337675 45600660508882342313006513)
                ·
                  refine ⟨34200495381661756734754885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45600660508882342313006513 34200495381661756734754885)
                  ·
                    refine ⟨6412592884061579387766541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34200495381661756734754885 6412592884061579387766541)
                    ·
                      refine ⟨2404722331523092270412453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6412592884061579387766541 2404722331523092270412453)
                      ·
                        rfl

theorem cell23_4683180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_4683180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683180 prefixEnd_4683180 := by exact prefixLift 4683180
  have htrace : WordTrace (prefixWord ++ tailWord_4683180) baseStart_4683180 baseEnd_4683180 := by
    simpa [prefixWord, tailWord_4683180, baseEnd_4683180] using wordTrace_append hprefix tailTrace_4683180
  have hstable : (prefixWord ++ tailWord_4683180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683180).length < 2 ^ (prefixWord ++ tailWord_4683180).sum := by decide
  have hdescent : baseEnd_4683180 < baseStart_4683180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683183 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 11]
def baseStart_4683183 : Nat := 118140960795 + 4683183 * 2 ^ 59
def prefixEnd_4683183 : Nat := 4983230072969 + 3 ^ 40 * 4683183 * 2
def baseEnd_4683183 : Nat := 267191541329450639852771

theorem tailTrace_4683183 : CollatzResearch.WordTrace tailWord_4683183 prefixEnd_4683183 267191541329450639852771 := by
  unfold tailWord_4683183
  simp only [CollatzResearch.WordTrace]
  refine ⟨170809716592635289824270203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113873144395090193216180135 170809716592635289824270203)
  ·
    refine ⟨256214574888952934736405305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170809716592635289824270203 256214574888952934736405305)
    ·
      refine ⟨192160931166714701052303979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256214574888952934736405305 192160931166714701052303979)
      ·
        refine ⟨288241396750072051578455969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192160931166714701052303979 288241396750072051578455969)
        ·
          refine ⟨216181047562554038683841977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288241396750072051578455969 216181047562554038683841977)
          ·
            refine ⟨162135785671915529012881483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216181047562554038683841977 162135785671915529012881483)
            ·
              refine ⟨243203678507873293519322225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162135785671915529012881483 243203678507873293519322225)
              ·
                refine ⟨182402758880904970139491669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243203678507873293519322225 182402758880904970139491669)
                ·
                  refine ⟨267191541329450639852771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 182402758880904970139491669 267191541329450639852771)
                  ·
                    rfl

theorem cell23_4683183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 11].length) (baseStart_4683183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683183 prefixEnd_4683183 := by exact prefixLift 4683183
  have htrace : WordTrace (prefixWord ++ tailWord_4683183) baseStart_4683183 baseEnd_4683183 := by
    simpa [prefixWord, tailWord_4683183, baseEnd_4683183] using wordTrace_append hprefix tailTrace_4683183
  have hstable : (prefixWord ++ tailWord_4683183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683183).length < 2 ^ (prefixWord ++ tailWord_4683183).sum := by decide
  have hdescent : baseEnd_4683183 < baseStart_4683183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683240 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4683240 : Nat := 118140960795 + 4683240 * 2 ^ 59
def prefixEnd_4683240 : Nat := 4983230072969 + 3 ^ 40 * 4683240 * 2
def baseEnd_4683240 : Nat := 2404753140362362035662177

theorem tailTrace_4683240 : CollatzResearch.WordTrace tailWord_4683240 prefixEnd_4683240 2404753140362362035662177 := by
  unfold tailWord_4683240
  simp only [CollatzResearch.WordTrace]
  refine ⟨85405897776714394279547587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113874530368952525706063449 85405897776714394279547587)
  ·
    refine ⟨128108846665071591419321381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85405897776714394279547587 128108846665071591419321381)
    ·
      refine ⟨24020408749700923391122759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128108846665071591419321381 24020408749700923391122759)
      ·
        refine ⟨36030613124551385086684139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24020408749700923391122759 36030613124551385086684139)
        ·
          refine ⟨54045919686827077630026209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36030613124551385086684139 54045919686827077630026209)
          ·
            refine ⟨40534439765120308222519657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54045919686827077630026209 40534439765120308222519657)
            ·
              refine ⟨30400829823840231166889743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40534439765120308222519657 30400829823840231166889743)
              ·
                refine ⟨45601244735760346750334615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30400829823840231166889743 45601244735760346750334615)
                ·
                  refine ⟨68401867103640520125501923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45601244735760346750334615 68401867103640520125501923)
                  ·
                    refine ⟨102602800655460780188252885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68401867103640520125501923 102602800655460780188252885)
                    ·
                      refine ⟨2404753140362362035662177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102602800655460780188252885 2404753140362362035662177)
                      ·
                        rfl

theorem cell23_4683240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4683240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683240 prefixEnd_4683240 := by exact prefixLift 4683240
  have htrace : WordTrace (prefixWord ++ tailWord_4683240) baseStart_4683240 baseEnd_4683240 := by
    simpa [prefixWord, tailWord_4683240, baseEnd_4683240] using wordTrace_append hprefix tailTrace_4683240
  have hstable : (prefixWord ++ tailWord_4683240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683240).length < 2 ^ (prefixWord ++ tailWord_4683240).sum := by decide
  have hdescent : baseEnd_4683240 < baseStart_4683240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683245 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4683245 : Nat := 118140960795 + 4683245 * 2 ^ 59
def prefixEnd_4683245 : Nat := 4983230072969 + 3 ^ 40 * 4683245 * 2
def baseEnd_4683245 : Nat := 2404755707765634516099655

theorem tailTrace_4683245 : CollatzResearch.WordTrace tailWord_4683245 prefixEnd_4683245 2404755707765634516099655 := by
  unfold tailWord_4683245
  simp only [CollatzResearch.WordTrace]
  refine ⟨170811977918410674413027189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113874651945607116275351459 170811977918410674413027189)
  ·
    refine ⟨16013622929851000726221299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170811977918410674413027189 16013622929851000726221299)
    ·
      refine ⟨24020434394776501089331949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16013622929851000726221299 24020434394776501089331949)
      ·
        refine ⟨9007662898041187908499481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24020434394776501089331949 9007662898041187908499481)
        ·
          refine ⟨6755747173530890931374611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9007662898041187908499481 6755747173530890931374611)
          ·
            refine ⟨10133620760296336397061917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6755747173530890931374611 10133620760296336397061917)
            ·
              refine ⟨3800107785111126148898219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10133620760296336397061917 3800107785111126148898219)
              ·
                refine ⟨5700161677666689223347329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3800107785111126148898219 5700161677666689223347329)
                ·
                  refine ⟨4275121258250016917510497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5700161677666689223347329 4275121258250016917510497)
                  ·
                    refine ⟨3206340943687512688132873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4275121258250016917510497 3206340943687512688132873)
                    ·
                      refine ⟨2404755707765634516099655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206340943687512688132873 2404755707765634516099655)
                      ·
                        rfl

theorem cell23_4683245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4683245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683245 prefixEnd_4683245 := by exact prefixLift 4683245
  have htrace : WordTrace (prefixWord ++ tailWord_4683245) baseStart_4683245 baseEnd_4683245 := by
    simpa [prefixWord, tailWord_4683245, baseEnd_4683245] using wordTrace_append hprefix tailTrace_4683245
  have hstable : (prefixWord ++ tailWord_4683245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683245).length < 2 ^ (prefixWord ++ tailWord_4683245).sum := by decide
  have hdescent : baseEnd_4683245 < baseStart_4683245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683267 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 4, 4, 2]
def baseStart_4683267 : Nat := 118140960795 + 4683267 * 2 ^ 59
def prefixEnd_4683267 : Nat := 4983230072969 + 3 ^ 40 * 4683267 * 2
def baseEnd_4683267 : Nat := 2404767004340033430024553

theorem tailTrace_4683267 : CollatzResearch.WordTrace tailWord_4683267 prefixEnd_4683267 2404767004340033430024553 := by
  unfold tailWord_4683267
  simp only [CollatzResearch.WordTrace]
  refine ⟨170812780324330972170328055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113875186882887314780218703 170812780324330972170328055)
  ·
    refine ⟨256219170486496458255492083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170812780324330972170328055 256219170486496458255492083)
    ·
      refine ⟨384328755729744687383238125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256219170486496458255492083 384328755729744687383238125)
      ·
        refine ⟨144123283398654257768714297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384328755729744687383238125 144123283398654257768714297)
        ·
          refine ⟨108092462548990693326535723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144123283398654257768714297 108092462548990693326535723)
          ·
            refine ⟨162138693823486039989803585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108092462548990693326535723 162138693823486039989803585)
            ·
              refine ⟨121604020367614529992352689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162138693823486039989803585 121604020367614529992352689)
              ·
                refine ⟨91203015275710897494264517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121604020367614529992352689 91203015275710897494264517)
                ·
                  refine ⟨17100565364195793280174597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91203015275710897494264517 17100565364195793280174597)
                  ·
                    refine ⟨3206356005786711240032737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17100565364195793280174597 3206356005786711240032737)
                    ·
                      refine ⟨2404767004340033430024553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206356005786711240032737 2404767004340033430024553)
                      ·
                        rfl

theorem cell23_4683267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_4683267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683267 prefixEnd_4683267 := by exact prefixLift 4683267
  have htrace : WordTrace (prefixWord ++ tailWord_4683267) baseStart_4683267 baseEnd_4683267 := by
    simpa [prefixWord, tailWord_4683267, baseEnd_4683267] using wordTrace_append hprefix tailTrace_4683267
  have hstable : (prefixWord ++ tailWord_4683267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683267).length < 2 ^ (prefixWord ++ tailWord_4683267).sum := by decide
  have hdescent : baseEnd_4683267 < baseStart_4683267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683268 : List Nat := [2, 3, 2, 3, 3, 1, 1, 3, 5]
def baseStart_4683268 : Nat := 118140960795 + 4683268 * 2 ^ 59
def prefixEnd_4683268 : Nat := 4983230072969 + 3 ^ 40 * 4683268 * 2
def baseEnd_4683268 : Nat := 267196390868965325123561

theorem tailTrace_4683268 : CollatzResearch.WordTrace tailWord_4683268 prefixEnd_4683268 267196390868965325123561 := by
  unfold tailWord_4683268
  simp only [CollatzResearch.WordTrace]
  refine ⟨85406408398663674670557229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113875211198218232894076305 85406408398663674670557229)
  ·
    refine ⟨32027403149498878001458961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85406408398663674670557229 32027403149498878001458961)
    ·
      refine ⟨24020552362124158501094221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32027403149498878001458961 24020552362124158501094221)
      ·
        refine ⟨9007707135796559437910333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24020552362124158501094221 9007707135796559437910333)
        ·
          refine ⟨3377890175923709789216375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9007707135796559437910333 3377890175923709789216375)
          ·
            refine ⟨5066835263885564683824563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377890175923709789216375 5066835263885564683824563)
            ·
              refine ⟨7600252895828347025736845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066835263885564683824563 7600252895828347025736845)
              ·
                refine ⟨2850094835935630134651317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7600252895828347025736845 2850094835935630134651317)
                ·
                  refine ⟨267196390868965325123561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2850094835935630134651317 267196390868965325123561)
                  ·
                    rfl

theorem cell23_4683268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_4683268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683268 prefixEnd_4683268 := by exact prefixLift 4683268
  have htrace : WordTrace (prefixWord ++ tailWord_4683268) baseStart_4683268 baseEnd_4683268 := by
    simpa [prefixWord, tailWord_4683268, baseEnd_4683268] using wordTrace_append hprefix tailTrace_4683268
  have hstable : (prefixWord ++ tailWord_4683268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683268).length < 2 ^ (prefixWord ++ tailWord_4683268).sum := by decide
  have hdescent : baseEnd_4683268 < baseStart_4683268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683337 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 1, 5]
def baseStart_4683337 : Nat := 118140960795 + 4683337 * 2 ^ 59
def prefixEnd_4683337 : Nat := 4983230072969 + 3 ^ 40 * 4683337 * 2
def baseEnd_4683337 : Nat := 801600982661949385383077

theorem tailTrace_4683337 : CollatzResearch.WordTrace tailWord_4683337 prefixEnd_4683337 801600982661949385383077 := by
  unfold tailWord_4683337
  simp only [CollatzResearch.WordTrace]
  refine ⟨170815333434077374125376265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113876888956051582750250843 170815333434077374125376265)
  ·
    refine ⟨128111500075558030594032199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170815333434077374125376265 128111500075558030594032199)
    ·
      refine ⟨192167250113337045891048299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128111500075558030594032199 192167250113337045891048299)
      ·
        refine ⟨288250875170005568836572449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192167250113337045891048299 288250875170005568836572449)
        ·
          refine ⟨216188156377504176627429337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288250875170005568836572449 216188156377504176627429337)
          ·
            refine ⟨162141117283128132470572003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216188156377504176627429337 162141117283128132470572003)
            ·
              refine ⟨243211675924692198705858005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162141117283128132470572003 243211675924692198705858005)
              ·
                refine ⟨5700273654484973407168547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 243211675924692198705858005 5700273654484973407168547)
                ·
                  refine ⟨8550410481727460110752821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5700273654484973407168547 8550410481727460110752821)
                  ·
                    refine ⟨801600982661949385383077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8550410481727460110752821 801600982661949385383077)
                    ·
                      rfl

theorem cell23_4683337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_4683337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683337 prefixEnd_4683337 := by exact prefixLift 4683337
  have htrace : WordTrace (prefixWord ++ tailWord_4683337) baseStart_4683337 baseEnd_4683337 := by
    simpa [prefixWord, tailWord_4683337, baseEnd_4683337] using wordTrace_append hprefix tailTrace_4683337
  have hstable : (prefixWord ++ tailWord_4683337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683337).length < 2 ^ (prefixWord ++ tailWord_4683337).sum := by decide
  have hdescent : baseEnd_4683337 < baseStart_4683337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683341 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 6]
def baseStart_4683341 : Nat := 118140960795 + 4683341 * 2 ^ 59
def prefixEnd_4683341 : Nat := 4983230072969 + 3 ^ 40 * 4683341 * 2
def baseEnd_4683341 : Nat := 267200555767607348944357

theorem tailTrace_4683341 : CollatzResearch.WordTrace tailWord_4683341 prefixEnd_4683341 267200555767607348944357 := by
  unfold tailWord_4683341
  simp only [CollatzResearch.WordTrace]
  refine ⟨170815479326062882808521877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113876986217375255205681251 170815479326062882808521877)
  ·
    refine ⟨8006975593409197631649463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170815479326062882808521877 8006975593409197631649463)
    ·
      refine ⟨12010463390113796447474195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8006975593409197631649463 12010463390113796447474195)
      ·
        refine ⟨18015695085170694671211293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12010463390113796447474195 18015695085170694671211293)
        ·
          refine ⟨6755885656939010501704235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18015695085170694671211293 6755885656939010501704235)
          ·
            refine ⟨10133828485408515752556353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6755885656939010501704235 10133828485408515752556353)
            ·
              refine ⟨7600371364056386814417265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10133828485408515752556353 7600371364056386814417265)
              ·
                refine ⟨5700278523042290110812949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7600371364056386814417265 5700278523042290110812949)
                ·
                  refine ⟨267200555767607348944357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5700278523042290110812949 267200555767607348944357)
                  ·
                    rfl

theorem cell23_4683341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_4683341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683341 prefixEnd_4683341 := by exact prefixLift 4683341
  have htrace : WordTrace (prefixWord ++ tailWord_4683341) baseStart_4683341 baseEnd_4683341 := by
    simpa [prefixWord, tailWord_4683341, baseEnd_4683341] using wordTrace_append hprefix tailTrace_4683341
  have hstable : (prefixWord ++ tailWord_4683341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683341).length < 2 ^ (prefixWord ++ tailWord_4683341).sum := by decide
  have hdescent : baseEnd_4683341 < baseStart_4683341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683344 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 2, 3, 2]
def baseStart_4683344 : Nat := 118140960795 + 4683344 * 2 ^ 59
def prefixEnd_4683344 : Nat := 4983230072969 + 3 ^ 40 * 4683344 * 2
def baseEnd_4683344 : Nat := 2404806542350429628761699

theorem tailTrace_4683344 : CollatzResearch.WordTrace tailWord_4683344 prefixEnd_4683344 2404806542350429628761699 := by
  unfold tailWord_4683344
  simp only [CollatzResearch.WordTrace]
  refine ⟨85407794372526007160440543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113877059163368009547254057 85407794372526007160440543)
  ·
    refine ⟨128111691558789010740660815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85407794372526007160440543 128111691558789010740660815)
    ·
      refine ⟨192167537338183516110991223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128111691558789010740660815 192167537338183516110991223)
      ·
        refine ⟨288251306007275274166486835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192167537338183516110991223 288251306007275274166486835)
        ·
          refine ⟨432376959010912911249730253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288251306007275274166486835 432376959010912911249730253)
          ·
            refine ⟨162141359629092341718648845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 432376959010912911249730253 162141359629092341718648845)
            ·
              refine ⟨60803009860909628144493317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162141359629092341718648845 60803009860909628144493317)
              ·
                refine ⟨11400564348920555277092497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60803009860909628144493317 11400564348920555277092497)
                ·
                  refine ⟨8550423261690416457819373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11400564348920555277092497 8550423261690416457819373)
                  ·
                    refine ⟨3206408723133906171682265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8550423261690416457819373 3206408723133906171682265)
                    ·
                      refine ⟨2404806542350429628761699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206408723133906171682265 2404806542350429628761699)
                      ·
                        rfl

theorem cell23_4683344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 3, 2].length) (baseStart_4683344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683344 prefixEnd_4683344 := by exact prefixLift 4683344
  have htrace : WordTrace (prefixWord ++ tailWord_4683344) baseStart_4683344 baseEnd_4683344 := by
    simpa [prefixWord, tailWord_4683344, baseEnd_4683344] using wordTrace_append hprefix tailTrace_4683344
  have hstable : (prefixWord ++ tailWord_4683344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683344).length < 2 ^ (prefixWord ++ tailWord_4683344).sum := by decide
  have hdescent : baseEnd_4683344 < baseStart_4683344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683367 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 1, 6]
def baseStart_4683367 : Nat := 118140960795 + 4683367 * 2 ^ 59
def prefixEnd_4683367 : Nat := 4983230072969 + 3 ^ 40 * 4683367 * 2
def baseEnd_4683367 : Nat := 801606117468494346258031

theorem tailTrace_4683367 : CollatzResearch.WordTrace tailWord_4683367 prefixEnd_4683367 801606117468494346258031 := by
  unfold tailWord_4683367
  simp only [CollatzResearch.WordTrace]
  refine ⟨170816427623968689248968355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113877618415979126165978903 170816427623968689248968355)
  ·
    refine ⟨256224641435953033873452533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170816427623968689248968355 256224641435953033873452533)
    ·
      refine ⟨24021060134620596925636175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256224641435953033873452533 24021060134620596925636175)
      ·
        refine ⟨36031590201930895388454263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24021060134620596925636175 36031590201930895388454263)
        ·
          refine ⟨54047385302896343082681395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36031590201930895388454263 54047385302896343082681395)
          ·
            refine ⟨81071077954344514624022093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54047385302896343082681395 81071077954344514624022093)
            ·
              refine ⟨30401654232879192984008285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81071077954344514624022093 30401654232879192984008285)
              ·
                refine ⟨11400620337329697369003107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30401654232879192984008285 11400620337329697369003107)
                ·
                  refine ⟨17100930505994546053504661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11400620337329697369003107 17100930505994546053504661)
                  ·
                    refine ⟨801606117468494346258031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17100930505994546053504661 801606117468494346258031)
                    ·
                      rfl

theorem cell23_4683367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_4683367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683367 prefixEnd_4683367 := by exact prefixLift 4683367
  have htrace : WordTrace (prefixWord ++ tailWord_4683367) baseStart_4683367 baseEnd_4683367 := by
    simpa [prefixWord, tailWord_4683367, baseEnd_4683367] using wordTrace_append hprefix tailTrace_4683367
  have hstable : (prefixWord ++ tailWord_4683367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683367).length < 2 ^ (prefixWord ++ tailWord_4683367).sum := by decide
  have hdescent : baseEnd_4683367 < baseStart_4683367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683378 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_4683378 : Nat := 118140960795 + 4683378 * 2 ^ 59
def prefixEnd_4683378 : Nat := 4983230072969 + 3 ^ 40 * 4683378 * 2
def baseEnd_4683378 : Nat := 2404824000692682495736543

theorem tailTrace_4683378 : CollatzResearch.WordTrace tailWord_4683378 prefixEnd_4683378 2404824000692682495736543 := by
  unfold tailWord_4683378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42704207206732209531904697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113877885884619225418412525 42704207206732209531904697)
  ·
    refine ⟨32028155405049157148928523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42704207206732209531904697 32028155405049157148928523)
    ·
      refine ⟨48042233107573735723392785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32028155405049157148928523 48042233107573735723392785)
      ·
        refine ⟨36031674830680301792544589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48042233107573735723392785 36031674830680301792544589)
        ·
          refine ⟨13511878061505113172204221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36031674830680301792544589 13511878061505113172204221)
          ·
            refine ⟨5066954273064417439576583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13511878061505113172204221 5066954273064417439576583)
            ·
              refine ⟨7600431409596626159364875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066954273064417439576583 7600431409596626159364875)
              ·
                refine ⟨11400647114394939239047313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7600431409596626159364875 11400647114394939239047313)
                ·
                  refine ⟨8550485335796204429285485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11400647114394939239047313 8550485335796204429285485)
                  ·
                    refine ⟨3206432000923576660982057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8550485335796204429285485 3206432000923576660982057)
                    ·
                      refine ⟨2404824000692682495736543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206432000923576660982057 2404824000692682495736543)
                      ·
                        rfl

theorem cell23_4683378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_4683378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683378 prefixEnd_4683378 := by exact prefixLift 4683378
  have htrace : WordTrace (prefixWord ++ tailWord_4683378) baseStart_4683378 baseEnd_4683378 := by
    simpa [prefixWord, tailWord_4683378, baseEnd_4683378] using wordTrace_append hprefix tailTrace_4683378
  have hstable : (prefixWord ++ tailWord_4683378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683378).length < 2 ^ (prefixWord ++ tailWord_4683378).sum := by decide
  have hdescent : baseEnd_4683378 < baseStart_4683378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683387 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4]
def baseStart_4683387 : Nat := 118140960795 + 4683387 * 2 ^ 59
def prefixEnd_4683387 : Nat := 4983230072969 + 3 ^ 40 * 4683387 * 2
def baseEnd_4683387 : Nat := 2404828622018572960524001

theorem tailTrace_4683387 : CollatzResearch.WordTrace tailWord_4683387 prefixEnd_4683387 2404828622018572960524001 := by
  unfold tailWord_4683387
  simp only [CollatzResearch.WordTrace]
  refine ⟨170817157083896232664696415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113878104722597488443130943 170817157083896232664696415)
  ·
    refine ⟨256225735625844348997044623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170817157083896232664696415 256225735625844348997044623)
    ·
      refine ⟨384338603438766523495566935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256225735625844348997044623 384338603438766523495566935)
      ·
        refine ⟨576507905158149785243350403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384338603438766523495566935 576507905158149785243350403)
        ·
          refine ⟨864761857737224677865025605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576507905158149785243350403 864761857737224677865025605)
          ·
            refine ⟨162142848325729627099692301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 864761857737224677865025605 162142848325729627099692301)
            ·
              refine ⟨60803568122148610162384613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162142848325729627099692301 60803568122148610162384613)
              ·
                refine ⟨11400669022902864405447115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60803568122148610162384613 11400669022902864405447115)
                ·
                  refine ⟨17101003534354296608170673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11400669022902864405447115 17101003534354296608170673)
                  ·
                    refine ⟨12825752650765722456128005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17101003534354296608170673 12825752650765722456128005)
                    ·
                      refine ⟨2404828622018572960524001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12825752650765722456128005 2404828622018572960524001)
                      ·
                        rfl

theorem cell23_4683387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4].length) (baseStart_4683387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683387 prefixEnd_4683387 := by exact prefixLift 4683387
  have htrace : WordTrace (prefixWord ++ tailWord_4683387) baseStart_4683387 baseEnd_4683387 := by
    simpa [prefixWord, tailWord_4683387, baseEnd_4683387] using wordTrace_append hprefix tailTrace_4683387
  have hstable : (prefixWord ++ tailWord_4683387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683387).length < 2 ^ (prefixWord ++ tailWord_4683387).sum := by decide
  have hdescent : baseEnd_4683387 < baseStart_4683387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683485 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4683485 : Nat := 118140960795 + 4683485 * 2 ^ 59
def prefixEnd_4683485 : Nat := 4983230072969 + 3 ^ 40 * 4683485 * 2
def baseEnd_4683485 : Nat := 2404878943122713577098551

theorem tailTrace_4683485 : CollatzResearch.WordTrace tailWord_4683485 prefixEnd_4683485 2404878943122713577098551 := by
  unfold tailWord_4683485
  simp only [CollatzResearch.WordTrace]
  refine ⟨170820731437541195401763909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113880487625027463601175939 170820731437541195401763909)
  ·
    refine ⟨32028887144538974137830733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170820731437541195401763909 32028887144538974137830733)
    ·
      refine ⟨12010832679202115301686525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32028887144538974137830733 12010832679202115301686525)
      ·
        refine ⟨4504062254700793238132447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12010832679202115301686525 4504062254700793238132447)
        ·
          refine ⟨6756093382051189857198671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4504062254700793238132447 6756093382051189857198671)
          ·
            refine ⟨10134140073076784785798007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6756093382051189857198671 10134140073076784785798007)
            ·
              refine ⟨15201210109615177178697011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10134140073076784785798007 15201210109615177178697011)
              ·
                refine ⟨22801815164422765768045517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15201210109615177178697011 22801815164422765768045517)
                ·
                  refine ⟨8550680686658537163017069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22801815164422765768045517 8550680686658537163017069)
                  ·
                    refine ⟨3206505257496951436131401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8550680686658537163017069 3206505257496951436131401)
                    ·
                      refine ⟨2404878943122713577098551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206505257496951436131401 2404878943122713577098551)
                      ·
                        rfl

theorem cell23_4683485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4683485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683485 prefixEnd_4683485 := by exact prefixLift 4683485
  have htrace : WordTrace (prefixWord ++ tailWord_4683485) baseStart_4683485 baseEnd_4683485 := by
    simpa [prefixWord, tailWord_4683485, baseEnd_4683485] using wordTrace_append hprefix tailTrace_4683485
  have hstable : (prefixWord ++ tailWord_4683485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683485).length < 2 ^ (prefixWord ++ tailWord_4683485).sum := by decide
  have hdescent : baseEnd_4683485 < baseStart_4683485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683487 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 9]
def baseStart_4683487 : Nat := 118140960795 + 4683487 * 2 ^ 59
def prefixEnd_4683487 : Nat := 4983230072969 + 3 ^ 40 * 4683487 * 2
def baseEnd_4683487 : Nat := 267208885564891396585949

theorem tailTrace_4683487 : CollatzResearch.WordTrace tailWord_4683487 prefixEnd_4683487 267208885564891396585949 := by
  unfold tailWord_4683487
  simp only [CollatzResearch.WordTrace]
  refine ⟨170820804383533949743336715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113880536255689299828891143 170820804383533949743336715)
  ·
    refine ⟨256231206575300924615005073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170820804383533949743336715 256231206575300924615005073)
    ·
      refine ⟨192173404931475693461253805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256231206575300924615005073 192173404931475693461253805)
      ·
        refine ⟨72065026849303385047970177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192173404931475693461253805 72065026849303385047970177)
        ·
          refine ⟨54048770136977538785977633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72065026849303385047970177 54048770136977538785977633)
          ·
            refine ⟨40536577602733154089483225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54048770136977538785977633 40536577602733154089483225)
            ·
              refine ⟨30402433202049865567112419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40536577602733154089483225 30402433202049865567112419)
              ·
                refine ⟨45603649803074798350668629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30402433202049865567112419 45603649803074798350668629)
                ·
                  refine ⟨267208885564891396585949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45603649803074798350668629 267208885564891396585949)
                  ·
                    rfl

theorem cell23_4683487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 9].length) (baseStart_4683487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683487 prefixEnd_4683487 := by exact prefixLift 4683487
  have htrace : WordTrace (prefixWord ++ tailWord_4683487) baseStart_4683487 baseEnd_4683487 := by
    simpa [prefixWord, tailWord_4683487, baseEnd_4683487] using wordTrace_append hprefix tailTrace_4683487
  have hstable : (prefixWord ++ tailWord_4683487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683487).length < 2 ^ (prefixWord ++ tailWord_4683487).sum := by decide
  have hdescent : baseEnd_4683487 < baseStart_4683487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683514 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_4683514 : Nat := 118140960795 + 4683514 * 2 ^ 59
def prefixEnd_4683514 : Nat := 4983230072969 + 3 ^ 40 * 4683514 * 2
def baseEnd_4683514 : Nat := 2404893834061693963635917

theorem tailTrace_4683514 : CollatzResearch.WordTrace tailWord_4683514 prefixEnd_4683514 2404893834061693963635917 := by
  unfold tailWord_4683514
  simp only [CollatzResearch.WordTrace]
  refine ⟨42705447288609033338642399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113881192769624088903046397 42705447288609033338642399)
  ·
    refine ⟨64058170932913550007963599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42705447288609033338642399 64058170932913550007963599)
    ·
      refine ⟨96087256399370325011945399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64058170932913550007963599 96087256399370325011945399)
      ·
        refine ⟨144130884599055487517918099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96087256399370325011945399 144130884599055487517918099)
        ·
          refine ⟨216196326898583231276877149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144130884599055487517918099 216196326898583231276877149)
          ·
            refine ⟨81073622586968711728828931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216196326898583231276877149 81073622586968711728828931)
            ·
              refine ⟨121610433880453067593243397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81073622586968711728828931 121610433880453067593243397)
              ·
                refine ⟨22801956352584950173733137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121610433880453067593243397 22801956352584950173733137)
                ·
                  refine ⟨17101467264438712630299853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22801956352584950173733137 17101467264438712630299853)
                  ·
                    refine ⟨6413050224164517236362445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17101467264438712630299853 6413050224164517236362445)
                    ·
                      refine ⟨2404893834061693963635917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6413050224164517236362445 2404893834061693963635917)
                      ·
                        rfl

theorem cell23_4683514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_4683514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683514 prefixEnd_4683514 := by exact prefixLift 4683514
  have htrace : WordTrace (prefixWord ++ tailWord_4683514) baseStart_4683514 baseEnd_4683514 := by
    simpa [prefixWord, tailWord_4683514, baseEnd_4683514] using wordTrace_append hprefix tailTrace_4683514
  have hstable : (prefixWord ++ tailWord_4683514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683514).length < 2 ^ (prefixWord ++ tailWord_4683514).sum := by decide
  have hdescent : baseEnd_4683514 < baseStart_4683514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683534 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_4683534 : Nat := 118140960795 + 4683534 * 2 ^ 59
def prefixEnd_4683534 : Nat := 4983230072969 + 3 ^ 40 * 4683534 * 2
def baseEnd_4683534 : Nat := 801634701224927961795275

theorem tailTrace_4683534 : CollatzResearch.WordTrace tailWord_4683534 prefixEnd_4683534 801634701224927961795275 := by
  unfold tailWord_4683534
  simp only [CollatzResearch.WordTrace]
  refine ⟨21352814826795459596287207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113881679076242451180198437 21352814826795459596287207)
  ·
    refine ⟨32029222240193189394430811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21352814826795459596287207 32029222240193189394430811)
    ·
      refine ⟨48043833360289784091646217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32029222240193189394430811 48043833360289784091646217)
      ·
        refine ⟨36032875020217338068734663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48043833360289784091646217 36032875020217338068734663)
        ·
          refine ⟨54049312530326007103101995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36032875020217338068734663 54049312530326007103101995)
          ·
            refine ⟨81073968795489010654652993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54049312530326007103101995 81073968795489010654652993)
            ·
              refine ⟨60805476596616757990989745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81073968795489010654652993 60805476596616757990989745)
              ·
                refine ⟨45604107447462568493242309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60805476596616757990989745 45604107447462568493242309)
                ·
                  refine ⟨8550770146399231592482933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45604107447462568493242309 8550770146399231592482933)
                  ·
                    refine ⟨801634701224927961795275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8550770146399231592482933 801634701224927961795275)
                    ·
                      rfl

theorem cell23_4683534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_4683534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683534 prefixEnd_4683534 := by exact prefixLift 4683534
  have htrace : WordTrace (prefixWord ++ tailWord_4683534) baseStart_4683534 baseEnd_4683534 := by
    simpa [prefixWord, tailWord_4683534, baseEnd_4683534] using wordTrace_append hprefix tailTrace_4683534
  have hstable : (prefixWord ++ tailWord_4683534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683534).length < 2 ^ (prefixWord ++ tailWord_4683534).sum := by decide
  have hdescent : baseEnd_4683534 < baseStart_4683534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683547 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 2, 8]
def baseStart_4683547 : Nat := 118140960795 + 4683547 * 2 ^ 59
def prefixEnd_4683547 : Nat := 4983230072969 + 3 ^ 40 * 4683547 * 2
def baseEnd_4683547 : Nat := 801636926307764111507755

theorem tailTrace_4683547 : CollatzResearch.WordTrace tailWord_4683547 prefixEnd_4683547 801636926307764111507755 := by
  unfold tailWord_4683547
  simp only [CollatzResearch.WordTrace]
  refine ⟨170822992763316579990520895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113881995175544386660347263 170822992763316579990520895)
  ·
    refine ⟨256234489144974869985781343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170822992763316579990520895 256234489144974869985781343)
    ·
      refine ⟨384351733717462304978672015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256234489144974869985781343 384351733717462304978672015)
      ·
        refine ⟨576527600576193457468008023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384351733717462304978672015 576527600576193457468008023)
        ·
          refine ⟨864791400864290186202012035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576527600576193457468008023 864791400864290186202012035)
          ·
            refine ⟨1297187101296435279303018053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864791400864290186202012035 1297187101296435279303018053)
            ·
              refine ⟨243222581493081614869315885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1297187101296435279303018053 243222581493081614869315885)
              ·
                refine ⟨91208468059905605575993457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243222581493081614869315885 91208468059905605575993457)
                ·
                  refine ⟨68406351044929204181995093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91208468059905605575993457 68406351044929204181995093)
                  ·
                    refine ⟨801636926307764111507755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68406351044929204181995093 801636926307764111507755)
                    ·
                      rfl

theorem cell23_4683547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_4683547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683547 prefixEnd_4683547 := by exact prefixLift 4683547
  have htrace : WordTrace (prefixWord ++ tailWord_4683547) baseStart_4683547 baseEnd_4683547 := by
    simpa [prefixWord, tailWord_4683547, baseEnd_4683547] using wordTrace_append hprefix tailTrace_4683547
  have hstable : (prefixWord ++ tailWord_4683547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683547).length < 2 ^ (prefixWord ++ tailWord_4683547).sum := by decide
  have hdescent : baseEnd_4683547 < baseStart_4683547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683615 : List Nat := [1, 1, 2, 3, 1, 6, 1, 3, 1, 4]
def baseStart_4683615 : Nat := 118140960795 + 4683615 * 2 ^ 59
def prefixEnd_4683615 : Nat := 4983230072969 + 3 ^ 40 * 4683615 * 2
def baseEnd_4683615 : Nat := 801648565202599356157651

theorem tailTrace_4683615 : CollatzResearch.WordTrace tailWord_4683615 prefixEnd_4683615 801648565202599356157651 := by
  unfold tailWord_4683615
  simp only [CollatzResearch.WordTrace]
  refine ⟨170825472927070227603996299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113883648618046818402664199 170825472927070227603996299)
  ·
    refine ⟨256238209390605341405994449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170825472927070227603996299 256238209390605341405994449)
    ·
      refine ⟨192178657042954006054495837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256238209390605341405994449 192178657042954006054495837)
      ·
        refine ⟨72066996391107752270435939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192178657042954006054495837 72066996391107752270435939)
        ·
          refine ⟨108100494586661628405653909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72066996391107752270435939 108100494586661628405653909)
          ·
            refine ⟨5067210683749763831515027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108100494586661628405653909 5067210683749763831515027)
            ·
              refine ⟨7600816025624645747272541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5067210683749763831515027 7600816025624645747272541)
              ·
                refine ⟨2850306009609242155227203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7600816025624645747272541 2850306009609242155227203)
                ·
                  refine ⟨4275459014413863232840805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850306009609242155227203 4275459014413863232840805)
                  ·
                    refine ⟨801648565202599356157651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4275459014413863232840805 801648565202599356157651)
                    ·
                      rfl

theorem cell23_4683615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 4].length) (baseStart_4683615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683615 prefixEnd_4683615 := by exact prefixLift 4683615
  have htrace : WordTrace (prefixWord ++ tailWord_4683615) baseStart_4683615 baseEnd_4683615 := by
    simpa [prefixWord, tailWord_4683615, baseEnd_4683615] using wordTrace_append hprefix tailTrace_4683615
  have hstable : (prefixWord ++ tailWord_4683615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683615).length < 2 ^ (prefixWord ++ tailWord_4683615).sum := by decide
  have hdescent : baseEnd_4683615 < baseStart_4683615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683634 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4683634 : Nat := 118140960795 + 4683634 * 2 ^ 59
def prefixEnd_4683634 : Nat := 4983230072969 + 3 ^ 40 * 4683634 * 2
def baseEnd_4683634 : Nat := 2404955451740233494135365

theorem tailTrace_4683634 : CollatzResearch.WordTrace tailWord_4683634 prefixEnd_4683634 2404955451740233494135365 := by
  unfold tailWord_4683634
  simp only [CollatzResearch.WordTrace]
  refine ⟨42706541478500348462234489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113884110609334262565958637 42706541478500348462234489)
  ·
    refine ⟨32029906108875261346675867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42706541478500348462234489 32029906108875261346675867)
    ·
      refine ⟨48044859163312892020013801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32029906108875261346675867 48044859163312892020013801)
      ·
        refine ⟨36033644372484669015010351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48044859163312892020013801 36033644372484669015010351)
        ·
          refine ⟨54050466558727003522515527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36033644372484669015010351 54050466558727003522515527)
          ·
            refine ⟨81075699838090505283773291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54050466558727003522515527 81075699838090505283773291)
            ·
              refine ⟨121613549757135757925659937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81075699838090505283773291 121613549757135757925659937)
              ·
                refine ⟨91210162317851818444244953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121613549757135757925659937 91210162317851818444244953)
                ·
                  refine ⟨68407621738388863833183715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91210162317851818444244953 68407621738388863833183715)
                  ·
                    refine ⟨102611432607583295749775573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68407621738388863833183715 102611432607583295749775573)
                    ·
                      refine ⟨2404955451740233494135365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102611432607583295749775573 2404955451740233494135365)
                      ·
                        rfl

theorem cell23_4683634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4683634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683634 prefixEnd_4683634 := by exact prefixLift 4683634
  have htrace : WordTrace (prefixWord ++ tailWord_4683634) baseStart_4683634 baseEnd_4683634 := by
    simpa [prefixWord, tailWord_4683634, baseEnd_4683634] using wordTrace_append hprefix tailTrace_4683634
  have hstable : (prefixWord ++ tailWord_4683634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683634).length < 2 ^ (prefixWord ++ tailWord_4683634).sum := by decide
  have hdescent : baseEnd_4683634 < baseStart_4683634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683644 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_4683644 : Nat := 118140960795 + 4683644 * 2 ^ 59
def prefixEnd_4683644 : Nat := 4983230072969 + 3 ^ 40 * 4683644 * 2
def baseEnd_4683644 : Nat := 2404960586546778455010319

theorem tailTrace_4683644 : CollatzResearch.WordTrace tailWord_4683644 prefixEnd_4683644 2404960586546778455010319 := by
  unfold tailWord_4683644
  simp only [CollatzResearch.WordTrace]
  refine ⟨85413265321982582778400993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113884353762643443704534657 85413265321982582778400993)
  ·
    refine ⟨64059948991486937083800745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85413265321982582778400993 64059948991486937083800745)
    ·
      refine ⟨48044961743615202812850559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64059948991486937083800745 48044961743615202812850559)
      ·
        refine ⟨72067442615422804219275839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48044961743615202812850559 72067442615422804219275839)
        ·
          refine ⟨108101163923134206328913759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72067442615422804219275839 108101163923134206328913759)
          ·
            refine ⟨162151745884701309493370639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108101163923134206328913759 162151745884701309493370639)
            ·
              refine ⟨243227618827051964240055959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162151745884701309493370639 243227618827051964240055959)
              ·
                refine ⟨364841428240577946360083939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243227618827051964240055959 364841428240577946360083939)
                ·
                  refine ⟨547262142360866919540125909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364841428240577946360083939 547262142360866919540125909)
                  ·
                    refine ⟨12826456461582818426721701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 547262142360866919540125909 12826456461582818426721701)
                    ·
                      refine ⟨2404960586546778455010319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12826456461582818426721701 2404960586546778455010319)
                      ·
                        rfl

theorem cell23_4683644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_4683644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683644 prefixEnd_4683644 := by exact prefixLift 4683644
  have htrace : WordTrace (prefixWord ++ tailWord_4683644) baseStart_4683644 baseEnd_4683644 := by
    simpa [prefixWord, tailWord_4683644, baseEnd_4683644] using wordTrace_append hprefix tailTrace_4683644
  have hstable : (prefixWord ++ tailWord_4683644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683644).length < 2 ^ (prefixWord ++ tailWord_4683644).sum := by decide
  have hdescent : baseEnd_4683644 < baseStart_4683644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683658 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_4683658 : Nat := 118140960795 + 4683658 * 2 ^ 59
def prefixEnd_4683658 : Nat := 4983230072969 + 3 ^ 40 * 4683658 * 2
def baseEnd_4683658 : Nat := 801655925091980466745085

theorem tailTrace_4683658 : CollatzResearch.WordTrace tailWord_4683658 prefixEnd_4683658 801655925091980466745085 := by
  unfold tailWord_4683658
  simp only [CollatzResearch.WordTrace]
  refine ⟨42706760316478611486952907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113884694177276297298541085 42706760316478611486952907)
  ·
    refine ⟨64060140474717917230429361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42706760316478611486952907 64060140474717917230429361)
    ·
      refine ⟨48045105356038437922822021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64060140474717917230429361 48045105356038437922822021)
      ·
        refine ⟨9008457254257207110529129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48045105356038437922822021 9008457254257207110529129)
        ·
          refine ⟨6756342940692905332896847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9008457254257207110529129 6756342940692905332896847)
          ·
            refine ⟨10134514411039357999345271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6756342940692905332896847 10134514411039357999345271)
            ·
              refine ⟨15201771616559036999017907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10134514411039357999345271 15201771616559036999017907)
              ·
                refine ⟨22802657424838555498526861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15201771616559036999017907 22802657424838555498526861)
                ·
                  refine ⟨8550996534314458311947573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22802657424838555498526861 8550996534314458311947573)
                  ·
                    refine ⟨801655925091980466745085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8550996534314458311947573 801655925091980466745085)
                    ·
                      rfl

theorem cell23_4683658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_4683658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683658 prefixEnd_4683658 := by exact prefixLift 4683658
  have htrace : WordTrace (prefixWord ++ tailWord_4683658) baseStart_4683658 baseEnd_4683658 := by
    simpa [prefixWord, tailWord_4683658, baseEnd_4683658] using wordTrace_append hprefix tailTrace_4683658
  have hstable : (prefixWord ++ tailWord_4683658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683658).length < 2 ^ (prefixWord ++ tailWord_4683658).sum := by decide
  have hdescent : baseEnd_4683658 < baseStart_4683658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683664 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_4683664 : Nat := 118140960795 + 4683664 * 2 ^ 59
def prefixEnd_4683664 : Nat := 4983230072969 + 3 ^ 40 * 4683664 * 2
def baseEnd_4683664 : Nat := 2404970856159868376760227

theorem tailTrace_4683664 : CollatzResearch.WordTrace tailWord_4683664 prefixEnd_4683664 2404970856159868376760227 := by
  unfold tailWord_4683664
  simp only [CollatzResearch.WordTrace]
  refine ⟨85413630051946354486265023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113884840069261805981686697 85413630051946354486265023)
  ·
    refine ⟨128120445077919531729397535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85413630051946354486265023 128120445077919531729397535)
    ·
      refine ⟨192180667616879297594096303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128120445077919531729397535 192180667616879297594096303)
      ·
        refine ⟨288271001425318946391144455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192180667616879297594096303 288271001425318946391144455)
        ·
          refine ⟨432406502137978419586716683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288271001425318946391144455 432406502137978419586716683)
          ·
            refine ⟨648609753206967629380075025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432406502137978419586716683 648609753206967629380075025)
            ·
              refine ⟨486457314905225722035056269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648609753206967629380075025 486457314905225722035056269)
              ·
                refine ⟨182421493089459645763146101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 486457314905225722035056269 182421493089459645763146101)
                ·
                  refine ⟨17102014977136841790294947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182421493089459645763146101 17102014977136841790294947)
                  ·
                    refine ⟨25653022465705262685442421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17102014977136841790294947 25653022465705262685442421)
                    ·
                      refine ⟨2404970856159868376760227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25653022465705262685442421 2404970856159868376760227)
                      ·
                        rfl

theorem cell23_4683664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_4683664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683664 prefixEnd_4683664 := by exact prefixLift 4683664
  have htrace : WordTrace (prefixWord ++ tailWord_4683664) baseStart_4683664 baseEnd_4683664 := by
    simpa [prefixWord, tailWord_4683664, baseEnd_4683664] using wordTrace_append hprefix tailTrace_4683664
  have hstable : (prefixWord ++ tailWord_4683664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683664).length < 2 ^ (prefixWord ++ tailWord_4683664).sum := by decide
  have hdescent : baseEnd_4683664 < baseStart_4683664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683671 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 1, 6]
def baseStart_4683671 : Nat := 118140960795 + 4683671 * 2 ^ 59
def prefixEnd_4683671 : Nat := 4983230072969 + 3 ^ 40 * 4683671 * 2
def baseEnd_4683671 : Nat := 801658150174816616457565

theorem tailTrace_4683671 : CollatzResearch.WordTrace tailWord_4683671 prefixEnd_4683671 801658150174816616457565 := by
  unfold tailWord_4683671
  simp only [CollatzResearch.WordTrace]
  refine ⟨170827515414867349168034867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113885010276578232778689911 170827515414867349168034867)
  ·
    refine ⟨256241273122301023752052301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170827515414867349168034867 256241273122301023752052301)
    ·
      refine ⟨96090477420862883907019613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256241273122301023752052301 96090477420862883907019613)
      ·
        refine ⟨36033929032823581465132355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96090477420862883907019613 36033929032823581465132355)
        ·
          refine ⟨54050893549235372197698533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36033929032823581465132355 54050893549235372197698533)
          ·
            refine ⟨10134542540481632287068475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54050893549235372197698533 10134542540481632287068475)
            ·
              refine ⟨15201813810722448430602713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10134542540481632287068475 15201813810722448430602713)
              ·
                refine ⟨11401360358041836322952035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15201813810722448430602713 11401360358041836322952035)
                ·
                  refine ⟨17102040537062754484428053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11401360358041836322952035 17102040537062754484428053)
                  ·
                    refine ⟨801658150174816616457565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17102040537062754484428053 801658150174816616457565)
                    ·
                      rfl

theorem cell23_4683671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_4683671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683671 prefixEnd_4683671 := by exact prefixLift 4683671
  have htrace : WordTrace (prefixWord ++ tailWord_4683671) baseStart_4683671 baseEnd_4683671 := by
    simpa [prefixWord, tailWord_4683671, baseEnd_4683671] using wordTrace_append hprefix tailTrace_4683671
  have hstable : (prefixWord ++ tailWord_4683671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683671).length < 2 ^ (prefixWord ++ tailWord_4683671).sum := by decide
  have hdescent : baseEnd_4683671 < baseStart_4683671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683684 : List Nat := [2, 3, 1, 2, 1, 14]
def baseStart_4683684 : Nat := 118140960795 + 4683684 * 2 ^ 59
def prefixEnd_4683684 : Nat := 4983230072969 + 3 ^ 40 * 4683684 * 2
def baseEnd_4683684 : Nat := 9897041669847565014445

theorem tailTrace_4683684 : CollatzResearch.WordTrace tailWord_4683684 prefixEnd_4683684 9897041669847565014445 := by
  unfold tailWord_4683684
  simp only [CollatzResearch.WordTrace]
  refine ⟨85413994781910126194129053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113885326375880168258838737 85413994781910126194129053)
  ·
    refine ⟨32030248043216297322798395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85413994781910126194129053 32030248043216297322798395)
    ·
      refine ⟨48045372064824445984197593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32030248043216297322798395 48045372064824445984197593)
      ·
        refine ⟨36034029048618334488148195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48045372064824445984197593 36034029048618334488148195)
        ·
          refine ⟨54051043572927501732222293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36034029048618334488148195 54051043572927501732222293)
          ·
            refine ⟨9897041669847565014445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 54051043572927501732222293 9897041669847565014445)
            ·
              rfl

theorem cell23_4683684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 14].length) (baseStart_4683684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683684 prefixEnd_4683684 := by exact prefixLift 4683684
  have htrace : WordTrace (prefixWord ++ tailWord_4683684) baseStart_4683684 baseEnd_4683684 := by
    simpa [prefixWord, tailWord_4683684, baseEnd_4683684] using wordTrace_append hprefix tailTrace_4683684
  have hstable : (prefixWord ++ tailWord_4683684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683684).length < 2 ^ (prefixWord ++ tailWord_4683684).sum := by decide
  have hdescent : baseEnd_4683684 < baseStart_4683684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683701 : List Nat := [1, 3, 3, 2, 1, 2, 3, 8]
def baseStart_4683701 : Nat := 118140960795 + 4683701 * 2 ^ 59
def prefixEnd_4683701 : Nat := 4983230072969 + 3 ^ 40 * 4683701 * 2
def baseEnd_4683701 : Nat := 89073698331262397481391

theorem tailTrace_4683701 : CollatzResearch.WordTrace tailWord_4683701 prefixEnd_4683701 89073698331262397481391 := by
  unfold tailWord_4683701
  simp only [CollatzResearch.WordTrace]
  refine ⟨170828609604758664291626957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113885739736505776194417971 170828609604758664291626957)
  ·
    refine ⟨64060728601784499109360109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170828609604758664291626957 64060728601784499109360109)
    ·
      refine ⟨24022773225669187166010041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64060728601784499109360109 24022773225669187166010041)
      ·
        refine ⟨18017079919251890374507531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24022773225669187166010041 18017079919251890374507531)
        ·
          refine ⟨27025619878877835561761297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18017079919251890374507531 27025619878877835561761297)
          ·
            refine ⟨20269214909158376671320973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27025619878877835561761297 20269214909158376671320973)
            ·
              refine ⟨7600955590934391251745365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20269214909158376671320973 7600955590934391251745365)
              ·
                refine ⟨89073698331262397481391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7600955590934391251745365 89073698331262397481391)
                ·
                  rfl

theorem cell23_4683701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 8].length) (baseStart_4683701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683701 prefixEnd_4683701 := by exact prefixLift 4683701
  have htrace : WordTrace (prefixWord ++ tailWord_4683701) baseStart_4683701 baseEnd_4683701 := by
    simpa [prefixWord, tailWord_4683701, baseEnd_4683701] using wordTrace_append hprefix tailTrace_4683701
  have hstable : (prefixWord ++ tailWord_4683701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683701).length < 2 ^ (prefixWord ++ tailWord_4683701).sum := by decide
  have hdescent : baseEnd_4683701 < baseStart_4683701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683745 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_4683745 : Nat := 118140960795 + 4683745 * 2 ^ 59
def prefixEnd_4683745 : Nat := 4983230072969 + 3 ^ 40 * 4683745 * 2
def baseEnd_4683745 : Nat := 2405012448092882559847355

theorem tailTrace_4683745 : CollatzResearch.WordTrace tailWord_4683745 prefixEnd_4683745 2405012448092882559847355 := by
  unfold tailWord_4683745
  simp only [CollatzResearch.WordTrace]
  refine ⟨170830214416599259806228689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113886809611066173204152459 170830214416599259806228689)
  ·
    refine ⟨128122660812449444854671517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170830214416599259806228689 128122660812449444854671517)
    ·
      refine ⟨48045997804668541820501819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128122660812449444854671517 48045997804668541820501819)
      ·
        refine ⟨72068996707002812730752729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48045997804668541820501819 72068996707002812730752729)
        ·
          refine ⟨54051747530252109548064547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72068996707002812730752729 54051747530252109548064547)
          ·
            refine ⟨81077621295378164322096821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54051747530252109548064547 81077621295378164322096821)
            ·
              refine ⟨7601026996441702905196577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81077621295378164322096821 7601026996441702905196577)
              ·
                refine ⟨5700770247331277178897433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7601026996441702905196577 5700770247331277178897433)
                ·
                  refine ⟨4275577685498457884173075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5700770247331277178897433 4275577685498457884173075)
                  ·
                    refine ⟨6413366528247686826259613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4275577685498457884173075 6413366528247686826259613)
                    ·
                      refine ⟨2405012448092882559847355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6413366528247686826259613 2405012448092882559847355)
                      ·
                        rfl

theorem cell23_4683745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_4683745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683745 prefixEnd_4683745 := by exact prefixLift 4683745
  have htrace : WordTrace (prefixWord ++ tailWord_4683745) baseStart_4683745 baseEnd_4683745 := by
    simpa [prefixWord, tailWord_4683745, baseEnd_4683745] using wordTrace_append hprefix tailTrace_4683745
  have hstable : (prefixWord ++ tailWord_4683745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683745).length < 2 ^ (prefixWord ++ tailWord_4683745).sum := by decide
  have hdescent : baseEnd_4683745 < baseStart_4683745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683771 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 3]
def baseStart_4683771 : Nat := 118140960795 + 4683771 * 2 ^ 59
def prefixEnd_4683771 : Nat := 4983230072969 + 3 ^ 40 * 4683771 * 2
def baseEnd_4683771 : Nat := 2405025798589899458122235

theorem tailTrace_4683771 : CollatzResearch.WordTrace tailWord_4683771 prefixEnd_4683771 2405025798589899458122235 := by
  unfold tailWord_4683771
  simp only [CollatzResearch.WordTrace]
  refine ⟨170831162714505066246675167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113887441809670044164450111 170831162714505066246675167)
  ·
    refine ⟨256246744071757599370012751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170831162714505066246675167 256246744071757599370012751)
    ·
      refine ⟨384370116107636399055019127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256246744071757599370012751 384370116107636399055019127)
      ·
        refine ⟨576555174161454598582528691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384370116107636399055019127 576555174161454598582528691)
        ·
          refine ⟨864832761242181897873793037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576555174161454598582528691 864832761242181897873793037)
          ·
            refine ⟨324312285465818211702672389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 864832761242181897873793037 324312285465818211702672389)
            ·
              refine ⟨60808553524840914694251073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 324312285465818211702672389 60808553524840914694251073)
              ·
                refine ⟨45606415143630686020688305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60808553524840914694251073 45606415143630686020688305)
                ·
                  refine ⟨34204811357723014515516229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45606415143630686020688305 34204811357723014515516229)
                  ·
                    refine ⟨6413402129573065221659293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34204811357723014515516229 6413402129573065221659293)
                    ·
                      refine ⟨2405025798589899458122235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6413402129573065221659293 2405025798589899458122235)
                      ·
                        rfl

theorem cell23_4683771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 3].length) (baseStart_4683771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683771 prefixEnd_4683771 := by exact prefixLift 4683771
  have htrace : WordTrace (prefixWord ++ tailWord_4683771) baseStart_4683771 baseEnd_4683771 := by
    simpa [prefixWord, tailWord_4683771, baseEnd_4683771] using wordTrace_append hprefix tailTrace_4683771
  have hstable : (prefixWord ++ tailWord_4683771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683771).length < 2 ^ (prefixWord ++ tailWord_4683771).sum := by decide
  have hdescent : baseEnd_4683771 < baseStart_4683771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683871 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_4683871 : Nat := 118140960795 + 4683871 * 2 ^ 59
def prefixEnd_4683871 : Nat := 4983230072969 + 3 ^ 40 * 4683871 * 2
def baseEnd_4683871 : Nat := 2405077146655349066871775

theorem tailTrace_4683871 : CollatzResearch.WordTrace tailWord_4683871 prefixEnd_4683871 2405077146655349066871775 := by
  unfold tailWord_4683871
  simp only [CollatzResearch.WordTrace]
  refine ⟨170834810014142783325315467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113889873342761855550210311 170834810014142783325315467)
  ·
    refine ⟨256252215021214174987973201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170834810014142783325315467 256252215021214174987973201)
    ·
      refine ⟨192189161265910631240979901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256252215021214174987973201 192189161265910631240979901)
      ·
        refine ⟨72070935474716486715367463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192189161265910631240979901 72070935474716486715367463)
        ·
          refine ⟨108106403212074730073051195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72070935474716486715367463 108106403212074730073051195)
          ·
            refine ⟨162159604818112095109576793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108106403212074730073051195 162159604818112095109576793)
            ·
              refine ⟨121619703613584071332182595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162159604818112095109576793 121619703613584071332182595)
              ·
                refine ⟨182429555420376106998273893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121619703613584071332182595 182429555420376106998273893)
                ·
                  refine ⟨34205541641320520062176355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182429555420376106998273893 34205541641320520062176355)
                  ·
                    refine ⟨51308312461980780093264533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34205541641320520062176355 51308312461980780093264533)
                    ·
                      refine ⟨2405077146655349066871775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51308312461980780093264533 2405077146655349066871775)
                      ·
                        rfl

theorem cell23_4683871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_4683871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683871 prefixEnd_4683871 := by exact prefixLift 4683871
  have htrace : WordTrace (prefixWord ++ tailWord_4683871) baseStart_4683871 baseEnd_4683871 := by
    simpa [prefixWord, tailWord_4683871, baseEnd_4683871] using wordTrace_append hprefix tailTrace_4683871
  have hstable : (prefixWord ++ tailWord_4683871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683871).length < 2 ^ (prefixWord ++ tailWord_4683871).sum := by decide
  have hdescent : baseEnd_4683871 < baseStart_4683871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683885 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_4683885 : Nat := 118140960795 + 4683885 * 2 ^ 59
def prefixEnd_4683885 : Nat := 4983230072969 + 3 ^ 40 * 4683885 * 2
def baseEnd_4683885 : Nat := 801694778461504004032237

theorem tailTrace_4683885 : CollatzResearch.WordTrace tailWord_4683885 prefixEnd_4683885 801694778461504004032237 := by
  unfold tailWord_4683885
  simp only [CollatzResearch.WordTrace]
  refine ⟨170835320636092063716325109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113890213757394709144216739 170835320636092063716325109)
  ·
    refine ⟨16015811309633630973405479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170835320636092063716325109 16015811309633630973405479)
    ·
      refine ⟨24023716964450446460108219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16015811309633630973405479 24023716964450446460108219)
      ·
        refine ⟨36035575446675669690162329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24023716964450446460108219 36035575446675669690162329)
        ·
          refine ⟨27026681585006752267621747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36035575446675669690162329 27026681585006752267621747)
          ·
            refine ⟨40540022377510128401432621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27026681585006752267621747 40540022377510128401432621)
            ·
              refine ⟨15202508391566298150537233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40540022377510128401432621 15202508391566298150537233)
              ·
                refine ⟨11401881293674723612902925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15202508391566298150537233 11401881293674723612902925)
                ·
                  refine ⟨4275705485128021354838597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11401881293674723612902925 4275705485128021354838597)
                  ·
                    refine ⟨801694778461504004032237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4275705485128021354838597 801694778461504004032237)
                    ·
                      rfl

theorem cell23_4683885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_4683885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683885 prefixEnd_4683885 := by exact prefixLift 4683885
  have htrace : WordTrace (prefixWord ++ tailWord_4683885) baseStart_4683885 baseEnd_4683885 := by
    simpa [prefixWord, tailWord_4683885, baseEnd_4683885] using wordTrace_append hprefix tailTrace_4683885
  have hstable : (prefixWord ++ tailWord_4683885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683885).length < 2 ^ (prefixWord ++ tailWord_4683885).sum := by decide
  have hdescent : baseEnd_4683885 < baseStart_4683885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683895 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_4683895 : Nat := 118140960795 + 4683895 * 2 ^ 59
def prefixEnd_4683895 : Nat := 4983230072969 + 3 ^ 40 * 4683895 * 2
def baseEnd_4683895 : Nat := 2405089470191056972971665

theorem tailTrace_4683895 : CollatzResearch.WordTrace tailWord_4683895 prefixEnd_4683895 2405089470191056972971665 := by
  unfold tailWord_4683895
  simp only [CollatzResearch.WordTrace]
  refine ⟨170835685366055835424189139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113890456910703890282792759 170835685366055835424189139)
  ·
    refine ⟨256253528049083753136283709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170835685366055835424189139 256253528049083753136283709)
    ·
      refine ⟨96095073018406407426106391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256253528049083753136283709 96095073018406407426106391)
      ·
        refine ⟨144142609527609611139159587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96095073018406407426106391 144142609527609611139159587)
        ·
          refine ⟨216213914291414416708739381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144142609527609611139159587 216213914291414416708739381)
          ·
            refine ⟨20270054464820101566444317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 216213914291414416708739381 20270054464820101566444317)
            ·
              refine ⟨7601270424307538087416619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20270054464820101566444317 7601270424307538087416619)
              ·
                refine ⟨11401905636461307131124929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7601270424307538087416619 11401905636461307131124929)
                ·
                  refine ⟨8551429227345980348343697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11401905636461307131124929 8551429227345980348343697)
                  ·
                    refine ⟨6413571920509485261257773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8551429227345980348343697 6413571920509485261257773)
                    ·
                      refine ⟨2405089470191056972971665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6413571920509485261257773 2405089470191056972971665)
                      ·
                        rfl

theorem cell23_4683895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_4683895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683895 prefixEnd_4683895 := by exact prefixLift 4683895
  have htrace : WordTrace (prefixWord ++ tailWord_4683895) baseStart_4683895 baseEnd_4683895 := by
    simpa [prefixWord, tailWord_4683895, baseEnd_4683895] using wordTrace_append hprefix tailTrace_4683895
  have hstable : (prefixWord ++ tailWord_4683895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683895).length < 2 ^ (prefixWord ++ tailWord_4683895).sum := by decide
  have hdescent : baseEnd_4683895 < baseStart_4683895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683948 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_4683948 : Nat := 118140960795 + 4683948 * 2 ^ 59
def prefixEnd_4683948 : Nat := 4983230072969 + 3 ^ 40 * 4683948 * 2
def baseEnd_4683948 : Nat := 2405116684665745265608921

theorem tailTrace_4683948 : CollatzResearch.WordTrace tailWord_4683948 prefixEnd_4683948 2405116684665745265608921 := by
  unfold tailWord_4683948
  simp only [CollatzResearch.WordTrace]
  refine ⟨85418809217431912737934249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113891745623242550317245665 85418809217431912737934249)
  ·
    refine ⟨64064106913073934553450687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85418809217431912737934249 64064106913073934553450687)
    ·
      refine ⟨96096160369610901830176031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64064106913073934553450687 96096160369610901830176031)
      ·
        refine ⟨144144240554416352745264047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96096160369610901830176031 144144240554416352745264047)
        ·
          refine ⟨216216360831624529117896071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144144240554416352745264047 216216360831624529117896071)
          ·
            refine ⟨324324541247436793676844107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216216360831624529117896071 324324541247436793676844107)
            ·
              refine ⟨486486811871155190515266161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324324541247436793676844107 486486811871155190515266161)
              ·
                refine ⟨364865108903366392886449621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486486811871155190515266161 364865108903366392886449621)
                ·
                  refine ⟨8551525989922649833276163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 364865108903366392886449621 8551525989922649833276163)
                  ·
                    refine ⟨12827288984883974749914245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8551525989922649833276163 12827288984883974749914245)
                    ·
                      refine ⟨2405116684665745265608921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12827288984883974749914245 2405116684665745265608921)
                      ·
                        rfl

theorem cell23_4683948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_4683948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683948 prefixEnd_4683948 := by exact prefixLift 4683948
  have htrace : WordTrace (prefixWord ++ tailWord_4683948) baseStart_4683948 baseEnd_4683948 := by
    simpa [prefixWord, tailWord_4683948, baseEnd_4683948] using wordTrace_append hprefix tailTrace_4683948
  have hstable : (prefixWord ++ tailWord_4683948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683948).length < 2 ^ (prefixWord ++ tailWord_4683948).sum := by decide
  have hdescent : baseEnd_4683948 < baseStart_4683948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683959 : List Nat := [1, 1, 3, 1, 4, 2, 3, 3, 1, 1, 3]
def baseStart_4683959 : Nat := 118140960795 + 4683959 * 2 ^ 59
def prefixEnd_4683959 : Nat := 4983230072969 + 3 ^ 40 * 4683959 * 2
def baseEnd_4683959 : Nat := 2405122332952944722571371

theorem tailTrace_4683959 : CollatzResearch.WordTrace tailWord_4683959 prefixEnd_4683959 2405122332952944722571371 := by
  unfold tailWord_4683959
  simp only [CollatzResearch.WordTrace]
  refine ⟨170838019637823974354518931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113892013091882649569679287 170838019637823974354518931)
  ·
    refine ⟨256257029456735961531778397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170838019637823974354518931 256257029456735961531778397)
    ·
      refine ⟨96096386046275985574416899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256257029456735961531778397 96096386046275985574416899)
      ·
        refine ⟨144144579069413978361625349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96096386046275985574416899 144144579069413978361625349)
        ·
          refine ⟨27027108575515120942804753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144144579069413978361625349 27027108575515120942804753)
          ·
            refine ⟨20270331431636340707103565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27027108575515120942804753 20270331431636340707103565)
            ·
              refine ⟨7601374286863627765163837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20270331431636340707103565 7601374286863627765163837)
              ·
                refine ⟨2850515357573860411936439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7601374286863627765163837 2850515357573860411936439)
                ·
                  refine ⟨4275773036360790617904659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850515357573860411936439 4275773036360790617904659)
                  ·
                    refine ⟨6413659554541185926856989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4275773036360790617904659 6413659554541185926856989)
                    ·
                      refine ⟨2405122332952944722571371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6413659554541185926856989 2405122332952944722571371)
                      ·
                        rfl

theorem cell23_4683959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_4683959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683959 prefixEnd_4683959 := by exact prefixLift 4683959
  have htrace : WordTrace (prefixWord ++ tailWord_4683959) baseStart_4683959 baseEnd_4683959 := by
    simpa [prefixWord, tailWord_4683959, baseEnd_4683959] using wordTrace_append hprefix tailTrace_4683959
  have hstable : (prefixWord ++ tailWord_4683959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683959).length < 2 ^ (prefixWord ++ tailWord_4683959).sum := by decide
  have hdescent : baseEnd_4683959 < baseStart_4683959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683978 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_4683978 : Nat := 118140960795 + 4683978 * 2 ^ 59
def prefixEnd_4683978 : Nat := 4983230072969 + 3 ^ 40 * 4683978 * 2
def baseEnd_4683978 : Nat := 2405132089085380148233783

theorem tailTrace_4683978 : CollatzResearch.WordTrace tailWord_4683978 prefixEnd_4683978 2405132089085380148233783 := by
  unfold tailWord_4683978
  simp only [CollatzResearch.WordTrace]
  refine ⟨42709678156188785149865147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113892475083170093732973725 42709678156188785149865147)
  ·
    refine ⟨64064517234283177724797721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42709678156188785149865147 64064517234283177724797721)
    ·
      refine ⟨48048387925712383293598291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64064517234283177724797721 48048387925712383293598291)
      ·
        refine ⟨72072581888568574940397437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48048387925712383293598291 72072581888568574940397437)
        ·
          refine ⟨27027218208213215602649039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72072581888568574940397437 27027218208213215602649039)
          ·
            refine ⟨40540827312319823403973559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27027218208213215602649039 40540827312319823403973559)
            ·
              refine ⟨60811240968479735105960339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40540827312319823403973559 60811240968479735105960339)
              ·
                refine ⟨91216861452719602658940509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60811240968479735105960339 91216861452719602658940509)
                ·
                  refine ⟨34206323044769850997102691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91216861452719602658940509 34206323044769850997102691)
                  ·
                    refine ⟨51309484567154776495654037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34206323044769850997102691 51309484567154776495654037)
                    ·
                      refine ⟨2405132089085380148233783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51309484567154776495654037 2405132089085380148233783)
                      ·
                        rfl

theorem cell23_4683978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_4683978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683978 prefixEnd_4683978 := by exact prefixLift 4683978
  have htrace : WordTrace (prefixWord ++ tailWord_4683978) baseStart_4683978 baseEnd_4683978 := by
    simpa [prefixWord, tailWord_4683978, baseEnd_4683978] using wordTrace_append hprefix tailTrace_4683978
  have hstable : (prefixWord ++ tailWord_4683978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683978).length < 2 ^ (prefixWord ++ tailWord_4683978).sum := by decide
  have hdescent : baseEnd_4683978 < baseStart_4683978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683992 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 2, 4]
def baseStart_4683992 : Nat := 118140960795 + 4683992 * 2 ^ 59
def prefixEnd_4683992 : Nat := 4983230072969 + 3 ^ 40 * 4683992 * 2
def baseEnd_4683992 : Nat := 801713092604847697819573

theorem tailTrace_4683992 : CollatzResearch.WordTrace tailWord_4683992 prefixEnd_4683992 801713092604847697819573 := by
  unfold tailWord_4683992
  simp only [CollatzResearch.WordTrace]
  refine ⟨85419611623352210495235115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113892815497802947326980153 85419611623352210495235115)
  ·
    refine ⟨128129417435028315742852673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85419611623352210495235115 128129417435028315742852673)
    ·
      refine ⟨96097063076271236807139505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128129417435028315742852673 96097063076271236807139505)
      ·
        refine ⟨72072797307203427605354629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96097063076271236807139505 72072797307203427605354629)
        ·
          refine ⟨13513649495100642676003993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72072797307203427605354629 13513649495100642676003993)
          ·
            refine ⟨10135237121325482007002995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13513649495100642676003993 10135237121325482007002995)
            ·
              refine ⟨15202855681988223010504493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10135237121325482007002995 15202855681988223010504493)
              ·
                refine ⟨5701070880745583628939185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15202855681988223010504493 5701070880745583628939185)
                ·
                  refine ⟨4275803160559187721704389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5701070880745583628939185 4275803160559187721704389)
                  ·
                    refine ⟨801713092604847697819573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4275803160559187721704389 801713092604847697819573)
                    ·
                      rfl

theorem cell23_4683992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_4683992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683992 prefixEnd_4683992 := by exact prefixLift 4683992
  have htrace : WordTrace (prefixWord ++ tailWord_4683992) baseStart_4683992 baseEnd_4683992 := by
    simpa [prefixWord, tailWord_4683992, baseEnd_4683992] using wordTrace_append hprefix tailTrace_4683992
  have hstable : (prefixWord ++ tailWord_4683992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683992).length < 2 ^ (prefixWord ++ tailWord_4683992).sum := by decide
  have hdescent : baseEnd_4683992 < baseStart_4683992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4683996 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4683996 : Nat := 118140960795 + 4683996 * 2 ^ 59
def prefixEnd_4683996 : Nat := 4983230072969 + 3 ^ 40 * 4683996 * 2
def baseEnd_4683996 : Nat := 801713777245720359269567

theorem tailTrace_4683996 : CollatzResearch.WordTrace tailWord_4683996 prefixEnd_4683996 801713777245720359269567 := by
  unfold tailWord_4683996
  simp only [CollatzResearch.WordTrace]
  refine ⟨85419684569344964836807921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113892912759126619782410561 85419684569344964836807921)
  ·
    refine ⟨64064763427008723627605941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85419684569344964836807921 64064763427008723627605941)
    ·
      refine ⟨6006071571282067840088057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64064763427008723627605941 6006071571282067840088057)
      ·
        refine ⟨4504553678461550880066043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6006071571282067840088057 4504553678461550880066043)
        ·
          refine ⟨6756830517692326320099065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4504553678461550880066043 6756830517692326320099065)
          ·
            refine ⟨5067622888269244740074299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6756830517692326320099065 5067622888269244740074299)
            ·
              refine ⟨7601434332403867110111449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5067622888269244740074299 7601434332403867110111449)
              ·
                refine ⟨5701075749302900332583587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7601434332403867110111449 5701075749302900332583587)
                ·
                  refine ⟨8551613623954350498875381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5701075749302900332583587 8551613623954350498875381)
                  ·
                    refine ⟨801713777245720359269567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8551613623954350498875381 801713777245720359269567)
                    ·
                      rfl

theorem cell23_4683996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4683996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4683996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4683996 prefixEnd_4683996 := by exact prefixLift 4683996
  have htrace : WordTrace (prefixWord ++ tailWord_4683996) baseStart_4683996 baseEnd_4683996 := by
    simpa [prefixWord, tailWord_4683996, baseEnd_4683996] using wordTrace_append hprefix tailTrace_4683996
  have hstable : (prefixWord ++ tailWord_4683996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4683996).length < 2 ^ (prefixWord ++ tailWord_4683996).sum := by decide
  have hdescent : baseEnd_4683996 < baseStart_4683996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4683996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684015 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 3]
def baseStart_4684015 : Nat := 118140960795 + 4684015 * 2 ^ 59
def prefixEnd_4684015 : Nat := 4983230072969 + 3 ^ 40 * 4684015 * 2
def baseEnd_4684015 : Nat := 2405151087869596503471113

theorem tailTrace_4684015 : CollatzResearch.WordTrace tailWord_4684015 prefixEnd_4684015 2405151087869596503471113 := by
  unfold tailWord_4684015
  simp only [CollatzResearch.WordTrace]
  refine ⟨170840062125621095918557499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113893374750414063945704999 170840062125621095918557499)
  ·
    refine ⟨256260093188431643877836249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170840062125621095918557499 256260093188431643877836249)
    ·
      refine ⟨192195069891323732908377187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256260093188431643877836249 192195069891323732908377187)
      ·
        refine ⟨288292604836985599362565781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192195069891323732908377187 288292604836985599362565781)
        ·
          refine ⟨13513715851733699970120271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 288292604836985599362565781 13513715851733699970120271)
          ·
            refine ⟨20270573777600549955180407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13513715851733699970120271 20270573777600549955180407)
            ·
              refine ⟨30405860666400824932770611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20270573777600549955180407 30405860666400824932770611)
              ·
                refine ⟨45608790999601237399155917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30405860666400824932770611 45608790999601237399155917)
                ·
                  refine ⟨17103296624850464024683469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45608790999601237399155917 17103296624850464024683469)
                  ·
                    refine ⟨6413736234318924009256301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17103296624850464024683469 6413736234318924009256301)
                    ·
                      refine ⟨2405151087869596503471113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6413736234318924009256301 2405151087869596503471113)
                      ·
                        rfl

theorem cell23_4684015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_4684015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684015 prefixEnd_4684015 := by exact prefixLift 4684015
  have htrace : WordTrace (prefixWord ++ tailWord_4684015) baseStart_4684015 baseEnd_4684015 := by
    simpa [prefixWord, tailWord_4684015, baseEnd_4684015] using wordTrace_append hprefix tailTrace_4684015
  have hstable : (prefixWord ++ tailWord_4684015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684015).length < 2 ^ (prefixWord ++ tailWord_4684015).sum := by decide
  have hdescent : baseEnd_4684015 < baseStart_4684015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684032 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 2, 1, 3]
def baseStart_4684032 : Nat := 118140960795 + 4684032 * 2 ^ 59
def prefixEnd_4684032 : Nat := 4983230072969 + 3 ^ 40 * 4684032 * 2
def baseEnd_4684032 : Nat := 2405159817040722936958535

theorem tailTrace_4684032 : CollatzResearch.WordTrace tailWord_4684032 prefixEnd_4684032 2405159817040722936958535 := by
  unfold tailWord_4684032
  simp only [CollatzResearch.WordTrace]
  refine ⟨85420341083279753910963175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113893788111039671881284233 85420341083279753910963175)
  ·
    refine ⟨128130511624919630866444763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85420341083279753910963175 128130511624919630866444763)
    ·
      refine ⟨192195767437379446299667145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128130511624919630866444763 192195767437379446299667145)
      ·
        refine ⟨144146825578034584724750359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192195767437379446299667145 144146825578034584724750359)
        ·
          refine ⟨216220238367051877087125539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144146825578034584724750359 216220238367051877087125539)
          ·
            refine ⟨324330357550577815630688309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216220238367051877087125539 324330357550577815630688309)
            ·
              refine ⟨30405971020366670215377029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324330357550577815630688309 30405971020366670215377029)
              ·
                refine ⟨5701119566318750665383193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30405971020366670215377029 5701119566318750665383193)
                ·
                  refine ⟨4275839674739062999037395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5701119566318750665383193 4275839674739062999037395)
                  ·
                    refine ⟨6413759512108594498556093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4275839674739062999037395 6413759512108594498556093)
                    ·
                      refine ⟨2405159817040722936958535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6413759512108594498556093 2405159817040722936958535)
                      ·
                        rfl

theorem cell23_4684032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_4684032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684032 prefixEnd_4684032 := by exact prefixLift 4684032
  have htrace : WordTrace (prefixWord ++ tailWord_4684032) baseStart_4684032 baseEnd_4684032 := by
    simpa [prefixWord, tailWord_4684032, baseEnd_4684032] using wordTrace_append hprefix tailTrace_4684032
  have hstable : (prefixWord ++ tailWord_4684032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684032).length < 2 ^ (prefixWord ++ tailWord_4684032).sum := by decide
  have hdescent : baseEnd_4684032 < baseStart_4684032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684039 : List Nat := [1, 1, 4, 5, 2, 1, 1, 8]
def baseStart_4684039 : Nat := 118140960795 + 4684039 * 2 ^ 59
def prefixEnd_4684039 : Nat := 4983230072969 + 3 ^ 40 * 4684039 * 2
def baseEnd_4684039 : Nat := 89080126348344607761889

theorem tailTrace_4684039 : CollatzResearch.WordTrace tailWord_4684039 prefixEnd_4684039 89080126348344607761889 := by
  unfold tailWord_4684039
  simp only [CollatzResearch.WordTrace]
  refine ⟨170840937477534148017431171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113893958318356098678287447 170840937477534148017431171)
  ·
    refine ⟨256261406216301222026146757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170840937477534148017431171 256261406216301222026146757)
    ·
      refine ⟨48049013665556479129902517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256261406216301222026146757 48049013665556479129902517)
      ·
        refine ⟨4504595031145919918428361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48049013665556479129902517 4504595031145919918428361)
        ·
          refine ⟨3378446273359439938821271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4504595031145919918428361 3378446273359439938821271)
          ·
            refine ⟨5067669410039159908231907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378446273359439938821271 5067669410039159908231907)
            ·
              refine ⟨7601504115058739862347861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5067669410039159908231907 7601504115058739862347861)
              ·
                refine ⟨89080126348344607761889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7601504115058739862347861 89080126348344607761889)
                ·
                  rfl

theorem cell23_4684039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 8].length) (baseStart_4684039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684039 prefixEnd_4684039 := by exact prefixLift 4684039
  have htrace : WordTrace (prefixWord ++ tailWord_4684039) baseStart_4684039 baseEnd_4684039 := by
    simpa [prefixWord, tailWord_4684039, baseEnd_4684039] using wordTrace_append hprefix tailTrace_4684039
  have hstable : (prefixWord ++ tailWord_4684039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684039).length < 2 ^ (prefixWord ++ tailWord_4684039).sum := by decide
  have hdescent : baseEnd_4684039 < baseStart_4684039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684042 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_4684042 : Nat := 118140960795 + 4684042 * 2 ^ 59
def prefixEnd_4684042 : Nat := 4983230072969 + 3 ^ 40 * 4684042 * 2
def baseEnd_4684042 : Nat := 2405164951847267897833489

theorem tailTrace_4684042 : CollatzResearch.WordTrace tailWord_4684042 prefixEnd_4684042 2405164951847267897833489 := by
  unfold tailWord_4684042
  simp only [CollatzResearch.WordTrace]
  refine ⟨42710261724130819882447595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113894031264348853019860253 42710261724130819882447595)
  ·
    refine ⟨64065392586196229823671393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42710261724130819882447595 64065392586196229823671393)
    ·
      refine ⟨48049044439647172367753545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64065392586196229823671393 48049044439647172367753545)
      ·
        refine ⟨36036783329735379275815159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48049044439647172367753545 36036783329735379275815159)
        ·
          refine ⟨54055174994603068913722739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36036783329735379275815159 54055174994603068913722739)
          ·
            refine ⟨81082762491904603370584109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54055174994603068913722739 81082762491904603370584109)
            ·
              refine ⟨30406035934464226263969041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81082762491904603370584109 30406035934464226263969041)
              ·
                refine ⟨22804526950848169697976781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30406035934464226263969041 22804526950848169697976781)
                ·
                  refine ⟨8551697606568063636741293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22804526950848169697976781 8551697606568063636741293)
                  ·
                    refine ⟨3206886602463023863777985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8551697606568063636741293 3206886602463023863777985)
                    ·
                      refine ⟨2405164951847267897833489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3206886602463023863777985 2405164951847267897833489)
                      ·
                        rfl

theorem cell23_4684042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_4684042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684042 prefixEnd_4684042 := by exact prefixLift 4684042
  have htrace : WordTrace (prefixWord ++ tailWord_4684042) baseStart_4684042 baseEnd_4684042 := by
    simpa [prefixWord, tailWord_4684042, baseEnd_4684042] using wordTrace_append hprefix tailTrace_4684042
  have hstable : (prefixWord ++ tailWord_4684042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684042).length < 2 ^ (prefixWord ++ tailWord_4684042).sum := by decide
  have hdescent : baseEnd_4684042 < baseStart_4684042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4684085 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4684085 : Nat := 118140960795 + 4684085 * 2 ^ 59
def prefixEnd_4684085 : Nat := 4983230072969 + 3 ^ 40 * 4684085 * 2
def baseEnd_4684085 : Nat := 2405187031515411229595791

theorem tailTrace_4684085 : CollatzResearch.WordTrace tailWord_4684085 prefixEnd_4684085 2405187031515411229595791 := by
  unfold tailWord_4684085
  simp only [CollatzResearch.WordTrace]
  refine ⟨170842615235367497873605709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113895076823578331915737139 170842615235367497873605709)
  ·
    refine ⟨64065980713262811702602141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170842615235367497873605709 64065980713262811702602141)
    ·
      refine ⟨24024742767473554388475803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64065980713262811702602141 24024742767473554388475803)
      ·
        refine ⟨36037114151210331582713705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24024742767473554388475803 36037114151210331582713705)
        ·
          refine ⟨27027835613407748687035279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36037114151210331582713705 27027835613407748687035279)
          ·
            refine ⟨40541753420111623030552919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27027835613407748687035279 40541753420111623030552919)
            ·
              refine ⟨60812630130167434545829379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40541753420111623030552919 60812630130167434545829379)
              ·
                refine ⟨91218945195251151818744069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60812630130167434545829379 91218945195251151818744069)
                ·
                  refine ⟨17103552224109590966014513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91218945195251151818744069 17103552224109590966014513)
                  ·
                    refine ⟨12827664168082193224510885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17103552224109590966014513 12827664168082193224510885)
                    ·
                      refine ⟨2405187031515411229595791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12827664168082193224510885 2405187031515411229595791)
                      ·
                        rfl

theorem cell23_4684085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4684085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4684085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4684085 prefixEnd_4684085 := by exact prefixLift 4684085
  have htrace : WordTrace (prefixWord ++ tailWord_4684085) baseStart_4684085 baseEnd_4684085 := by
    simpa [prefixWord, tailWord_4684085, baseEnd_4684085] using wordTrace_append hprefix tailTrace_4684085
  have hstable : (prefixWord ++ tailWord_4684085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4684085).length < 2 ^ (prefixWord ++ tailWord_4684085).sum := by decide
  have hdescent : baseEnd_4684085 < baseStart_4684085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4684085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
