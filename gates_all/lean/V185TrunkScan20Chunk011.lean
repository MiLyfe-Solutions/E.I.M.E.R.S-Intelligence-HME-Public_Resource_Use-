import V185TrunkScan20Chunk010

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_67565 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 4]
def baseStart_67565 : Nat := 118140960795 + 67565 * 2 ^ 59
def prefixEnd_67565 : Nat := 4983230072969 + 3 ^ 40 * 67565 * 2
def baseEnd_67565 : Nat := 30838507041007453623805

theorem tailTrace_67565 : CollatzResearch.WordTrace tailWord_67565 prefixEnd_67565 30838507041007453623805 := by
  unfold tailWord_67565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464298000231019028428149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1642865333487346018952099 2464298000231019028428149)
  ·
    refine ⟨231027937521658033915139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2464298000231019028428149 231027937521658033915139)
    ·
      refine ⟨346541906282487050872709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231027937521658033915139 346541906282487050872709)
      ·
        refine ⟨64976607427966322038633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346541906282487050872709 64976607427966322038633)
        ·
          refine ⟨48732455570974741528975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64976607427966322038633 48732455570974741528975)
          ·
            refine ⟨73098683356462112293463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48732455570974741528975 73098683356462112293463)
            ·
              refine ⟨109648025034693168440195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73098683356462112293463 109648025034693168440195)
              ·
                refine ⟨164472037552039752660293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109648025034693168440195 164472037552039752660293)
                ·
                  refine ⟨30838507041007453623805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164472037552039752660293 30838507041007453623805)
                  ·
                    rfl

theorem cell20_67565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_67565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67565 prefixEnd_67565 := by exact prefixLift 67565
  have htrace : WordTrace (prefixWord ++ tailWord_67565) baseStart_67565 baseEnd_67565 := by
    simpa [prefixWord, tailWord_67565, baseEnd_67565] using wordTrace_append hprefix tailTrace_67565
  have hstable : (prefixWord ++ tailWord_67565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67565).length < 2 ^ (prefixWord ++ tailWord_67565).sum := by decide
  have hdescent : baseEnd_67565 < baseStart_67565 := by decide
  rcases family_descends (prefixWord ++ tailWord_67565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67569 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 4]
def baseStart_67569 : Nat := 118140960795 + 67569 * 2 ^ 59
def prefixEnd_67569 : Nat := 4983230072969 + 3 ^ 40 * 67569 * 2
def baseEnd_67569 : Nat := 30840332750001217490455

theorem tailTrace_67569 : CollatzResearch.WordTrace tailWord_67569 prefixEnd_67569 30840332750001217490455 := by
  unfold tailWord_67569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464443892216527711573761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1642962594811018474382507 2464443892216527711573761)
  ·
    refine ⟨1848332919162395783680321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2464443892216527711573761 1848332919162395783680321)
    ·
      refine ⟨1386249689371796837760241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1848332919162395783680321 1386249689371796837760241)
      ·
        refine ⟨1039687267028847628320181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1386249689371796837760241 1039687267028847628320181)
        ·
          refine ⟨97470681283954465155017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1039687267028847628320181 97470681283954465155017)
          ·
            refine ⟨73103010962965848866263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97470681283954465155017 73103010962965848866263)
            ·
              refine ⟨109654516444448773299395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73103010962965848866263 109654516444448773299395)
              ·
                refine ⟨164481774666673159949093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109654516444448773299395 164481774666673159949093)
                ·
                  refine ⟨30840332750001217490455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164481774666673159949093 30840332750001217490455)
                  ·
                    rfl

theorem cell20_67569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_67569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67569 prefixEnd_67569 := by exact prefixLift 67569
  have htrace : WordTrace (prefixWord ++ tailWord_67569) baseStart_67569 baseEnd_67569 := by
    simpa [prefixWord, tailWord_67569, baseEnd_67569] using wordTrace_append hprefix tailTrace_67569
  have hstable : (prefixWord ++ tailWord_67569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67569).length < 2 ^ (prefixWord ++ tailWord_67569).sum := by decide
  have hdescent : baseEnd_67569 < baseStart_67569 := by decide
  rcases family_descends (prefixWord ++ tailWord_67569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67620 : List Nat := [2, 3, 1, 4, 3, 1, 2, 2, 2]
def baseStart_67620 : Nat := 118140960795 + 67620 * 2 ^ 59
def prefixEnd_67620 : Nat := 4983230072969 + 3 ^ 40 * 67620 * 2
def baseEnd_67620 : Nat := 30863610539671706790247

theorem tailTrace_67620 : CollatzResearch.WordTrace tailWord_67620 prefixEnd_67620 30863610539671706790247 := by
  unfold tailWord_67620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233152007515881710840157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1644202676687842281120209 1233152007515881710840157)
  ·
    refine ⟨462432002818455641565059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1233152007515881710840157 462432002818455641565059)
    ·
      refine ⟨693648004227683462347589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462432002818455641565059 693648004227683462347589)
      ·
        refine ⟨130059000792690649190173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 693648004227683462347589 130059000792690649190173)
        ·
          refine ⟨48772125297258993446315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130059000792690649190173 48772125297258993446315)
          ·
            refine ⟨73158187945888490169473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48772125297258993446315 73158187945888490169473)
            ·
              refine ⟨54868640959416367627105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73158187945888490169473 54868640959416367627105)
              ·
                refine ⟨41151480719562275720329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54868640959416367627105 41151480719562275720329)
                ·
                  refine ⟨30863610539671706790247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41151480719562275720329 30863610539671706790247)
                  ·
                    rfl

theorem cell20_67620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_67620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67620 prefixEnd_67620 := by exact prefixLift 67620
  have htrace : WordTrace (prefixWord ++ tailWord_67620) baseStart_67620 baseEnd_67620 := by
    simpa [prefixWord, tailWord_67620, baseEnd_67620] using wordTrace_append hprefix tailTrace_67620
  have hstable : (prefixWord ++ tailWord_67620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67620).length < 2 ^ (prefixWord ++ tailWord_67620).sum := by decide
  have hdescent : baseEnd_67620 < baseStart_67620 := by decide
  rcases family_descends (prefixWord ++ tailWord_67620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67621 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 3]
def baseStart_67621 : Nat := 118140960795 + 67621 * 2 ^ 59
def prefixEnd_67621 : Nat := 4983230072969 + 3 ^ 40 * 67621 * 2
def baseEnd_67621 : Nat := 30864066966920147756909

theorem tailTrace_67621 : CollatzResearch.WordTrace tailWord_67621 prefixEnd_67621 30864066966920147756909 := by
  unfold tailWord_67621
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466340488028140592466717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1644226992018760394977811 2466340488028140592466717)
  ·
    refine ⟨924877683010552722175019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2466340488028140592466717 924877683010552722175019)
    ·
      refine ⟨1387316524515829083262529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924877683010552722175019 1387316524515829083262529)
      ·
        refine ⟨1040487393386871812446897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1387316524515829083262529 1040487393386871812446897)
        ·
          refine ⟨780365545040153859335173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1040487393386871812446897 780365545040153859335173)
          ·
            refine ⟨146318539695028848625345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 780365545040153859335173 146318539695028848625345)
            ·
              refine ⟨109738904771271636469009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146318539695028848625345 109738904771271636469009)
              ·
                refine ⟨82304178578453727351757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109738904771271636469009 82304178578453727351757)
                ·
                  refine ⟨30864066966920147756909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82304178578453727351757 30864066966920147756909)
                  ·
                    rfl

theorem cell20_67621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_67621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67621 prefixEnd_67621 := by exact prefixLift 67621
  have htrace : WordTrace (prefixWord ++ tailWord_67621) baseStart_67621 baseEnd_67621 := by
    simpa [prefixWord, tailWord_67621, baseEnd_67621] using wordTrace_append hprefix tailTrace_67621
  have hstable : (prefixWord ++ tailWord_67621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67621).length < 2 ^ (prefixWord ++ tailWord_67621).sum := by decide
  have hdescent : baseEnd_67621 < baseStart_67621 := by decide
  rcases family_descends (prefixWord ++ tailWord_67621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67625 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_67625 : Nat := 118140960795 + 67625 * 2 ^ 59
def prefixEnd_67625 : Nat := 4983230072969 + 3 ^ 40 * 67625 * 2
def baseEnd_67625 : Nat := 30865892675913911623559

theorem tailTrace_67625 : CollatzResearch.WordTrace tailWord_67625 prefixEnd_67625 30865892675913911623559 := by
  unfold tailWord_67625
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466486380013649275612329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1644324253342432850408219 2466486380013649275612329)
  ·
    refine ⟨1849864785010236956709247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2466486380013649275612329 1849864785010236956709247)
    ·
      refine ⟨2774797177515355435063871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1849864785010236956709247 2774797177515355435063871)
      ·
        refine ⟨4162195766273033152595807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774797177515355435063871 4162195766273033152595807)
        ·
          refine ⟨6243293649409549728893711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4162195766273033152595807 6243293649409549728893711)
          ·
            refine ⟨9364940474114324593340567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243293649409549728893711 9364940474114324593340567)
            ·
              refine ⟨14047410711171486890010851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9364940474114324593340567 14047410711171486890010851)
              ·
                refine ⟨21071116066757230335016277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14047410711171486890010851 21071116066757230335016277)
                ·
                  refine ⟨30865892675913911623559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 21071116066757230335016277 30865892675913911623559)
                  ·
                    rfl

theorem cell20_67625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_67625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67625 prefixEnd_67625 := by exact prefixLift 67625
  have htrace : WordTrace (prefixWord ++ tailWord_67625) baseStart_67625 baseEnd_67625 := by
    simpa [prefixWord, tailWord_67625, baseEnd_67625] using wordTrace_append hprefix tailTrace_67625
  have hstable : (prefixWord ++ tailWord_67625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67625).length < 2 ^ (prefixWord ++ tailWord_67625).sum := by decide
  have hdescent : baseEnd_67625 < baseStart_67625 := by decide
  rcases family_descends (prefixWord ++ tailWord_67625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67663 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_67663 : Nat := 118140960795 + 67663 * 2 ^ 59
def prefixEnd_67663 : Nat := 4983230072969 + 3 ^ 40 * 67663 * 2
def baseEnd_67663 : Nat := 30883236911354668356737

theorem tailTrace_67663 : CollatzResearch.WordTrace tailWord_67663 prefixEnd_67663 30883236911354668356737 := by
  unfold tailWord_67663
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467872353875981765495643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1645248235917321176997095 2467872353875981765495643)
  ·
    refine ⟨3701808530813972648243465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2467872353875981765495643 3701808530813972648243465)
    ·
      refine ⟨2776356398110479486182599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3701808530813972648243465 2776356398110479486182599)
      ·
        refine ⟨4164534597165719229273899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776356398110479486182599 4164534597165719229273899)
        ·
          refine ⟨6246801895748578843910849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164534597165719229273899 6246801895748578843910849)
          ·
            refine ⟨4685101421811434132933137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6246801895748578843910849 4685101421811434132933137)
            ·
              refine ⟨3513826066358575599699853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4685101421811434132933137 3513826066358575599699853)
              ·
                refine ⟨1317684774884465849887445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3513826066358575599699853 1317684774884465849887445)
                ·
                  refine ⟨30883236911354668356737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1317684774884465849887445 30883236911354668356737)
                  ·
                    rfl

theorem cell20_67663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_67663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67663 prefixEnd_67663 := by exact prefixLift 67663
  have htrace : WordTrace (prefixWord ++ tailWord_67663) baseStart_67663 baseEnd_67663 := by
    simpa [prefixWord, tailWord_67663, baseEnd_67663] using wordTrace_append hprefix tailTrace_67663
  have hstable : (prefixWord ++ tailWord_67663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67663).length < 2 ^ (prefixWord ++ tailWord_67663).sum := by decide
  have hdescent : baseEnd_67663 < baseStart_67663 := by decide
  rcases family_descends (prefixWord ++ tailWord_67663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67676 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_67676 : Nat := 118140960795 + 67676 * 2 ^ 59
def prefixEnd_67676 : Nat := 4983230072969 + 3 ^ 40 * 67676 * 2
def baseEnd_67676 : Nat := 30889170465584400923351

theorem tailTrace_67676 : CollatzResearch.WordTrace tailWord_67676 prefixEnd_67676 30889170465584400923351 := by
  unfold tailWord_67676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234173251414442492859441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1645564335219256657145921 1234173251414442492859441)
  ·
    refine ⟨925629938560831869644581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1234173251414442492859441 925629938560831869644581)
    ·
      refine ⟨173555613480155975558359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 925629938560831869644581 173555613480155975558359)
      ·
        refine ⟨260333420220233963337539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173555613480155975558359 260333420220233963337539)
        ·
          refine ⟨390500130330350945006309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260333420220233963337539 390500130330350945006309)
          ·
            refine ⟨73218774436940802188683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 390500130330350945006309 73218774436940802188683)
            ·
              refine ⟨109828161655411203283025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73218774436940802188683 109828161655411203283025)
              ·
                refine ⟨82371121241558402462269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109828161655411203283025 82371121241558402462269)
                ·
                  refine ⟨30889170465584400923351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82371121241558402462269 30889170465584400923351)
                  ·
                    rfl

theorem cell20_67676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_67676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67676 prefixEnd_67676 := by exact prefixLift 67676
  have htrace : WordTrace (prefixWord ++ tailWord_67676) baseStart_67676 baseEnd_67676 := by
    simpa [prefixWord, tailWord_67676, baseEnd_67676] using wordTrace_append hprefix tailTrace_67676
  have hstable : (prefixWord ++ tailWord_67676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67676).length < 2 ^ (prefixWord ++ tailWord_67676).sum := by decide
  have hdescent : baseEnd_67676 < baseStart_67676 := by decide
  rcases family_descends (prefixWord ++ tailWord_67676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67680 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_67680 : Nat := 118140960795 + 67680 * 2 ^ 59
def prefixEnd_67680 : Nat := 4983230072969 + 3 ^ 40 * 67680 * 2
def baseEnd_67680 : Nat := 30890996174578164790001

theorem tailTrace_67680 : CollatzResearch.WordTrace tailWord_67680 prefixEnd_67680 30890996174578164790001 := by
  unfold tailWord_67680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234246197407196834432247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1645661596542929112576329 1234246197407196834432247)
  ·
    refine ⟨1851369296110795251648371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234246197407196834432247 1851369296110795251648371)
    ·
      refine ⟨2777053944166192877472557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851369296110795251648371 2777053944166192877472557)
      ·
        refine ⟨1041395229062322329052209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2777053944166192877472557 1041395229062322329052209)
        ·
          refine ⟨781046421796741746789157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1041395229062322329052209 781046421796741746789157)
          ·
            refine ⟨146446204086889077522967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 781046421796741746789157 146446204086889077522967)
            ·
              refine ⟨219669306130333616284451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146446204086889077522967 219669306130333616284451)
              ·
                refine ⟨329503959195500424426677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219669306130333616284451 329503959195500424426677)
                ·
                  refine ⟨30890996174578164790001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329503959195500424426677 30890996174578164790001)
                  ·
                    rfl

theorem cell20_67680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_67680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67680 prefixEnd_67680 := by exact prefixLift 67680
  have htrace : WordTrace (prefixWord ++ tailWord_67680) baseStart_67680 baseEnd_67680 := by
    simpa [prefixWord, tailWord_67680, baseEnd_67680] using wordTrace_append hprefix tailTrace_67680
  have hstable : (prefixWord ++ tailWord_67680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67680).length < 2 ^ (prefixWord ++ tailWord_67680).sum := by decide
  have hdescent : baseEnd_67680 < baseStart_67680 := by decide
  rcases family_descends (prefixWord ++ tailWord_67680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67697 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 3]
def baseStart_67697 : Nat := 118140960795 + 67697 * 2 ^ 59
def prefixEnd_67697 : Nat := 4983230072969 + 3 ^ 40 * 67697 * 2
def baseEnd_67697 : Nat := 30898755437801661223265

theorem tailTrace_67697 : CollatzResearch.WordTrace tailWord_67697 prefixEnd_67697 30898755437801661223265 := by
  unfold tailWord_67697
  simp only [CollatzResearch.WordTrace]
  refine ⟨2469112435752805572233345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1646074957168537048155563 2469112435752805572233345)
  ·
    refine ⟨1851834326814604179175009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2469112435752805572233345 1851834326814604179175009)
    ·
      refine ⟨1388875745110953134381257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1851834326814604179175009 1388875745110953134381257)
      ·
        refine ⟨1041656808833214850785943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1388875745110953134381257 1041656808833214850785943)
        ·
          refine ⟨1562485213249822276178915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041656808833214850785943 1562485213249822276178915)
          ·
            refine ⟨2343727819874733414268373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562485213249822276178915 2343727819874733414268373)
            ·
              refine ⟨54931120778314064396915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2343727819874733414268373 54931120778314064396915)
              ·
                refine ⟨82396681167471096595373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54931120778314064396915 82396681167471096595373)
                ·
                  refine ⟨30898755437801661223265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82396681167471096595373 30898755437801661223265)
                  ·
                    rfl

theorem cell20_67697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_67697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67697 prefixEnd_67697 := by exact prefixLift 67697
  have htrace : WordTrace (prefixWord ++ tailWord_67697) baseStart_67697 baseEnd_67697 := by
    simpa [prefixWord, tailWord_67697, baseEnd_67697] using wordTrace_append hprefix tailTrace_67697
  have hstable : (prefixWord ++ tailWord_67697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67697).length < 2 ^ (prefixWord ++ tailWord_67697).sum := by decide
  have hdescent : baseEnd_67697 < baseStart_67697 := by decide
  rcases family_descends (prefixWord ++ tailWord_67697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67738 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_67738 : Nat := 118140960795 + 67738 * 2 ^ 59
def prefixEnd_67738 : Nat := 4983230072969 + 3 ^ 40 * 67738 * 2
def baseEnd_67738 : Nat := 30917468954987740856431

theorem tailTrace_67738 : CollatzResearch.WordTrace tailWord_67738 prefixEnd_67738 30917468954987740856431 := by
  unfold tailWord_67738
  simp only [CollatzResearch.WordTrace]
  refine ⟨617651957151067393618967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1647071885736179716317245 617651957151067393618967)
  ·
    refine ⟨926477935726601090428451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 617651957151067393618967 926477935726601090428451)
    ·
      refine ⟨1389716903589901635642677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 926477935726601090428451 1389716903589901635642677)
      ·
        refine ⟨130285959711553278341501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1389716903589901635642677 130285959711553278341501)
        ·
          refine ⟨48857234891832479378063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130285959711553278341501 48857234891832479378063)
          ·
            refine ⟨73285852337748719067095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48857234891832479378063 73285852337748719067095)
            ·
              refine ⟨109928778506623078600643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73285852337748719067095 109928778506623078600643)
              ·
                refine ⟨164893167759934617900965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109928778506623078600643 164893167759934617900965)
                ·
                  refine ⟨30917468954987740856431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164893167759934617900965 30917468954987740856431)
                  ·
                    rfl

theorem cell20_67738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_67738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67738 prefixEnd_67738 := by exact prefixLift 67738
  have htrace : WordTrace (prefixWord ++ tailWord_67738) baseStart_67738 baseEnd_67738 := by
    simpa [prefixWord, tailWord_67738, baseEnd_67738] using wordTrace_append hprefix tailTrace_67738
  have hstable : (prefixWord ++ tailWord_67738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67738).length < 2 ^ (prefixWord ++ tailWord_67738).sum := by decide
  have hdescent : baseEnd_67738 < baseStart_67738 := by decide
  rcases family_descends (prefixWord ++ tailWord_67738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67739 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_67739 : Nat := 118140960795 + 67739 * 2 ^ 59
def prefixEnd_67739 : Nat := 4983230072969 + 3 ^ 40 * 67739 * 2
def baseEnd_67739 : Nat := 30917925382236181823093

theorem tailTrace_67739 : CollatzResearch.WordTrace tailWord_67739 prefixEnd_67739 30917925382236181823093 := by
  unfold tailWord_67739
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470644301600646745262271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1647096201067097830174847 2470644301600646745262271)
  ·
    refine ⟨3705966452400970117893407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2470644301600646745262271 3705966452400970117893407)
    ·
      refine ⟨5558949678601455176840111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3705966452400970117893407 5558949678601455176840111)
      ·
        refine ⟨8338424517902182765260167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5558949678601455176840111 8338424517902182765260167)
        ·
          refine ⟨12507636776853274147890251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8338424517902182765260167 12507636776853274147890251)
          ·
            refine ⟨18761455165279911221835377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12507636776853274147890251 18761455165279911221835377)
            ·
              refine ⟨14071091373959933416376533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18761455165279911221835377 14071091373959933416376533)
              ·
                refine ⟨329791204077185939446325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14071091373959933416376533 329791204077185939446325)
                ·
                  refine ⟨30917925382236181823093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329791204077185939446325 30917925382236181823093)
                  ·
                    rfl

theorem cell20_67739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_67739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67739 prefixEnd_67739 := by exact prefixLift 67739
  have htrace : WordTrace (prefixWord ++ tailWord_67739) baseStart_67739 baseEnd_67739 := by
    simpa [prefixWord, tailWord_67739, baseEnd_67739] using wordTrace_append hprefix tailTrace_67739
  have hstable : (prefixWord ++ tailWord_67739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67739).length < 2 ^ (prefixWord ++ tailWord_67739).sum := by decide
  have hdescent : baseEnd_67739 < baseStart_67739 := by decide
  rcases family_descends (prefixWord ++ tailWord_67739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67770 : List Nat := [3, 1, 1, 1, 2, 2, 4, 6]
def baseStart_67770 : Nat := 118140960795 + 67770 * 2 ^ 59
def prefixEnd_67770 : Nat := 4983230072969 + 3 ^ 40 * 67770 * 2
def baseEnd_67770 : Nat := 10310691542312617263211

theorem tailTrace_67770 : CollatzResearch.WordTrace tailWord_67770 prefixEnd_67770 10310691542312617263211 := by
  unfold tailWord_67770
  simp only [CollatzResearch.WordTrace]
  refine ⟨617943741122084759910191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1647849976325559359760509 617943741122084759910191)
  ·
    refine ⟨926915611683127139865287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 617943741122084759910191 926915611683127139865287)
    ·
      refine ⟨1390373417524690709797931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 926915611683127139865287 1390373417524690709797931)
      ·
        refine ⟨2085560126287036064696897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1390373417524690709797931 2085560126287036064696897)
        ·
          refine ⟨1564170094715277048522673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2085560126287036064696897 1564170094715277048522673)
          ·
            refine ⟨1173127571036457786392005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1564170094715277048522673 1173127571036457786392005)
            ·
              refine ⟨219961419569335834948501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1173127571036457786392005 219961419569335834948501)
              ·
                refine ⟨10310691542312617263211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 219961419569335834948501 10310691542312617263211)
                ·
                  rfl

theorem cell20_67770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_67770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67770 prefixEnd_67770 := by exact prefixLift 67770
  have htrace : WordTrace (prefixWord ++ tailWord_67770) baseStart_67770 baseEnd_67770 := by
    simpa [prefixWord, tailWord_67770, baseEnd_67770] using wordTrace_append hprefix tailTrace_67770
  have hstable : (prefixWord ++ tailWord_67770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67770).length < 2 ^ (prefixWord ++ tailWord_67770).sum := by decide
  have hdescent : baseEnd_67770 < baseStart_67770 := by decide
  rcases family_descends (prefixWord ++ tailWord_67770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67849 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 3]
def baseStart_67849 : Nat := 118140960795 + 67849 * 2 ^ 59
def prefixEnd_67849 : Nat := 4983230072969 + 3 ^ 40 * 67849 * 2
def baseEnd_67849 : Nat := 30968132379564688155977

theorem tailTrace_67849 : CollatzResearch.WordTrace tailWord_67849 prefixEnd_67849 30968132379564688155977 := by
  unfold tailWord_67849
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474656331202135531766601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1649770887468090354511067 2474656331202135531766601)
  ·
    refine ⟨1855992248401601648824951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2474656331202135531766601 1855992248401601648824951)
    ·
      refine ⟨2783988372602402473237427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855992248401601648824951 2783988372602402473237427)
      ·
        refine ⟨4175982558903603709856141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783988372602402473237427 4175982558903603709856141)
        ·
          refine ⟨1565993459588851391196053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4175982558903603709856141 1565993459588851391196053)
          ·
            refine ⟨73405943418227408962315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1565993459588851391196053 73405943418227408962315)
            ·
              refine ⟨110108915127341113443473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73405943418227408962315 110108915127341113443473)
              ·
                refine ⟨82581686345505835082605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110108915127341113443473 82581686345505835082605)
                ·
                  refine ⟨30968132379564688155977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82581686345505835082605 30968132379564688155977)
                  ·
                    rfl

theorem cell20_67849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_67849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67849 prefixEnd_67849 := by exact prefixLift 67849
  have htrace : WordTrace (prefixWord ++ tailWord_67849) baseStart_67849 baseEnd_67849 := by
    simpa [prefixWord, tailWord_67849, baseEnd_67849] using wordTrace_append hprefix tailTrace_67849
  have hstable : (prefixWord ++ tailWord_67849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67849).length < 2 ^ (prefixWord ++ tailWord_67849).sum := by decide
  have hdescent : baseEnd_67849 < baseStart_67849 := by decide
  rcases family_descends (prefixWord ++ tailWord_67849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67866 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_67866 : Nat := 118140960795 + 67866 * 2 ^ 59
def prefixEnd_67866 : Nat := 4983230072969 + 3 ^ 40 * 67866 * 2
def baseEnd_67866 : Nat := 30975891642788184589241

theorem tailTrace_67866 : CollatzResearch.WordTrace tailWord_67866 prefixEnd_67866 30975891642788184589241 := by
  unfold tailWord_67866
  simp only [CollatzResearch.WordTrace]
  refine ⟨618819093035136858783863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1650184248093698290090301 618819093035136858783863)
  ·
    refine ⟨928228639552705288175795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618819093035136858783863 928228639552705288175795)
    ·
      refine ⟨1392342959329057932263693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928228639552705288175795 1392342959329057932263693)
      ·
        refine ⟨522128609748396724598885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1392342959329057932263693 522128609748396724598885)
        ·
          refine ⟨97899114327824385862291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 522128609748396724598885 97899114327824385862291)
          ·
            refine ⟨146848671491736578793437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97899114327824385862291 146848671491736578793437)
            ·
              refine ⟨55068251809401217047539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146848671491736578793437 55068251809401217047539)
              ·
                refine ⟨82602377714101825571309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55068251809401217047539 82602377714101825571309)
                ·
                  refine ⟨30975891642788184589241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82602377714101825571309 30975891642788184589241)
                  ·
                    rfl

theorem cell20_67866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_67866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67866 prefixEnd_67866 := by exact prefixLift 67866
  have htrace : WordTrace (prefixWord ++ tailWord_67866) baseStart_67866 baseEnd_67866 := by
    simpa [prefixWord, tailWord_67866, baseEnd_67866] using wordTrace_append hprefix tailTrace_67866
  have hstable : (prefixWord ++ tailWord_67866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67866).length < 2 ^ (prefixWord ++ tailWord_67866).sum := by decide
  have hdescent : baseEnd_67866 < baseStart_67866 := by decide
  rcases family_descends (prefixWord ++ tailWord_67866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67886 : List Nat := [4, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_67886 : Nat := 118140960795 + 67886 * 2 ^ 59
def prefixEnd_67886 : Nat := 4983230072969 + 3 ^ 40 * 67886 * 2
def baseEnd_67886 : Nat := 30985020187757003922493

theorem tailTrace_67886 : CollatzResearch.WordTrace tailWord_67886 prefixEnd_67886 30985020187757003922493 := by
  unfold tailWord_67886
  simp only [CollatzResearch.WordTrace]
  refine ⟨309500729008511356357939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1650670554712060567242341 309500729008511356357939)
  ·
    refine ⟨464251093512767034536909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 309500729008511356357939 464251093512767034536909)
    ·
      refine ⟨174094160067287637951341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 464251093512767034536909 174094160067287637951341)
      ·
        refine ⟨65285310025232864231753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174094160067287637951341 65285310025232864231753)
        ·
          refine ⟨48963982518924648173815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65285310025232864231753 48963982518924648173815)
          ·
            refine ⟨73445973778386972260723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48963982518924648173815 73445973778386972260723)
            ·
              refine ⟨110168960667580458391085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73445973778386972260723 110168960667580458391085)
              ·
                refine ⟨41313360250342671896657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110168960667580458391085 41313360250342671896657)
                ·
                  refine ⟨30985020187757003922493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41313360250342671896657 30985020187757003922493)
                  ·
                    rfl

theorem cell20_67886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_67886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67886 prefixEnd_67886 := by exact prefixLift 67886
  have htrace : WordTrace (prefixWord ++ tailWord_67886) baseStart_67886 baseEnd_67886 := by
    simpa [prefixWord, tailWord_67886, baseEnd_67886] using wordTrace_append hprefix tailTrace_67886
  have hstable : (prefixWord ++ tailWord_67886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67886).length < 2 ^ (prefixWord ++ tailWord_67886).sum := by decide
  have hdescent : baseEnd_67886 < baseStart_67886 := by decide
  rcases family_descends (prefixWord ++ tailWord_67886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67890 : List Nat := [3, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_67890 : Nat := 118140960795 + 67890 * 2 ^ 59
def prefixEnd_67890 : Nat := 4983230072969 + 3 ^ 40 * 67890 * 2
def baseEnd_67890 : Nat := 30986845896750767789143

theorem tailTrace_67890 : CollatzResearch.WordTrace tailWord_67890 prefixEnd_67890 30986845896750767789143 := by
  unfold tailWord_67890
  simp only [CollatzResearch.WordTrace]
  refine ⟨619037931013399883502281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1650767816035733022672749 619037931013399883502281)
  ·
    refine ⟨464278448260049912626711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 619037931013399883502281 464278448260049912626711)
    ·
      refine ⟨696417672390074868940067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464278448260049912626711 696417672390074868940067)
      ·
        refine ⟨1044626508585112303410101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696417672390074868940067 1044626508585112303410101)
        ·
          refine ⟨97933735179854278444697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1044626508585112303410101 97933735179854278444697)
          ·
            refine ⟨73450301384890708833523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97933735179854278444697 73450301384890708833523)
            ·
              refine ⟨110175452077336063250285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73450301384890708833523 110175452077336063250285)
              ·
                refine ⟨41315794529001023718857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110175452077336063250285 41315794529001023718857)
                ·
                  refine ⟨30986845896750767789143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41315794529001023718857 30986845896750767789143)
                  ·
                    rfl

theorem cell20_67890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_67890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67890 prefixEnd_67890 := by exact prefixLift 67890
  have htrace : WordTrace (prefixWord ++ tailWord_67890) baseStart_67890 baseEnd_67890 := by
    simpa [prefixWord, tailWord_67890, baseEnd_67890] using wordTrace_append hprefix tailTrace_67890
  have hstable : (prefixWord ++ tailWord_67890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67890).length < 2 ^ (prefixWord ++ tailWord_67890).sum := by decide
  have hdescent : baseEnd_67890 < baseStart_67890 := by decide
  rcases family_descends (prefixWord ++ tailWord_67890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67891 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_67891 : Nat := 118140960795 + 67891 * 2 ^ 59
def prefixEnd_67891 : Nat := 4983230072969 + 3 ^ 40 * 67891 * 2
def baseEnd_67891 : Nat := 30987302323999208755805

theorem tailTrace_67891 : CollatzResearch.WordTrace tailWord_67891 prefixEnd_67891 30987302323999208755805 := by
  unfold tailWord_67891
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476188197049976704795527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1650792131366651136530351 2476188197049976704795527)
  ·
    refine ⟨3714282295574965057193291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476188197049976704795527 3714282295574965057193291)
    ·
      refine ⟨5571423443362447585789937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714282295574965057193291 5571423443362447585789937)
      ·
        refine ⟨4178567582521835689342453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5571423443362447585789937 4178567582521835689342453)
        ·
          refine ⟨391740710861422095875855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4178567582521835689342453 391740710861422095875855)
          ·
            refine ⟨587611066292133143813783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391740710861422095875855 587611066292133143813783)
            ·
              refine ⟨881416599438199715720675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587611066292133143813783 881416599438199715720675)
              ·
                refine ⟨1322124899157299573581013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881416599438199715720675 1322124899157299573581013)
                ·
                  refine ⟨30987302323999208755805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1322124899157299573581013 30987302323999208755805)
                  ·
                    rfl

theorem cell20_67891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_67891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67891 prefixEnd_67891 := by exact prefixLift 67891
  have htrace : WordTrace (prefixWord ++ tailWord_67891) baseStart_67891 baseEnd_67891 := by
    simpa [prefixWord, tailWord_67891, baseEnd_67891] using wordTrace_append hprefix tailTrace_67891
  have hstable : (prefixWord ++ tailWord_67891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67891).length < 2 ^ (prefixWord ++ tailWord_67891).sum := by decide
  have hdescent : baseEnd_67891 < baseStart_67891 := by decide
  rcases family_descends (prefixWord ++ tailWord_67891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67911 : List Nat := [1, 1, 4, 1, 2, 2, 5, 2, 2]
def baseStart_67911 : Nat := 118140960795 + 67911 * 2 ^ 59
def prefixEnd_67911 : Nat := 4983230072969 + 3 ^ 40 * 67911 * 2
def baseEnd_67911 : Nat := 30996430868968028089057

theorem tailTrace_67911 : CollatzResearch.WordTrace tailWord_67911 prefixEnd_67911 30996430868968028089057 := by
  unfold tailWord_67911
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476917656977520120523587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1651278437985013413682391 2476917656977520120523587)
  ·
    refine ⟨3715376485466280180785381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476917656977520120523587 3715376485466280180785381)
    ·
      refine ⟨696633091024927533897259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3715376485466280180785381 696633091024927533897259)
      ·
        refine ⟨1044949636537391300845889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696633091024927533897259 1044949636537391300845889)
        ·
          refine ⟨783712227403043475634417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044949636537391300845889 783712227403043475634417)
          ·
            refine ⟨587784170552282606725813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 783712227403043475634417 587784170552282606725813)
            ·
              refine ⟨55104765989276494380545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 587784170552282606725813 55104765989276494380545)
              ·
                refine ⟨41328574491957370785409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55104765989276494380545 41328574491957370785409)
                ·
                  refine ⟨30996430868968028089057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41328574491957370785409 30996430868968028089057)
                  ·
                    rfl

theorem cell20_67911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 2].length) (baseStart_67911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67911 prefixEnd_67911 := by exact prefixLift 67911
  have htrace : WordTrace (prefixWord ++ tailWord_67911) baseStart_67911 baseEnd_67911 := by
    simpa [prefixWord, tailWord_67911, baseEnd_67911] using wordTrace_append hprefix tailTrace_67911
  have hstable : (prefixWord ++ tailWord_67911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67911).length < 2 ^ (prefixWord ++ tailWord_67911).sum := by decide
  have hdescent : baseEnd_67911 < baseStart_67911 := by decide
  rcases family_descends (prefixWord ++ tailWord_67911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67922 : List Nat := [3, 2, 2, 1, 1, 1, 3, 7]
def baseStart_67922 : Nat := 118140960795 + 67922 * 2 ^ 59
def prefixEnd_67922 : Nat := 4983230072969 + 3 ^ 40 * 67922 * 2
def baseEnd_67922 : Nat := 10333817189566959574115

theorem tailTrace_67922 : CollatzResearch.WordTrace tailWord_67922 prefixEnd_67922 10333817189566959574115 := by
  unfold tailWord_67922
  simp only [CollatzResearch.WordTrace]
  refine ⟨619329714984417249793505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1651545906625112666116013 619329714984417249793505)
  ·
    refine ⟨464497286238312937345129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 619329714984417249793505 464497286238312937345129)
    ·
      refine ⟨348372964678734703008847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464497286238312937345129 348372964678734703008847)
      ·
        refine ⟨522559447018102054513271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348372964678734703008847 522559447018102054513271)
        ·
          refine ⟨783839170527153081769907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522559447018102054513271 783839170527153081769907)
          ·
            refine ⟨1175758755790729622654861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783839170527153081769907 1175758755790729622654861)
            ·
              refine ⟨440909533421523608495573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1175758755790729622654861 440909533421523608495573)
              ·
                refine ⟨10333817189566959574115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 440909533421523608495573 10333817189566959574115)
                ·
                  rfl

theorem cell20_67922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_67922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67922 prefixEnd_67922 := by exact prefixLift 67922
  have htrace : WordTrace (prefixWord ++ tailWord_67922) baseStart_67922 baseEnd_67922 := by
    simpa [prefixWord, tailWord_67922, baseEnd_67922] using wordTrace_append hprefix tailTrace_67922
  have hstable : (prefixWord ++ tailWord_67922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67922).length < 2 ^ (prefixWord ++ tailWord_67922).sum := by decide
  have hdescent : baseEnd_67922 < baseStart_67922 := by decide
  rcases family_descends (prefixWord ++ tailWord_67922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67925 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 3]
def baseStart_67925 : Nat := 118140960795 + 67925 * 2 ^ 59
def prefixEnd_67925 : Nat := 4983230072969 + 3 ^ 40 * 67925 * 2
def baseEnd_67925 : Nat := 31002820850446201622333

theorem tailTrace_67925 : CollatzResearch.WordTrace tailWord_67925 prefixEnd_67925 31002820850446201622333 := by
  unfold tailWord_67925
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477428278926800511533229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1651618852617867007688819 2477428278926800511533229)
  ·
    refine ⟨929035604597550191824961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2477428278926800511533229 929035604597550191824961)
    ·
      refine ⟨696776703448162643868721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 929035604597550191824961 696776703448162643868721)
      ·
        refine ⟨522582527586121982901541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 696776703448162643868721 522582527586121982901541)
        ·
          refine ⟨97984223922397871794039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 522582527586121982901541 97984223922397871794039)
          ·
            refine ⟨146976335883596807691059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97984223922397871794039 146976335883596807691059)
            ·
              refine ⟨220464503825395211536589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146976335883596807691059 220464503825395211536589)
              ·
                refine ⟨82674188934523204326221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220464503825395211536589 82674188934523204326221)
                ·
                  refine ⟨31002820850446201622333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82674188934523204326221 31002820850446201622333)
                  ·
                    rfl

theorem cell20_67925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_67925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67925 prefixEnd_67925 := by exact prefixLift 67925
  have htrace : WordTrace (prefixWord ++ tailWord_67925) baseStart_67925 baseEnd_67925 := by
    simpa [prefixWord, tailWord_67925, baseEnd_67925] using wordTrace_append hprefix tailTrace_67925
  have hstable : (prefixWord ++ tailWord_67925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67925).length < 2 ^ (prefixWord ++ tailWord_67925).sum := by decide
  have hdescent : baseEnd_67925 < baseStart_67925 := by decide
  rcases family_descends (prefixWord ++ tailWord_67925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67977 : List Nat := [1, 2, 1, 1, 6, 3, 1, 5]
def baseStart_67977 : Nat := 118140960795 + 67977 * 2 ^ 59
def prefixEnd_67977 : Nat := 4983230072969 + 3 ^ 40 * 67977 * 2
def baseEnd_67977 : Nat := 10342185022455043962929

theorem tailTrace_67977 : CollatzResearch.WordTrace tailWord_67977 prefixEnd_67977 10342185022455043962929 := by
  unfold tailWord_67977
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479324874738413392426185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1652883249825608928284123 2479324874738413392426185)
  ·
    refine ⟨1859493656053810044319639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2479324874738413392426185 1859493656053810044319639)
    ·
      refine ⟨2789240484080715066479459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859493656053810044319639 2789240484080715066479459)
      ·
        refine ⟨4183860726121072599719189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789240484080715066479459 4183860726121072599719189)
        ·
          refine ⟨196118471536925278111837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4183860726121072599719189 196118471536925278111837)
          ·
            refine ⟨73544426826346979291939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196118471536925278111837 73544426826346979291939)
            ·
              refine ⟨110316640239520468937909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73544426826346979291939 110316640239520468937909)
              ·
                refine ⟨10342185022455043962929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110316640239520468937909 10342185022455043962929)
                ·
                  rfl

theorem cell20_67977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_67977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67977 prefixEnd_67977 := by exact prefixLift 67977
  have htrace : WordTrace (prefixWord ++ tailWord_67977) baseStart_67977 baseEnd_67977 := by
    simpa [prefixWord, tailWord_67977, baseEnd_67977] using wordTrace_append hprefix tailTrace_67977
  have hstable : (prefixWord ++ tailWord_67977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67977).length < 2 ^ (prefixWord ++ tailWord_67977).sum := by decide
  have hdescent : baseEnd_67977 < baseStart_67977 := by decide
  rcases family_descends (prefixWord ++ tailWord_67977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68005 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_68005 : Nat := 118140960795 + 68005 * 2 ^ 59
def prefixEnd_68005 : Nat := 4983230072969 + 3 ^ 40 * 68005 * 2
def baseEnd_68005 : Nat := 31039335030321478955339

theorem tailTrace_68005 : CollatzResearch.WordTrace tailWord_68005 prefixEnd_68005 31039335030321478955339 := by
  unfold tailWord_68005
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480346118636974174445469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1653564079091316116296979 2480346118636974174445469)
  ·
    refine ⟨930129794488865315417051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2480346118636974174445469 930129794488865315417051)
    ·
      refine ⟨1395194691733297973125577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930129794488865315417051 1395194691733297973125577)
      ·
        refine ⟨1046396018799973479844183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1395194691733297973125577 1046396018799973479844183)
        ·
          refine ⟨1569594028199960219766275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046396018799973479844183 1569594028199960219766275)
          ·
            refine ⟨2354391042299940329649413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569594028199960219766275 2354391042299940329649413)
            ·
              refine ⟨441448320431238811809265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2354391042299940329649413 441448320431238811809265)
              ·
                refine ⟨331086240323429108856949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441448320431238811809265 331086240323429108856949)
                ·
                  refine ⟨31039335030321478955339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331086240323429108856949 31039335030321478955339)
                  ·
                    rfl

theorem cell20_68005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_68005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68005 prefixEnd_68005 := by exact prefixLift 68005
  have htrace : WordTrace (prefixWord ++ tailWord_68005) baseStart_68005 baseEnd_68005 := by
    simpa [prefixWord, tailWord_68005, baseEnd_68005] using wordTrace_append hprefix tailTrace_68005
  have hstable : (prefixWord ++ tailWord_68005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68005).length < 2 ^ (prefixWord ++ tailWord_68005).sum := by decide
  have hdescent : baseEnd_68005 < baseStart_68005 := by decide
  rcases family_descends (prefixWord ++ tailWord_68005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68012 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_68012 : Nat := 118140960795 + 68012 * 2 ^ 59
def prefixEnd_68012 : Nat := 4983230072969 + 3 ^ 40 * 68012 * 2
def baseEnd_68012 : Nat := 31042530021060565721977

theorem tailTrace_68012 : CollatzResearch.WordTrace tailWord_68012 prefixEnd_68012 31042530021060565721977 := by
  unfold tailWord_68012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240300714805807184975145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1653734286407742913300193 1240300714805807184975145)
  ·
    refine ⟨930225536104355388731359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1240300714805807184975145 930225536104355388731359)
    ·
      refine ⟨1395338304156533083097039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930225536104355388731359 1395338304156533083097039)
      ·
        refine ⟨2093007456234799624645559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395338304156533083097039 2093007456234799624645559)
        ·
          refine ⟨3139511184352199436968339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093007456234799624645559 3139511184352199436968339)
          ·
            refine ⟨4709266776528299155452509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3139511184352199436968339 4709266776528299155452509)
            ·
              refine ⟨1765975041198112183294691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4709266776528299155452509 1765975041198112183294691)
              ·
                refine ⟨2648962561797168274942037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765975041198112183294691 2648962561797168274942037)
                ·
                  refine ⟨31042530021060565721977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2648962561797168274942037 31042530021060565721977)
                  ·
                    rfl

theorem cell20_68012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_68012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68012 prefixEnd_68012 := by exact prefixLift 68012
  have htrace : WordTrace (prefixWord ++ tailWord_68012) baseStart_68012 baseEnd_68012 := by
    simpa [prefixWord, tailWord_68012, baseEnd_68012] using wordTrace_append hprefix tailTrace_68012
  have hstable : (prefixWord ++ tailWord_68012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68012).length < 2 ^ (prefixWord ++ tailWord_68012).sum := by decide
  have hdescent : baseEnd_68012 < baseStart_68012 := by decide
  rcases family_descends (prefixWord ++ tailWord_68012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68029 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_68029 : Nat := 118140960795 + 68029 * 2 ^ 59
def prefixEnd_68029 : Nat := 4983230072969 + 3 ^ 40 * 68029 * 2
def baseEnd_68029 : Nat := 31050289284284062155241

theorem tailTrace_68029 : CollatzResearch.WordTrace tailWord_68029 prefixEnd_68029 31050289284284062155241 := by
  unfold tailWord_68029
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481221470550026273319141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1654147647033350848879427 2481221470550026273319141)
  ·
    refine ⟨465229025728129926247339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2481221470550026273319141 465229025728129926247339)
    ·
      refine ⟨697843538592194889371009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465229025728129926247339 697843538592194889371009)
      ·
        refine ⟨523382653944146167028257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 697843538592194889371009 523382653944146167028257)
        ·
          refine ⟨392536990458109625271193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523382653944146167028257 392536990458109625271193)
          ·
            refine ⟨294402742843582218953395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392536990458109625271193 294402742843582218953395)
            ·
              refine ⟨441604114265373328430093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294402742843582218953395 441604114265373328430093)
              ·
                refine ⟨165601542849514998161285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441604114265373328430093 165601542849514998161285)
                ·
                  refine ⟨31050289284284062155241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165601542849514998161285 31050289284284062155241)
                  ·
                    rfl

theorem cell20_68029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_68029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68029 prefixEnd_68029 := by exact prefixLift 68029
  have htrace : WordTrace (prefixWord ++ tailWord_68029) baseStart_68029 baseEnd_68029 := by
    simpa [prefixWord, tailWord_68029, baseEnd_68029] using wordTrace_append hprefix tailTrace_68029
  have hstable : (prefixWord ++ tailWord_68029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68029).length < 2 ^ (prefixWord ++ tailWord_68029).sum := by decide
  have hdescent : baseEnd_68029 < baseStart_68029 := by decide
  rcases family_descends (prefixWord ++ tailWord_68029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68039 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 3]
def baseStart_68039 : Nat := 118140960795 + 68039 * 2 ^ 59
def prefixEnd_68039 : Nat := 4983230072969 + 3 ^ 40 * 68039 * 2
def baseEnd_68039 : Nat := 31054853556768471821867

theorem tailTrace_68039 : CollatzResearch.WordTrace tailWord_68039 prefixEnd_68039 31054853556768471821867 := by
  unfold tailWord_68039
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481586200513797981183171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1654390800342531987455447 2481586200513797981183171)
  ·
    refine ⟨3722379300770696971774757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2481586200513797981183171 3722379300770696971774757)
    ·
      refine ⟨697946118894505682207767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3722379300770696971774757 697946118894505682207767)
      ·
        refine ⟨1046919178341758523311651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697946118894505682207767 1046919178341758523311651)
        ·
          refine ⟨1570378767512637784967477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046919178341758523311651 1570378767512637784967477)
          ·
            refine ⟨147223009454309792340701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1570378767512637784967477 147223009454309792340701)
            ·
              refine ⟨55208628545366172127763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147223009454309792340701 55208628545366172127763)
              ·
                refine ⟨82812942818049258191645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55208628545366172127763 82812942818049258191645)
                ·
                  refine ⟨31054853556768471821867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82812942818049258191645 31054853556768471821867)
                  ·
                    rfl

theorem cell20_68039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 3].length) (baseStart_68039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68039 prefixEnd_68039 := by exact prefixLift 68039
  have htrace : WordTrace (prefixWord ++ tailWord_68039) baseStart_68039 baseEnd_68039 := by
    simpa [prefixWord, tailWord_68039, baseEnd_68039] using wordTrace_append hprefix tailTrace_68039
  have hstable : (prefixWord ++ tailWord_68039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68039).length < 2 ^ (prefixWord ++ tailWord_68039).sum := by decide
  have hdescent : baseEnd_68039 < baseStart_68039 := by decide
  rcases family_descends (prefixWord ++ tailWord_68039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68053 : List Nat := [1, 3, 2, 3, 1, 2, 4, 4]
def baseStart_68053 : Nat := 118140960795 + 68053 * 2 ^ 59
def prefixEnd_68053 : Nat := 4983230072969 + 3 ^ 40 * 68053 * 2
def baseEnd_68053 : Nat := 10353747846082215118381

theorem tailTrace_68053 : CollatzResearch.WordTrace tailWord_68053 prefixEnd_68053 10353747846082215118381 := by
  unfold tailWord_68053
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482096822463078372192813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1654731214975385581461875 2482096822463078372192813)
  ·
    refine ⟨930786308423654389572305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2482096822463078372192813 930786308423654389572305)
    ·
      refine ⟨698089731317740792179229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 930786308423654389572305 698089731317740792179229)
      ·
        refine ⟨261783649244152797067211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 698089731317740792179229 261783649244152797067211)
        ·
          refine ⟨392675473866229195600817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261783649244152797067211 392675473866229195600817)
          ·
            refine ⟨294506605399671896700613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392675473866229195600817 294506605399671896700613)
            ·
              refine ⟨55219988512438480631365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294506605399671896700613 55219988512438480631365)
              ·
                refine ⟨10353747846082215118381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55219988512438480631365 10353747846082215118381)
                ·
                  rfl

theorem cell20_68053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_68053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68053 prefixEnd_68053 := by exact prefixLift 68053
  have htrace : WordTrace (prefixWord ++ tailWord_68053) baseStart_68053 baseEnd_68053 := by
    simpa [prefixWord, tailWord_68053, baseEnd_68053] using wordTrace_append hprefix tailTrace_68053
  have hstable : (prefixWord ++ tailWord_68053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68053).length < 2 ^ (prefixWord ++ tailWord_68053).sum := by decide
  have hdescent : baseEnd_68053 < baseStart_68053 := by decide
  rcases family_descends (prefixWord ++ tailWord_68053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68063 : List Nat := [1, 1, 2, 3, 3, 4, 1, 3, 2]
def baseStart_68063 : Nat := 118140960795 + 68063 * 2 ^ 59
def prefixEnd_68063 : Nat := 4983230072969 + 3 ^ 40 * 68063 * 2
def baseEnd_68063 : Nat := 31065807810731055021769

theorem tailTrace_68063 : CollatzResearch.WordTrace tailWord_68063 prefixEnd_68063 31065807810731055021769 := by
  unfold tailWord_68063
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482461552426850080056843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1654974368284566720037895 2482461552426850080056843)
  ·
    refine ⟨3723692328640275120085265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2482461552426850080056843 3723692328640275120085265)
    ·
      refine ⟨2792769246480206340063949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3723692328640275120085265 2792769246480206340063949)
      ·
        refine ⟨1047288467430077377523981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2792769246480206340063949 1047288467430077377523981)
        ·
          refine ⟨392733175286279016571493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1047288467430077377523981 392733175286279016571493)
          ·
            refine ⟨73637470366177315607155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 392733175286279016571493 73637470366177315607155)
            ·
              refine ⟨110456205549265973410733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73637470366177315607155 110456205549265973410733)
              ·
                refine ⟨41421077080974740029025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110456205549265973410733 41421077080974740029025)
                ·
                  refine ⟨31065807810731055021769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41421077080974740029025 31065807810731055021769)
                  ·
                    rfl

theorem cell20_68063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 2].length) (baseStart_68063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68063 prefixEnd_68063 := by exact prefixLift 68063
  have htrace : WordTrace (prefixWord ++ tailWord_68063) baseStart_68063 baseEnd_68063 := by
    simpa [prefixWord, tailWord_68063, baseEnd_68063] using wordTrace_append hprefix tailTrace_68063
  have hstable : (prefixWord ++ tailWord_68063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68063).length < 2 ^ (prefixWord ++ tailWord_68063).sum := by decide
  have hdescent : baseEnd_68063 < baseStart_68063 := by decide
  rcases family_descends (prefixWord ++ tailWord_68063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68074 : List Nat := [3, 1, 3, 1, 3, 1, 8]
def baseStart_68074 : Nat := 118140960795 + 68074 * 2 ^ 59
def prefixEnd_68074 : Nat := 4983230072969 + 3 ^ 40 * 68074 * 2
def baseEnd_68074 : Nat := 3452314278940433961673

theorem tailTrace_68074 : CollatzResearch.WordTrace tailWord_68074 prefixEnd_68074 3452314278940433961673 := by
  unfold tailWord_68074
  simp only [CollatzResearch.WordTrace]
  refine ⟨620715688846749739676819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1655241836924665972471517 620715688846749739676819)
  ·
    refine ⟨931073533270124609515229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620715688846749739676819 931073533270124609515229)
    ·
      refine ⟨349152574976296728568211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 931073533270124609515229 349152574976296728568211)
      ·
        refine ⟨523728862464445092852317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349152574976296728568211 523728862464445092852317)
        ·
          refine ⟨196398323424166909819619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523728862464445092852317 196398323424166909819619)
          ·
            refine ⟨294597485136250364729429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196398323424166909819619 294597485136250364729429)
            ·
              refine ⟨3452314278940433961673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 294597485136250364729429 3452314278940433961673)
              ·
                rfl

theorem cell20_68074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 8].length) (baseStart_68074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68074 prefixEnd_68074 := by exact prefixLift 68074
  have htrace : WordTrace (prefixWord ++ tailWord_68074) baseStart_68074 baseEnd_68074 := by
    simpa [prefixWord, tailWord_68074, baseEnd_68074] using wordTrace_append hprefix tailTrace_68074
  have hstable : (prefixWord ++ tailWord_68074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68074).length < 2 ^ (prefixWord ++ tailWord_68074).sum := by decide
  have hdescent : baseEnd_68074 < baseStart_68074 := by decide
  rcases family_descends (prefixWord ++ tailWord_68074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68081 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_68081 : Nat := 118140960795 + 68081 * 2 ^ 59
def prefixEnd_68081 : Nat := 4983230072969 + 3 ^ 40 * 68081 * 2
def baseEnd_68081 : Nat := 31074023501202992421695

theorem tailTrace_68081 : CollatzResearch.WordTrace tailWord_68081 prefixEnd_68081 31074023501202992421695 := by
  unfold tailWord_68081
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483118066361639154212097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1655412044241092769474731 2483118066361639154212097)
  ·
    refine ⟨1862338549771229365659073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2483118066361639154212097 1862338549771229365659073)
    ·
      refine ⟨1396753912328422024244305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1862338549771229365659073 1396753912328422024244305)
      ·
        refine ⟨1047565434246316518183229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1396753912328422024244305 1047565434246316518183229)
        ·
          refine ⟨392837037842368694318711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1047565434246316518183229 392837037842368694318711)
          ·
            refine ⟨589255556763553041478067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392837037842368694318711 589255556763553041478067)
            ·
              refine ⟨883883335145329562217101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589255556763553041478067 883883335145329562217101)
              ·
                refine ⟨331456250679498585831413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 883883335145329562217101 331456250679498585831413)
                ·
                  refine ⟨31074023501202992421695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331456250679498585831413 31074023501202992421695)
                  ·
                    rfl

theorem cell20_68081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_68081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68081 prefixEnd_68081 := by exact prefixLift 68081
  have htrace : WordTrace (prefixWord ++ tailWord_68081) baseStart_68081 baseEnd_68081 := by
    simpa [prefixWord, tailWord_68081, baseEnd_68081] using wordTrace_append hprefix tailTrace_68081
  have hstable : (prefixWord ++ tailWord_68081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68081).length < 2 ^ (prefixWord ++ tailWord_68081).sum := by decide
  have hdescent : baseEnd_68081 < baseStart_68081 := by decide
  rcases family_descends (prefixWord ++ tailWord_68081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68132 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_68132 : Nat := 118140960795 + 68132 * 2 ^ 59
def prefixEnd_68132 : Nat := 4983230072969 + 3 ^ 40 * 68132 * 2
def baseEnd_68132 : Nat := 31097301290873481721487

theorem tailTrace_68132 : CollatzResearch.WordTrace tailWord_68132 prefixEnd_68132 31097301290873481721487 := by
  unfold tailWord_68132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1242489094588437432159325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1656652126117916576212433 1242489094588437432159325)
  ·
    refine ⟨465933410470664037059747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1242489094588437432159325 465933410470664037059747)
    ·
      refine ⟨698900115705996055589621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465933410470664037059747 698900115705996055589621)
      ·
        refine ⟨65521885847437130211527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 698900115705996055589621 65521885847437130211527)
        ·
          refine ⟨98282828771155695317291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65521885847437130211527 98282828771155695317291)
          ·
            refine ⟨147424243156733542975937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98282828771155695317291 147424243156733542975937)
            ·
              refine ⟨110568182367550157231953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147424243156733542975937 110568182367550157231953)
              ·
                refine ⟨82926136775662617923965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110568182367550157231953 82926136775662617923965)
                ·
                  refine ⟨31097301290873481721487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82926136775662617923965 31097301290873481721487)
                  ·
                    rfl

theorem cell20_68132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_68132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68132 prefixEnd_68132 := by exact prefixLift 68132
  have htrace : WordTrace (prefixWord ++ tailWord_68132) baseStart_68132 baseEnd_68132 := by
    simpa [prefixWord, tailWord_68132, baseEnd_68132] using wordTrace_append hprefix tailTrace_68132
  have hstable : (prefixWord ++ tailWord_68132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68132).length < 2 ^ (prefixWord ++ tailWord_68132).sum := by decide
  have hdescent : baseEnd_68132 < baseStart_68132 := by decide
  rcases family_descends (prefixWord ++ tailWord_68132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68167 : List Nat := [1, 1, 4, 1, 4, 2, 3, 4]
def baseStart_68167 : Nat := 118140960795 + 68167 * 2 ^ 59
def prefixEnd_68167 : Nat := 4983230072969 + 3 ^ 40 * 68167 * 2
def baseEnd_68167 : Nat := 10371092081522971851559

theorem tailTrace_68167 : CollatzResearch.WordTrace tailWord_68167 prefixEnd_68167 10371092081522971851559 := by
  unfold tailWord_68167
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486254744050075841842755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1657503162700050561228503 2486254744050075841842755)
  ·
    refine ⟨3729382116075113762764133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2486254744050075841842755 3729382116075113762764133)
    ·
      refine ⟨699259146764083830518275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3729382116075113762764133 699259146764083830518275)
      ·
        refine ⟨1048888720146125745777413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699259146764083830518275 1048888720146125745777413)
        ·
          refine ⟨196666635027398577333265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1048888720146125745777413 196666635027398577333265)
          ·
            refine ⟨147499976270548932999949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196666635027398577333265 147499976270548932999949)
            ·
              refine ⟨55312491101455849874981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147499976270548932999949 55312491101455849874981)
              ·
                refine ⟨10371092081522971851559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55312491101455849874981 10371092081522971851559)
                ·
                  rfl

theorem cell20_68167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_68167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68167 prefixEnd_68167 := by exact prefixLift 68167
  have htrace : WordTrace (prefixWord ++ tailWord_68167) baseStart_68167 baseEnd_68167 := by
    simpa [prefixWord, tailWord_68167, baseEnd_68167] using wordTrace_append hprefix tailTrace_68167
  have hstable : (prefixWord ++ tailWord_68167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68167).length < 2 ^ (prefixWord ++ tailWord_68167).sum := by decide
  have hdescent : baseEnd_68167 < baseStart_68167 := by decide
  rcases family_descends (prefixWord ++ tailWord_68167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68171 : List Nat := [1, 1, 1, 1, 3, 1, 4, 8]
def baseStart_68171 : Nat := 118140960795 + 68171 * 2 ^ 59
def prefixEnd_68171 : Nat := 4983230072969 + 3 ^ 40 * 68171 * 2
def baseEnd_68171 : Nat := 10371700651187559807109

theorem tailTrace_68171 : CollatzResearch.WordTrace tailWord_68171 prefixEnd_68171 10371700651187559807109 := by
  unfold tailWord_68171
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486400636035584524988367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1657600424023723016658911 2486400636035584524988367)
  ·
    refine ⟨3729600954053376787482551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2486400636035584524988367 3729600954053376787482551)
    ·
      refine ⟨5594401431080065181223827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3729600954053376787482551 5594401431080065181223827)
      ·
        refine ⟨8391602146620097771835741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594401431080065181223827 8391602146620097771835741)
        ·
          refine ⟨3146850804982536664438403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8391602146620097771835741 3146850804982536664438403)
          ·
            refine ⟨4720276207473804996657605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146850804982536664438403 4720276207473804996657605)
            ·
              refine ⟨885051788901338436873301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4720276207473804996657605 885051788901338436873301)
              ·
                refine ⟨10371700651187559807109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 885051788901338436873301 10371700651187559807109)
                ·
                  rfl

theorem cell20_68171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_68171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68171 prefixEnd_68171 := by exact prefixLift 68171
  have htrace : WordTrace (prefixWord ++ tailWord_68171) baseStart_68171 baseEnd_68171 := by
    simpa [prefixWord, tailWord_68171, baseEnd_68171] using wordTrace_append hprefix tailTrace_68171
  have hstable : (prefixWord ++ tailWord_68171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68171).length < 2 ^ (prefixWord ++ tailWord_68171).sum := by decide
  have hdescent : baseEnd_68171 < baseStart_68171 := by decide
  rcases family_descends (prefixWord ++ tailWord_68171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68195 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_68195 : Nat := 118140960795 + 68195 * 2 ^ 59
def prefixEnd_68195 : Nat := 4983230072969 + 3 ^ 40 * 68195 * 2
def baseEnd_68195 : Nat := 31126056207525262621229

theorem tailTrace_68195 : CollatzResearch.WordTrace tailWord_68195 prefixEnd_68195 31126056207525262621229 := by
  unfold tailWord_68195
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487275987948636623862039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1658183991965757749241359 2487275987948636623862039)
  ·
    refine ⟨3730913981922954935793059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2487275987948636623862039 3730913981922954935793059)
    ·
      refine ⟨5596370972884432403689589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3730913981922954935793059 5596370972884432403689589)
      ·
        refine ⟨524659778707915537845899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5596370972884432403689589 524659778707915537845899)
        ·
          refine ⟨786989668061873306768849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524659778707915537845899 786989668061873306768849)
          ·
            refine ⟨590242251046404980076637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786989668061873306768849 590242251046404980076637)
            ·
              refine ⟨221340844142401867528739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 590242251046404980076637 221340844142401867528739)
              ·
                refine ⟨332011266213602801293109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221340844142401867528739 332011266213602801293109)
                ·
                  refine ⟨31126056207525262621229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332011266213602801293109 31126056207525262621229)
                  ·
                    rfl

theorem cell20_68195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_68195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68195 prefixEnd_68195 := by exact prefixLift 68195
  have htrace : WordTrace (prefixWord ++ tailWord_68195) baseStart_68195 baseEnd_68195 := by
    simpa [prefixWord, tailWord_68195, baseEnd_68195] using wordTrace_append hprefix tailTrace_68195
  have hstable : (prefixWord ++ tailWord_68195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68195).length < 2 ^ (prefixWord ++ tailWord_68195).sum := by decide
  have hdescent : baseEnd_68195 < baseStart_68195 := by decide
  rcases family_descends (prefixWord ++ tailWord_68195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68263 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 3]
def baseStart_68263 : Nat := 118140960795 + 68263 * 2 ^ 59
def prefixEnd_68263 : Nat := 4983230072969 + 3 ^ 40 * 68263 * 2
def baseEnd_68263 : Nat := 31157093260419248354285

theorem tailTrace_68263 : CollatzResearch.WordTrace tailWord_68263 prefixEnd_68263 31157093260419248354285 := by
  unfold tailWord_68263
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489756151702284237337443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1659837434468189491558295 2489756151702284237337443)
  ·
    refine ⟨3734634227553426356006165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2489756151702284237337443 3734634227553426356006165)
    ·
      refine ⟨175060979416566860437789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3734634227553426356006165 175060979416566860437789)
      ·
        refine ⟨65647867281212572664171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175060979416566860437789 65647867281212572664171)
        ·
          refine ⟨98471800921818858996257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65647867281212572664171 98471800921818858996257)
          ·
            refine ⟨73853850691364144247193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98471800921818858996257 73853850691364144247193)
            ·
              refine ⟨55390388018523108185395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73853850691364144247193 55390388018523108185395)
              ·
                refine ⟨83085582027784662278093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55390388018523108185395 83085582027784662278093)
                ·
                  refine ⟨31157093260419248354285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83085582027784662278093 31157093260419248354285)
                  ·
                    rfl

theorem cell20_68263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 3].length) (baseStart_68263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68263 prefixEnd_68263 := by exact prefixLift 68263
  have htrace : WordTrace (prefixWord ++ tailWord_68263) baseStart_68263 baseEnd_68263 := by
    simpa [prefixWord, tailWord_68263, baseEnd_68263] using wordTrace_append hprefix tailTrace_68263
  have hstable : (prefixWord ++ tailWord_68263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68263).length < 2 ^ (prefixWord ++ tailWord_68263).sum := by decide
  have hdescent : baseEnd_68263 < baseStart_68263 := by decide
  rcases family_descends (prefixWord ++ tailWord_68263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68312 : List Nat := [2, 1, 2, 2, 3, 3, 1, 4, 2]
def baseStart_68312 : Nat := 118140960795 + 68312 * 2 ^ 59
def prefixEnd_68312 : Nat := 4983230072969 + 3 ^ 40 * 68312 * 2
def baseEnd_68312 : Nat := 31179458195592855720751

theorem tailTrace_68312 : CollatzResearch.WordTrace tailWord_68312 prefixEnd_68312 31179458195592855720751 := by
  unfold tailWord_68312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245771664262382802935595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1661028885683177070580793 1245771664262382802935595)
  ·
    refine ⟨1868657496393574204403393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1245771664262382802935595 1868657496393574204403393)
    ·
      refine ⟨1401493122295180653302545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1868657496393574204403393 1401493122295180653302545)
      ·
        refine ⟨1051119841721385489976909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1401493122295180653302545 1051119841721385489976909)
        ·
          refine ⟨394169940645519558741341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1051119841721385489976909 394169940645519558741341)
          ·
            refine ⟨147813727742069834528003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 394169940645519558741341 147813727742069834528003)
            ·
              refine ⟨221720591613104751792005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147813727742069834528003 221720591613104751792005)
              ·
                refine ⟨41572610927457140961001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221720591613104751792005 41572610927457140961001)
                ·
                  refine ⟨31179458195592855720751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41572610927457140961001 31179458195592855720751)
                  ·
                    rfl

theorem cell20_68312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_68312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68312 prefixEnd_68312 := by exact prefixLift 68312
  have htrace : WordTrace (prefixWord ++ tailWord_68312) baseStart_68312 baseEnd_68312 := by
    simpa [prefixWord, tailWord_68312, baseEnd_68312] using wordTrace_append hprefix tailTrace_68312
  have hstable : (prefixWord ++ tailWord_68312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68312).length < 2 ^ (prefixWord ++ tailWord_68312).sum := by decide
  have hdescent : baseEnd_68312 < baseStart_68312 := by decide
  rcases family_descends (prefixWord ++ tailWord_68312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68333 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_68333 : Nat := 118140960795 + 68333 * 2 ^ 59
def prefixEnd_68333 : Nat := 4983230072969 + 3 ^ 40 * 68333 * 2
def baseEnd_68333 : Nat := 31189043167810116020665

theorem tailTrace_68333 : CollatzResearch.WordTrace tailWord_68333 prefixEnd_68333 31189043167810116020665 := by
  unfold tailWord_68333
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492309261448686192385653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1661539507632457461590435 2492309261448686192385653)
  ·
    refine ⟨233653993260814330536155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2492309261448686192385653 233653993260814330536155)
    ·
      refine ⟨350480989891221495804233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233653993260814330536155 350480989891221495804233)
      ·
        refine ⟨262860742418416121853175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350480989891221495804233 262860742418416121853175)
        ·
          refine ⟨394291113627624182779763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262860742418416121853175 394291113627624182779763)
          ·
            refine ⟨591436670441436274169645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394291113627624182779763 591436670441436274169645)
            ·
              refine ⟨221788751415538602813617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 591436670441436274169645 221788751415538602813617)
              ·
                refine ⟨166341563561653952110213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221788751415538602813617 166341563561653952110213)
                ·
                  refine ⟨31189043167810116020665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166341563561653952110213 31189043167810116020665)
                  ·
                    rfl

theorem cell20_68333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_68333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68333 prefixEnd_68333 := by exact prefixLift 68333
  have htrace : WordTrace (prefixWord ++ tailWord_68333) baseStart_68333 baseEnd_68333 := by
    simpa [prefixWord, tailWord_68333, baseEnd_68333] using wordTrace_append hprefix tailTrace_68333
  have hstable : (prefixWord ++ tailWord_68333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68333).length < 2 ^ (prefixWord ++ tailWord_68333).sum := by decide
  have hdescent : baseEnd_68333 < baseStart_68333 := by decide
  rcases family_descends (prefixWord ++ tailWord_68333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68371 : List Nat := [1, 1, 1, 2, 1, 3, 3, 6, 2]
def baseStart_68371 : Nat := 118140960795 + 68371 * 2 ^ 59
def prefixEnd_68371 : Nat := 4983230072969 + 3 ^ 40 * 68371 * 2
def baseEnd_68371 : Nat := 31206387403250872753843

theorem tailTrace_68371 : CollatzResearch.WordTrace tailWord_68371 prefixEnd_68371 31206387403250872753843 := by
  unfold tailWord_68371
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493695235311018682268967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1662463490207345788179311 2493695235311018682268967)
  ·
    refine ⟨3740542852966528023403451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2493695235311018682268967 3740542852966528023403451)
    ·
      refine ⟨5610814279449792035105177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740542852966528023403451 5610814279449792035105177)
      ·
        refine ⟨4208110709587344026328883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5610814279449792035105177 4208110709587344026328883)
        ·
          refine ⟨6312166064381016039493325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208110709587344026328883 6312166064381016039493325)
          ·
            refine ⟨2367062274142881014809997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6312166064381016039493325 2367062274142881014809997)
            ·
              refine ⟨887648352803580380553749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2367062274142881014809997 887648352803580380553749)
              ·
                refine ⟨41608516537667830338457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 887648352803580380553749 41608516537667830338457)
                ·
                  refine ⟨31206387403250872753843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41608516537667830338457 31206387403250872753843)
                  ·
                    rfl

theorem cell20_68371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 2].length) (baseStart_68371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68371 prefixEnd_68371 := by exact prefixLift 68371
  have htrace : WordTrace (prefixWord ++ tailWord_68371) baseStart_68371 baseEnd_68371 := by
    simpa [prefixWord, tailWord_68371, baseEnd_68371] using wordTrace_append hprefix tailTrace_68371
  have hstable : (prefixWord ++ tailWord_68371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68371).length < 2 ^ (prefixWord ++ tailWord_68371).sum := by decide
  have hdescent : baseEnd_68371 < baseStart_68371 := by decide
  rcases family_descends (prefixWord ++ tailWord_68371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68405 : List Nat := [1, 3, 3, 1, 3, 3, 1, 3, 2]
def baseStart_68405 : Nat := 118140960795 + 68405 * 2 ^ 59
def prefixEnd_68405 : Nat := 4983230072969 + 3 ^ 40 * 68405 * 2
def baseEnd_68405 : Nat := 31221905929697865620371

theorem tailTrace_68405 : CollatzResearch.WordTrace tailWord_68405 prefixEnd_68405 31221905929697865620371 := by
  unfold tailWord_68405
  simp only [CollatzResearch.WordTrace]
  refine ⟨2494935317187842489006669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1663290211458561659337779 2494935317187842489006669)
  ·
    refine ⟨935600743945440933377501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2494935317187842489006669 935600743945440933377501)
    ·
      refine ⟨350850278979540350016563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 935600743945440933377501 350850278979540350016563)
      ·
        refine ⟨526275418469310525024845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350850278979540350016563 526275418469310525024845)
        ·
          refine ⟨197353281925991446884317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 526275418469310525024845 197353281925991446884317)
          ·
            refine ⟨74007480722246792581619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197353281925991446884317 74007480722246792581619)
            ·
              refine ⟨111011221083370188872429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74007480722246792581619 111011221083370188872429)
              ·
                refine ⟨41629207906263820827161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111011221083370188872429 41629207906263820827161)
                ·
                  refine ⟨31221905929697865620371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41629207906263820827161 31221905929697865620371)
                  ·
                    rfl

theorem cell20_68405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_68405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68405 prefixEnd_68405 := by exact prefixLift 68405
  have htrace : WordTrace (prefixWord ++ tailWord_68405) baseStart_68405 baseEnd_68405 := by
    simpa [prefixWord, tailWord_68405, baseEnd_68405] using wordTrace_append hprefix tailTrace_68405
  have hstable : (prefixWord ++ tailWord_68405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68405).length < 2 ^ (prefixWord ++ tailWord_68405).sum := by decide
  have hdescent : baseEnd_68405 < baseStart_68405 := by decide
  rcases family_descends (prefixWord ++ tailWord_68405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68422 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_68422 : Nat := 118140960795 + 68422 * 2 ^ 59
def prefixEnd_68422 : Nat := 4983230072969 + 3 ^ 40 * 68422 * 2
def baseEnd_68422 : Nat := 31229665192921362053635

theorem tailTrace_68422 : CollatzResearch.WordTrace tailWord_68422 prefixEnd_68422 31229665192921362053635 := by
  unfold tailWord_68422
  simp only [CollatzResearch.WordTrace]
  refine ⟨77986104941445449761735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1663703572084169594917013 77986104941445449761735)
  ·
    refine ⟨116979157412168174642603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77986104941445449761735 116979157412168174642603)
    ·
      refine ⟨175468736118252261963905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116979157412168174642603 175468736118252261963905)
      ·
        refine ⟨131601552088689196472929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175468736118252261963905 131601552088689196472929)
        ·
          refine ⟨98701164066516897354697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131601552088689196472929 98701164066516897354697)
          ·
            refine ⟨74025873049887673016023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98701164066516897354697 74025873049887673016023)
            ·
              refine ⟨111038809574831509524035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74025873049887673016023 111038809574831509524035)
              ·
                refine ⟨166558214362247264286053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111038809574831509524035 166558214362247264286053)
                ·
                  refine ⟨31229665192921362053635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166558214362247264286053 31229665192921362053635)
                  ·
                    rfl

theorem cell20_68422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_68422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68422 prefixEnd_68422 := by exact prefixLift 68422
  have htrace : WordTrace (prefixWord ++ tailWord_68422) baseStart_68422 baseEnd_68422 := by
    simpa [prefixWord, tailWord_68422, baseEnd_68422] using wordTrace_append hprefix tailTrace_68422
  have hstable : (prefixWord ++ tailWord_68422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68422).length < 2 ^ (prefixWord ++ tailWord_68422).sum := by decide
  have hdescent : baseEnd_68422 < baseStart_68422 := by decide
  rcases family_descends (prefixWord ++ tailWord_68422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68423 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 3]
def baseStart_68423 : Nat := 118140960795 + 68423 * 2 ^ 59
def prefixEnd_68423 : Nat := 4983230072969 + 3 ^ 40 * 68423 * 2
def baseEnd_68423 : Nat := 31230121620169803020297

theorem tailTrace_68423 : CollatzResearch.WordTrace tailWord_68423 prefixEnd_68423 31230121620169803020297 := by
  unfold tailWord_68423
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495591831122631563161923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1663727887415087708774615 2495591831122631563161923)
  ·
    refine ⟨3743387746683947344742885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495591831122631563161923 3743387746683947344742885)
    ·
      refine ⟨701885202503240127139291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3743387746683947344742885 701885202503240127139291)
      ·
        refine ⟨1052827803754860190708937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701885202503240127139291 1052827803754860190708937)
        ·
          refine ⟨789620852816145143031703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1052827803754860190708937 789620852816145143031703)
          ·
            refine ⟨1184431279224217714547555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789620852816145143031703 1184431279224217714547555)
            ·
              refine ⟨1776646918836326571821333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184431279224217714547555 1776646918836326571821333)
              ·
                refine ⟨83280324320452808054125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1776646918836326571821333 83280324320452808054125)
                ·
                  refine ⟨31230121620169803020297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83280324320452808054125 31230121620169803020297)
                  ·
                    rfl

theorem cell20_68423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_68423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68423 prefixEnd_68423 := by exact prefixLift 68423
  have htrace : WordTrace (prefixWord ++ tailWord_68423) baseStart_68423 baseEnd_68423 := by
    simpa [prefixWord, tailWord_68423, baseEnd_68423] using wordTrace_append hprefix tailTrace_68423
  have hstable : (prefixWord ++ tailWord_68423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68423).length < 2 ^ (prefixWord ++ tailWord_68423).sum := by decide
  have hdescent : baseEnd_68423 < baseStart_68423 := by decide
  rcases family_descends (prefixWord ++ tailWord_68423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68436 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_68436 : Nat := 118140960795 + 68436 * 2 ^ 59
def prefixEnd_68436 : Nat := 4983230072969 + 3 ^ 40 * 68436 * 2
def baseEnd_68436 : Nat := 31236055174399535586911

theorem tailTrace_68436 : CollatzResearch.WordTrace tailWord_68436 prefixEnd_68436 31236055174399535586911 := by
  unfold tailWord_68436
  simp only [CollatzResearch.WordTrace]
  refine ⟨1248032990037767391692581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1664043986717023188923441 1248032990037767391692581)
  ·
    refine ⟨234006185632081385942359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1248032990037767391692581 234006185632081385942359)
    ·
      refine ⟨351009278448122078913539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234006185632081385942359 351009278448122078913539)
      ·
        refine ⟨526513917672183118370309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351009278448122078913539 526513917672183118370309)
        ·
          refine ⟨98721359563534334694433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 526513917672183118370309 98721359563534334694433)
          ·
            refine ⟨74041019672650751020825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98721359563534334694433 74041019672650751020825)
            ·
              refine ⟨55530764754488063265619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74041019672650751020825 55530764754488063265619)
              ·
                refine ⟨83296147131732094898429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55530764754488063265619 83296147131732094898429)
                ·
                  refine ⟨31236055174399535586911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83296147131732094898429 31236055174399535586911)
                  ·
                    rfl

theorem cell20_68436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_68436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68436 prefixEnd_68436 := by exact prefixLift 68436
  have htrace : WordTrace (prefixWord ++ tailWord_68436) baseStart_68436 baseEnd_68436 := by
    simpa [prefixWord, tailWord_68436, baseEnd_68436] using wordTrace_append hprefix tailTrace_68436
  have hstable : (prefixWord ++ tailWord_68436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68436).length < 2 ^ (prefixWord ++ tailWord_68436).sum := by decide
  have hdescent : baseEnd_68436 < baseStart_68436 := by decide
  rcases family_descends (prefixWord ++ tailWord_68436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68519 : List Nat := [1, 1, 6, 1, 3, 1, 2, 3, 2]
def baseStart_68519 : Nat := 118140960795 + 68519 * 2 ^ 59
def prefixEnd_68519 : Nat := 4983230072969 + 3 ^ 40 * 68519 * 2
def baseEnd_68519 : Nat := 31273938636020135819905

theorem tailTrace_68519 : CollatzResearch.WordTrace tailWord_68519 prefixEnd_68519 31273938636020135819905 := by
  unfold tailWord_68519
  simp only [CollatzResearch.WordTrace]
  refine ⟨2499093238774839958656611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1666062159183226639104407 2499093238774839958656611)
  ·
    refine ⟨3748639858162259937984917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2499093238774839958656611 3748639858162259937984917)
    ·
      refine ⟨175717493351355934593043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3748639858162259937984917 175717493351355934593043)
      ·
        refine ⟨263576240027033901889565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175717493351355934593043 263576240027033901889565)
        ·
          refine ⟨98841090010137713208587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263576240027033901889565 98841090010137713208587)
          ·
            refine ⟨148261635015206569812881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98841090010137713208587 148261635015206569812881)
            ·
              refine ⟨111196226261404927359661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148261635015206569812881 111196226261404927359661)
              ·
                refine ⟨41698584848026847759873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111196226261404927359661 41698584848026847759873)
                ·
                  refine ⟨31273938636020135819905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41698584848026847759873 31273938636020135819905)
                  ·
                    rfl

theorem cell20_68519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 2].length) (baseStart_68519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68519 prefixEnd_68519 := by exact prefixLift 68519
  have htrace : WordTrace (prefixWord ++ tailWord_68519) baseStart_68519 baseEnd_68519 := by
    simpa [prefixWord, tailWord_68519, baseEnd_68519] using wordTrace_append hprefix tailTrace_68519
  have hstable : (prefixWord ++ tailWord_68519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68519).length < 2 ^ (prefixWord ++ tailWord_68519).sum := by decide
  have hdescent : baseEnd_68519 < baseStart_68519 := by decide
  rcases family_descends (prefixWord ++ tailWord_68519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68537 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_68537 : Nat := 118140960795 + 68537 * 2 ^ 59
def prefixEnd_68537 : Nat := 4983230072969 + 3 ^ 40 * 68537 * 2
def baseEnd_68537 : Nat := 31282154326492073219831

theorem tailTrace_68537 : CollatzResearch.WordTrace tailWord_68537 prefixEnd_68537 31282154326492073219831 := by
  unfold tailWord_68537
  simp only [CollatzResearch.WordTrace]
  refine ⟨2499749752709629032811865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1666499835139752688541243 2499749752709629032811865)
  ·
    refine ⟨1874812314532221774608899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2499749752709629032811865 1874812314532221774608899)
    ·
      refine ⟨2812218471798332661913349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874812314532221774608899 2812218471798332661913349)
      ·
        refine ⟨527290963462187374108753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2812218471798332661913349 527290963462187374108753)
        ·
          refine ⟨395468222596640530581565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527290963462187374108753 395468222596640530581565)
          ·
            refine ⟨148300583473740198968087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 395468222596640530581565 148300583473740198968087)
            ·
              refine ⟨222450875210610298452131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148300583473740198968087 222450875210610298452131)
              ·
                refine ⟨333676312815915447678197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222450875210610298452131 333676312815915447678197)
                ·
                  refine ⟨31282154326492073219831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 333676312815915447678197 31282154326492073219831)
                  ·
                    rfl

theorem cell20_68537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_68537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68537 prefixEnd_68537 := by exact prefixLift 68537
  have htrace : WordTrace (prefixWord ++ tailWord_68537) baseStart_68537 baseEnd_68537 := by
    simpa [prefixWord, tailWord_68537, baseEnd_68537] using wordTrace_append hprefix tailTrace_68537
  have hstable : (prefixWord ++ tailWord_68537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68537).length < 2 ^ (prefixWord ++ tailWord_68537).sum := by decide
  have hdescent : baseEnd_68537 < baseStart_68537 := by decide
  rcases family_descends (prefixWord ++ tailWord_68537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68544 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_68544 : Nat := 118140960795 + 68544 * 2 ^ 59
def prefixEnd_68544 : Nat := 4983230072969 + 3 ^ 40 * 68544 * 2
def baseEnd_68544 : Nat := 31285349317231159986469

theorem tailTrace_68544 : CollatzResearch.WordTrace tailWord_68544 prefixEnd_68544 31285349317231159986469 := by
  unfold tailWord_68544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250002531842134614158343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1666670042456179485544457 1250002531842134614158343)
  ·
    refine ⟨1875003797763201921237515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250002531842134614158343 1875003797763201921237515)
    ·
      refine ⟨2812505696644802881856273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875003797763201921237515 2812505696644802881856273)
      ·
        refine ⟨2109379272483602161392205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2812505696644802881856273 2109379272483602161392205)
        ·
          refine ⟨791017227181350810522077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2109379272483602161392205 791017227181350810522077)
          ·
            refine ⟨296631460193006553945779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 791017227181350810522077 296631460193006553945779)
            ·
              refine ⟨444947190289509830918669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296631460193006553945779 444947190289509830918669)
              ·
                refine ⟨166855196358566186594501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 444947190289509830918669 166855196358566186594501)
                ·
                  refine ⟨31285349317231159986469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166855196358566186594501 31285349317231159986469)
                  ·
                    rfl

theorem cell20_68544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_68544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68544 prefixEnd_68544 := by exact prefixLift 68544
  have htrace : WordTrace (prefixWord ++ tailWord_68544) baseStart_68544 baseEnd_68544 := by
    simpa [prefixWord, tailWord_68544, baseEnd_68544] using wordTrace_append hprefix tailTrace_68544
  have hstable : (prefixWord ++ tailWord_68544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68544).length < 2 ^ (prefixWord ++ tailWord_68544).sum := by decide
  have hdescent : baseEnd_68544 < baseStart_68544 := by decide
  rcases family_descends (prefixWord ++ tailWord_68544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68568 : List Nat := [2, 1, 2, 2, 2, 3, 4, 4]
def baseStart_68568 : Nat := 118140960795 + 68568 * 2 ^ 59
def prefixEnd_68568 : Nat := 4983230072969 + 3 ^ 40 * 68568 * 2
def baseEnd_68568 : Nat := 10432101190397914395457

theorem tailTrace_68568 : CollatzResearch.WordTrace tailWord_68568 prefixEnd_68568 10432101190397914395457 := by
  unfold tailWord_68568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250440207798660663595179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1667253610398214218126905 1250440207798660663595179)
  ·
    refine ⟨1875660311697990995392769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250440207798660663595179 1875660311697990995392769)
    ·
      refine ⟨1406745233773493246544577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1875660311697990995392769 1406745233773493246544577)
      ·
        refine ⟨1055058925330119934908433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1406745233773493246544577 1055058925330119934908433)
        ·
          refine ⟨791294193997589951181325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055058925330119934908433 791294193997589951181325)
          ·
            refine ⟨296735322749096231692997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 791294193997589951181325 296735322749096231692997)
            ·
              refine ⟨55637873015455543442437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 296735322749096231692997 55637873015455543442437)
              ·
                refine ⟨10432101190397914395457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55637873015455543442437 10432101190397914395457)
                ·
                  rfl

theorem cell20_68568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_68568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68568 prefixEnd_68568 := by exact prefixLift 68568
  have htrace : WordTrace (prefixWord ++ tailWord_68568) baseStart_68568 baseEnd_68568 := by
    simpa [prefixWord, tailWord_68568, baseEnd_68568] using wordTrace_append hprefix tailTrace_68568
  have hstable : (prefixWord ++ tailWord_68568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68568).length < 2 ^ (prefixWord ++ tailWord_68568).sum := by decide
  have hdescent : baseEnd_68568 < baseStart_68568 := by decide
  rcases family_descends (prefixWord ++ tailWord_68568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68609 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 3]
def baseStart_68609 : Nat := 118140960795 + 68609 * 2 ^ 59
def prefixEnd_68609 : Nat := 4983230072969 + 3 ^ 40 * 68609 * 2
def baseEnd_68609 : Nat := 31315017088379822819537

theorem tailTrace_68609 : CollatzResearch.WordTrace tailWord_68609 prefixEnd_68609 31315017088379822819537 := by
  unfold tailWord_68609
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502375808448785329432881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1668250538965856886288587 2502375808448785329432881)
  ·
    refine ⟨1876781856336588997074661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2502375808448785329432881 1876781856336588997074661)
    ·
      refine ⟨351896598063110436951499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1876781856336588997074661 351896598063110436951499)
      ·
        refine ⟨527844897094665655427249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351896598063110436951499 527844897094665655427249)
        ·
          refine ⟨395883672820999241570437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527844897094665655427249 395883672820999241570437)
          ·
            refine ⟨74228188653937357794457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 395883672820999241570437 74228188653937357794457)
            ·
              refine ⟨55671141490453018345843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74228188653937357794457 55671141490453018345843)
              ·
                refine ⟨83506712235679527518765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55671141490453018345843 83506712235679527518765)
                ·
                  refine ⟨31315017088379822819537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83506712235679527518765 31315017088379822819537)
                  ·
                    rfl

theorem cell20_68609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_68609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68609 prefixEnd_68609 := by exact prefixLift 68609
  have htrace : WordTrace (prefixWord ++ tailWord_68609) baseStart_68609 baseEnd_68609 := by
    simpa [prefixWord, tailWord_68609, baseEnd_68609] using wordTrace_append hprefix tailTrace_68609
  have hstable : (prefixWord ++ tailWord_68609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68609).length < 2 ^ (prefixWord ++ tailWord_68609).sum := by decide
  have hdescent : baseEnd_68609 < baseStart_68609 := by decide
  rcases family_descends (prefixWord ++ tailWord_68609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68613 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 3]
def baseStart_68613 : Nat := 118140960795 + 68613 * 2 ^ 59
def prefixEnd_68613 : Nat := 4983230072969 + 3 ^ 40 * 68613 * 2
def baseEnd_68613 : Nat := 31316842797373586686187

theorem tailTrace_68613 : CollatzResearch.WordTrace tailWord_68613 prefixEnd_68613 31316842797373586686187 := by
  unfold tailWord_68613
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502521700434294012578493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1668347800289529341718995 2502521700434294012578493)
  ·
    refine ⟨938445637662860254716935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2502521700434294012578493 938445637662860254716935)
    ·
      refine ⟨1407668456494290382075403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 938445637662860254716935 1407668456494290382075403)
      ·
        refine ⟨2111502684741435573113105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407668456494290382075403 2111502684741435573113105)
        ·
          refine ⟨1583627013556076679834829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2111502684741435573113105 1583627013556076679834829)
          ·
            refine ⟨593860130083528754938061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1583627013556076679834829 593860130083528754938061)
            ·
              refine ⟨222697548781323283101773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 593860130083528754938061 222697548781323283101773)
              ·
                refine ⟨83511580792996231163165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222697548781323283101773 83511580792996231163165)
                ·
                  refine ⟨31316842797373586686187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83511580792996231163165 31316842797373586686187)
                  ·
                    rfl

theorem cell20_68613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_68613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68613 prefixEnd_68613 := by exact prefixLift 68613
  have htrace : WordTrace (prefixWord ++ tailWord_68613) baseStart_68613 baseEnd_68613 := by
    simpa [prefixWord, tailWord_68613, baseEnd_68613] using wordTrace_append hprefix tailTrace_68613
  have hstable : (prefixWord ++ tailWord_68613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68613).length < 2 ^ (prefixWord ++ tailWord_68613).sum := by decide
  have hdescent : baseEnd_68613 < baseStart_68613 := by decide
  rcases family_descends (prefixWord ++ tailWord_68613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68647 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 3]
def baseStart_68647 : Nat := 118140960795 + 68647 * 2 ^ 59
def prefixEnd_68647 : Nat := 4983230072969 + 3 ^ 40 * 68647 * 2
def baseEnd_68647 : Nat := 31332361323820579552715

theorem tailTrace_68647 : CollatzResearch.WordTrace tailWord_68647 prefixEnd_68647 31332361323820579552715 := by
  unfold tailWord_68647
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503761782311117819316195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1669174521540745212877463 2503761782311117819316195)
  ·
    refine ⟨3755642673466676728974293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2503761782311117819316195 3755642673466676728974293)
    ·
      refine ⟨88022875159375235835335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3755642673466676728974293 88022875159375235835335)
      ·
        refine ⟨132034312739062853753003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88022875159375235835335 132034312739062853753003)
        ·
          refine ⟨198051469108594280629505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132034312739062853753003 198051469108594280629505)
          ·
            refine ⟨148538601831445710472129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198051469108594280629505 148538601831445710472129)
            ·
              refine ⟨111403951373584282854097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148538601831445710472129 111403951373584282854097)
              ·
                refine ⟨83552963530188212140573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111403951373584282854097 83552963530188212140573)
                ·
                  refine ⟨31332361323820579552715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83552963530188212140573 31332361323820579552715)
                  ·
                    rfl

theorem cell20_68647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_68647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68647 prefixEnd_68647 := by exact prefixLift 68647
  have htrace : WordTrace (prefixWord ++ tailWord_68647) baseStart_68647 baseEnd_68647 := by
    simpa [prefixWord, tailWord_68647, baseEnd_68647] using wordTrace_append hprefix tailTrace_68647
  have hstable : (prefixWord ++ tailWord_68647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68647).length < 2 ^ (prefixWord ++ tailWord_68647).sum := by decide
  have hdescent : baseEnd_68647 < baseStart_68647 := by decide
  rcases family_descends (prefixWord ++ tailWord_68647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68650 : List Nat := [3, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_68650 : Nat := 118140960795 + 68650 * 2 ^ 59
def prefixEnd_68650 : Nat := 4983230072969 + 3 ^ 40 * 68650 * 2
def baseEnd_68650 : Nat := 31333730605565902452703

theorem tailTrace_68650 : CollatzResearch.WordTrace tailWord_68650 prefixEnd_68650 31333730605565902452703 := by
  unfold tailWord_68650
  simp only [CollatzResearch.WordTrace]
  refine ⟨625967800325062332918851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1669247467533499554450269 625967800325062332918851)
  ·
    refine ⟨938951700487593499378277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 625967800325062332918851 938951700487593499378277)
    ·
      refine ⟨176053443841423781133427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 938951700487593499378277 176053443841423781133427)
      ·
        refine ⟨264080165762135671700141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176053443841423781133427 264080165762135671700141)
        ·
          refine ⟨99030062160800876887553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264080165762135671700141 99030062160800876887553)
          ·
            refine ⟨74272546620600657665665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99030062160800876887553 74272546620600657665665)
            ·
              refine ⟨55704409965450493249249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74272546620600657665665 55704409965450493249249)
              ·
                refine ⟨41778307474087869936937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55704409965450493249249 41778307474087869936937)
                ·
                  refine ⟨31333730605565902452703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41778307474087869936937 31333730605565902452703)
                  ·
                    rfl

theorem cell20_68650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_68650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68650 prefixEnd_68650 := by exact prefixLift 68650
  have htrace : WordTrace (prefixWord ++ tailWord_68650) baseStart_68650 baseEnd_68650 := by
    simpa [prefixWord, tailWord_68650, baseEnd_68650] using wordTrace_append hprefix tailTrace_68650
  have hstable : (prefixWord ++ tailWord_68650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68650).length < 2 ^ (prefixWord ++ tailWord_68650).sum := by decide
  have hdescent : baseEnd_68650 < baseStart_68650 := by decide
  rcases family_descends (prefixWord ++ tailWord_68650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68651 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 3]
def baseStart_68651 : Nat := 118140960795 + 68651 * 2 ^ 59
def prefixEnd_68651 : Nat := 4983230072969 + 3 ^ 40 * 68651 * 2
def baseEnd_68651 : Nat := 31334187032814343419365

theorem tailTrace_68651 : CollatzResearch.WordTrace tailWord_68651 prefixEnd_68651 31334187032814343419365 := by
  unfold tailWord_68651
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503907674296626502461807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1669271782864417668307871 2503907674296626502461807)
  ·
    refine ⟨3755861511444939753692711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2503907674296626502461807 3755861511444939753692711)
    ·
      refine ⟨5633792267167409630539067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3755861511444939753692711 5633792267167409630539067)
      ·
        refine ⟨8450688400751114445808601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5633792267167409630539067 8450688400751114445808601)
        ·
          refine ⟨6338016300563335834356451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8450688400751114445808601 6338016300563335834356451)
          ·
            refine ⟨9507024450845003751534677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338016300563335834356451 9507024450845003751534677)
            ·
              refine ⟨111410442783339887713297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 9507024450845003751534677 111410442783339887713297)
              ·
                refine ⟨83557832087504915784973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111410442783339887713297 83557832087504915784973)
                ·
                  refine ⟨31334187032814343419365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83557832087504915784973 31334187032814343419365)
                  ·
                    rfl

theorem cell20_68651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_68651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68651 prefixEnd_68651 := by exact prefixLift 68651
  have htrace : WordTrace (prefixWord ++ tailWord_68651) baseStart_68651 baseEnd_68651 := by
    simpa [prefixWord, tailWord_68651, baseEnd_68651] using wordTrace_append hprefix tailTrace_68651
  have hstable : (prefixWord ++ tailWord_68651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68651).length < 2 ^ (prefixWord ++ tailWord_68651).sum := by decide
  have hdescent : baseEnd_68651 < baseStart_68651 := by decide
  rcases family_descends (prefixWord ++ tailWord_68651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68654 : List Nat := [4, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_68654 : Nat := 118140960795 + 68654 * 2 ^ 59
def prefixEnd_68654 : Nat := 4983230072969 + 3 ^ 40 * 68654 * 2
def baseEnd_68654 : Nat := 31335556314559666319353

theorem tailTrace_68654 : CollatzResearch.WordTrace tailWord_68654 prefixEnd_68654 31335556314559666319353 := by
  unfold tailWord_68654
  simp only [CollatzResearch.WordTrace]
  refine ⟨313002136660719751852627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1669344728857172009880677 313002136660719751852627)
  ·
    refine ⟨469503204991079627778941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 313002136660719751852627 469503204991079627778941)
    ·
      refine ⟨176063701871654860417103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 469503204991079627778941 176063701871654860417103)
      ·
        refine ⟨264095552807482290625655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176063701871654860417103 264095552807482290625655)
        ·
          refine ⟨396143329211223435938483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264095552807482290625655 396143329211223435938483)
          ·
            refine ⟨594214993816835153907725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396143329211223435938483 594214993816835153907725)
            ·
              refine ⟨222830622681313182715397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594214993816835153907725 222830622681313182715397)
              ·
                refine ⟨41780741752746221759137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222830622681313182715397 41780741752746221759137)
                ·
                  refine ⟨31335556314559666319353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41780741752746221759137 31335556314559666319353)
                  ·
                    rfl

theorem cell20_68654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_68654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68654 prefixEnd_68654 := by exact prefixLift 68654
  have htrace : WordTrace (prefixWord ++ tailWord_68654) baseStart_68654 baseEnd_68654 := by
    simpa [prefixWord, tailWord_68654, baseEnd_68654] using wordTrace_append hprefix tailTrace_68654
  have hstable : (prefixWord ++ tailWord_68654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68654).length < 2 ^ (prefixWord ++ tailWord_68654).sum := by decide
  have hdescent : baseEnd_68654 < baseStart_68654 := by decide
  rcases family_descends (prefixWord ++ tailWord_68654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68658 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_68658 : Nat := 118140960795 + 68658 * 2 ^ 59
def prefixEnd_68658 : Nat := 4983230072969 + 3 ^ 40 * 68658 * 2
def baseEnd_68658 : Nat := 31337382023553430186003

theorem tailTrace_68658 : CollatzResearch.WordTrace tailWord_68658 prefixEnd_68658 31337382023553430186003 := by
  unfold tailWord_68658
  simp only [CollatzResearch.WordTrace]
  refine ⟨626040746317816674491657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1669441990180844465311085 626040746317816674491657)
  ·
    refine ⟨469530559738362505868743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 626040746317816674491657 469530559738362505868743)
    ·
      refine ⟨704295839607543758803115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469530559738362505868743 704295839607543758803115)
      ·
        refine ⟨1056443759411315638204673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704295839607543758803115 1056443759411315638204673)
        ·
          refine ⟨792332819558486728653505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1056443759411315638204673 792332819558486728653505)
          ·
            refine ⟨594249614668865046490129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792332819558486728653505 594249614668865046490129)
            ·
              refine ⟨445687211001648784867597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594249614668865046490129 445687211001648784867597)
              ·
                refine ⟨167132704125618294325349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445687211001648784867597 167132704125618294325349)
                ·
                  refine ⟨31337382023553430186003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167132704125618294325349 31337382023553430186003)
                  ·
                    rfl

theorem cell20_68658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_68658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68658 prefixEnd_68658 := by exact prefixLift 68658
  have htrace : WordTrace (prefixWord ++ tailWord_68658) baseStart_68658 baseEnd_68658 := by
    simpa [prefixWord, tailWord_68658, baseEnd_68658] using wordTrace_append hprefix tailTrace_68658
  have hstable : (prefixWord ++ tailWord_68658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68658).length < 2 ^ (prefixWord ++ tailWord_68658).sum := by decide
  have hdescent : baseEnd_68658 < baseStart_68658 := by decide
  rcases family_descends (prefixWord ++ tailWord_68658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68678 : List Nat := [6, 1, 1, 1, 1, 3, 3, 4]
def baseStart_68678 : Nat := 118140960795 + 68678 * 2 ^ 59
def prefixEnd_68678 : Nat := 4983230072969 + 3 ^ 40 * 68678 * 2
def baseEnd_68678 : Nat := 10448836856174083173085

theorem tailTrace_68678 : CollatzResearch.WordTrace tailWord_68678 prefixEnd_68678 10448836856174083173085 := by
  unfold tailWord_68678
  simp only [CollatzResearch.WordTrace]
  refine ⟨78277888912462816052959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1669928296799206742463125 78277888912462816052959)
  ·
    refine ⟨117416833368694224079439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78277888912462816052959 117416833368694224079439)
    ·
      refine ⟨176125250053041336119159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117416833368694224079439 176125250053041336119159)
      ·
        refine ⟨264187875079562004178739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176125250053041336119159 264187875079562004178739)
        ·
          refine ⟨396281812619343006268109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264187875079562004178739 396281812619343006268109)
          ·
            refine ⟨148605679732253627350541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396281812619343006268109 148605679732253627350541)
            ·
              refine ⟨55727129899595110256453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148605679732253627350541 55727129899595110256453)
              ·
                refine ⟨10448836856174083173085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55727129899595110256453 10448836856174083173085)
                ·
                  rfl

theorem cell20_68678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_68678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68678 prefixEnd_68678 := by exact prefixLift 68678
  have htrace : WordTrace (prefixWord ++ tailWord_68678) baseStart_68678 baseEnd_68678 := by
    simpa [prefixWord, tailWord_68678, baseEnd_68678] using wordTrace_append hprefix tailTrace_68678
  have hstable : (prefixWord ++ tailWord_68678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68678).length < 2 ^ (prefixWord ++ tailWord_68678).sum := by decide
  have hdescent : baseEnd_68678 < baseStart_68678 := by decide
  rcases family_descends (prefixWord ++ tailWord_68678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68702 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_68702 : Nat := 118140960795 + 68702 * 2 ^ 59
def prefixEnd_68702 : Nat := 4983230072969 + 3 ^ 40 * 68702 * 2
def baseEnd_68702 : Nat := 31357464822484832719157

theorem tailTrace_68702 : CollatzResearch.WordTrace tailWord_68702 prefixEnd_68702 31357464822484832719157 := by
  unfold tailWord_68702
  simp only [CollatzResearch.WordTrace]
  refine ⟨313220974638982776571045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1670511864741241475045573 313220974638982776571045)
  ·
    refine ⟨58728932744809270607071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 313220974638982776571045 58728932744809270607071)
    ·
      refine ⟨88093399117213905910607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58728932744809270607071 88093399117213905910607)
      ·
        refine ⟨132140098675820858865911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88093399117213905910607 132140098675820858865911)
        ·
          refine ⟨198210148013731288298867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132140098675820858865911 198210148013731288298867)
          ·
            refine ⟨297315222020596932448301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198210148013731288298867 297315222020596932448301)
            ·
              refine ⟨111493208257723849668113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297315222020596932448301 111493208257723849668113)
              ·
                refine ⟨83619906193292887251085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111493208257723849668113 83619906193292887251085)
                ·
                  refine ⟨31357464822484832719157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83619906193292887251085 31357464822484832719157)
                  ·
                    rfl

theorem cell20_68702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_68702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68702 prefixEnd_68702 := by exact prefixLift 68702
  have htrace : WordTrace (prefixWord ++ tailWord_68702) baseStart_68702 baseEnd_68702 := by
    simpa [prefixWord, tailWord_68702, baseEnd_68702] using wordTrace_append hprefix tailTrace_68702
  have hstable : (prefixWord ++ tailWord_68702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68702).length < 2 ^ (prefixWord ++ tailWord_68702).sum := by decide
  have hdescent : baseEnd_68702 < baseStart_68702 := by decide
  rcases family_descends (prefixWord ++ tailWord_68702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68706 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_68706 : Nat := 118140960795 + 68706 * 2 ^ 59
def prefixEnd_68706 : Nat := 4983230072969 + 3 ^ 40 * 68706 * 2
def baseEnd_68706 : Nat := 31359290531478596585807

theorem tailTrace_68706 : CollatzResearch.WordTrace tailWord_68706 prefixEnd_68706 31359290531478596585807 := by
  unfold tailWord_68706
  simp only [CollatzResearch.WordTrace]
  refine ⟨626478422274342723928493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1670609126064913930475981 626478422274342723928493)
  ·
    refine ⟨234929408352878521473185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 626478422274342723928493 234929408352878521473185)
    ·
      refine ⟨176197056264658891104889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234929408352878521473185 176197056264658891104889)
      ·
        refine ⟨132147792198494168328667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176197056264658891104889 132147792198494168328667)
        ·
          refine ⟨198221688297741252493001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132147792198494168328667 198221688297741252493001)
          ·
            refine ⟨148666266223305939369751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198221688297741252493001 148666266223305939369751)
            ·
              refine ⟨222999399334958909054627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148666266223305939369751 222999399334958909054627)
              ·
                refine ⟨334499099002438363581941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222999399334958909054627 334499099002438363581941)
                ·
                  refine ⟨31359290531478596585807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334499099002438363581941 31359290531478596585807)
                  ·
                    rfl

theorem cell20_68706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_68706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68706 prefixEnd_68706 := by exact prefixLift 68706
  have htrace : WordTrace (prefixWord ++ tailWord_68706) baseStart_68706 baseEnd_68706 := by
    simpa [prefixWord, tailWord_68706, baseEnd_68706] using wordTrace_append hprefix tailTrace_68706
  have hstable : (prefixWord ++ tailWord_68706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68706).length < 2 ^ (prefixWord ++ tailWord_68706).sum := by decide
  have hdescent : baseEnd_68706 < baseStart_68706 := by decide
  rcases family_descends (prefixWord ++ tailWord_68706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68713 : List Nat := [1, 2, 1, 1, 1, 6, 2, 4, 2]
def baseStart_68713 : Nat := 118140960795 + 68713 * 2 ^ 59
def prefixEnd_68713 : Nat := 4983230072969 + 3 ^ 40 * 68713 * 2
def baseEnd_68713 : Nat := 31362485522217683352445

theorem tailTrace_68713 : CollatzResearch.WordTrace tailWord_68713 prefixEnd_68713 31362485522217683352445 := by
  unfold tailWord_68713
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506169000072011091218793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1670779333381340727479195 2506169000072011091218793)
  ·
    refine ⟨1879626750054008318414095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2506169000072011091218793 1879626750054008318414095)
    ·
      refine ⟨2819440125081012477621143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879626750054008318414095 2819440125081012477621143)
      ·
        refine ⟨4229160187621518716431715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819440125081012477621143 4229160187621518716431715)
        ·
          refine ⟨6343740281432278074647573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4229160187621518716431715 6343740281432278074647573)
          ·
            refine ⟨297362825692138034749105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6343740281432278074647573 297362825692138034749105)
            ·
              refine ⟨223022119269103526061829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297362825692138034749105 223022119269103526061829)
              ·
                refine ⟨41816647362956911136593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223022119269103526061829 41816647362956911136593)
                ·
                  refine ⟨31362485522217683352445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41816647362956911136593 31362485522217683352445)
                  ·
                    rfl

theorem cell20_68713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_68713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68713 prefixEnd_68713 := by exact prefixLift 68713
  have htrace : WordTrace (prefixWord ++ tailWord_68713) baseStart_68713 baseEnd_68713 := by
    simpa [prefixWord, tailWord_68713, baseEnd_68713] using wordTrace_append hprefix tailTrace_68713
  have hstable : (prefixWord ++ tailWord_68713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68713).length < 2 ^ (prefixWord ++ tailWord_68713).sum := by decide
  have hdescent : baseEnd_68713 < baseStart_68713 := by decide
  rcases family_descends (prefixWord ++ tailWord_68713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68737 : List Nat := [1, 2, 4, 2, 2, 3, 2, 4]
def baseStart_68737 : Nat := 118140960795 + 68737 * 2 ^ 59
def prefixEnd_68737 : Nat := 4983230072969 + 3 ^ 40 * 68737 * 2
def baseEnd_68737 : Nat := 10457813258726755517449

theorem tailTrace_68737 : CollatzResearch.WordTrace tailWord_68737 prefixEnd_68737 10457813258726755517449 := by
  unfold tailWord_68737
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507044351985063190092465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1671362901323375460061643 2507044351985063190092465)
  ·
    refine ⟨1880283263988797392569349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2507044351985063190092465 1880283263988797392569349)
    ·
      refine ⟨352553111997899511106753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1880283263988797392569349 352553111997899511106753)
      ·
        refine ⟨264414833998424633330065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352553111997899511106753 264414833998424633330065)
        ·
          refine ⟨198311125498818474997549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264414833998424633330065 198311125498818474997549)
          ·
            refine ⟨74366672062056928124081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198311125498818474997549 74366672062056928124081)
            ·
              refine ⟨55775004046542696093061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74366672062056928124081 55775004046542696093061)
              ·
                refine ⟨10457813258726755517449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55775004046542696093061 10457813258726755517449)
                ·
                  rfl

theorem cell20_68737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_68737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68737 prefixEnd_68737 := by exact prefixLift 68737
  have htrace : WordTrace (prefixWord ++ tailWord_68737) baseStart_68737 baseEnd_68737 := by
    simpa [prefixWord, tailWord_68737, baseEnd_68737] using wordTrace_append hprefix tailTrace_68737
  have hstable : (prefixWord ++ tailWord_68737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68737).length < 2 ^ (prefixWord ++ tailWord_68737).sum := by decide
  have hdescent : baseEnd_68737 < baseStart_68737 := by decide
  rcases family_descends (prefixWord ++ tailWord_68737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68755 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_68755 : Nat := 118140960795 + 68755 * 2 ^ 59
def prefixEnd_68755 : Nat := 4983230072969 + 3 ^ 40 * 68755 * 2
def baseEnd_68755 : Nat := 31381655466652203952273

theorem tailTrace_68755 : CollatzResearch.WordTrace tailWord_68755 prefixEnd_68755 31381655466652203952273 := by
  unfold tailWord_68755
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507700865919852264247719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1671800577279901509498479 2507700865919852264247719)
  ·
    refine ⟨3761551298879778396371579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2507700865919852264247719 3761551298879778396371579)
    ·
      refine ⟨5642326948319667594557369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761551298879778396371579 5642326948319667594557369)
      ·
        refine ⟨4231745211239750695918027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5642326948319667594557369 4231745211239750695918027)
        ·
          refine ⟨6347617816859626043877041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231745211239750695918027 6347617816859626043877041)
          ·
            refine ⟨4760713362644719532907781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6347617816859626043877041 4760713362644719532907781)
            ·
              refine ⟨892633755495884912420209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4760713362644719532907781 892633755495884912420209)
              ·
                refine ⟨669475316621913684315157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892633755495884912420209 669475316621913684315157)
                ·
                  refine ⟨31381655466652203952273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 669475316621913684315157 31381655466652203952273)
                  ·
                    rfl

theorem cell20_68755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_68755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68755 prefixEnd_68755 := by exact prefixLift 68755
  have htrace : WordTrace (prefixWord ++ tailWord_68755) baseStart_68755 baseEnd_68755 := by
    simpa [prefixWord, tailWord_68755, baseEnd_68755] using wordTrace_append hprefix tailTrace_68755
  have hstable : (prefixWord ++ tailWord_68755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68755).length < 2 ^ (prefixWord ++ tailWord_68755).sum := by decide
  have hdescent : baseEnd_68755 < baseStart_68755 := by decide
  rcases family_descends (prefixWord ++ tailWord_68755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68765 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 3]
def baseStart_68765 : Nat := 118140960795 + 68765 * 2 ^ 59
def prefixEnd_68765 : Nat := 4983230072969 + 3 ^ 40 * 68765 * 2
def baseEnd_68765 : Nat := 31386219739136613618899

theorem tailTrace_68765 : CollatzResearch.WordTrace tailWord_68765 prefixEnd_68765 31386219739136613618899 := by
  unfold tailWord_68765
  simp only [CollatzResearch.WordTrace]
  refine ⟨2508065595883623972111749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1672043730589082648074499 2508065595883623972111749)
  ·
    refine ⟨470262299228179494770953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2508065595883623972111749 470262299228179494770953)
    ·
      refine ⟨352696724421134621078215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 470262299228179494770953 352696724421134621078215)
      ·
        refine ⟨529045086631701931617323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352696724421134621078215 529045086631701931617323)
        ·
          refine ⟨793567629947552897425985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529045086631701931617323 793567629947552897425985)
          ·
            refine ⟨595175722460664673069489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793567629947552897425985 595175722460664673069489)
            ·
              refine ⟨446381791845498504802117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595175722460664673069489 446381791845498504802117)
              ·
                refine ⟨83696585971030969650397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446381791845498504802117 83696585971030969650397)
                ·
                  refine ⟨31386219739136613618899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83696585971030969650397 31386219739136613618899)
                  ·
                    rfl

theorem cell20_68765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_68765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68765 prefixEnd_68765 := by exact prefixLift 68765
  have htrace : WordTrace (prefixWord ++ tailWord_68765) baseStart_68765 baseEnd_68765 := by
    simpa [prefixWord, tailWord_68765, baseEnd_68765] using wordTrace_append hprefix tailTrace_68765
  have hstable : (prefixWord ++ tailWord_68765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68765).length < 2 ^ (prefixWord ++ tailWord_68765).sum := by decide
  have hdescent : baseEnd_68765 < baseStart_68765 := by decide
  rcases family_descends (prefixWord ++ tailWord_68765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68768 : List Nat := [2, 1, 1, 4, 2, 1, 5, 2, 2]
def baseStart_68768 : Nat := 118140960795 + 68768 * 2 ^ 59
def prefixEnd_68768 : Nat := 4983230072969 + 3 ^ 40 * 68768 * 2
def baseEnd_68768 : Nat := 31387589020881936518887

theorem tailTrace_68768 : CollatzResearch.WordTrace tailWord_68768 prefixEnd_68768 31387589020881936518887 := by
  unfold tailWord_68768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254087507436377742235479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1672116676581836989647305 1254087507436377742235479)
  ·
    refine ⟨1881131261154566613353219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1254087507436377742235479 1881131261154566613353219)
    ·
      refine ⟨2821696891731849920029829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881131261154566613353219 2821696891731849920029829)
      ·
        refine ⟨529068167199721860005593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2821696891731849920029829 529068167199721860005593)
        ·
          refine ⟨396801125399791395004195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529068167199721860005593 396801125399791395004195)
          ·
            refine ⟨595201688099687092506293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396801125399791395004195 595201688099687092506293)
            ·
              refine ⟨55800158259345664922465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 595201688099687092506293 55800158259345664922465)
              ·
                refine ⟨41850118694509248691849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55800158259345664922465 41850118694509248691849)
                ·
                  refine ⟨31387589020881936518887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41850118694509248691849 31387589020881936518887)
                  ·
                    rfl

theorem cell20_68768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_68768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68768 prefixEnd_68768 := by exact prefixLift 68768
  have htrace : WordTrace (prefixWord ++ tailWord_68768) baseStart_68768 baseEnd_68768 := by
    simpa [prefixWord, tailWord_68768, baseEnd_68768] using wordTrace_append hprefix tailTrace_68768
  have hstable : (prefixWord ++ tailWord_68768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68768).length < 2 ^ (prefixWord ++ tailWord_68768).sum := by decide
  have hdescent : baseEnd_68768 < baseStart_68768 := by decide
  rcases family_descends (prefixWord ++ tailWord_68768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68778 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_68778 : Nat := 118140960795 + 68778 * 2 ^ 59
def prefixEnd_68778 : Nat := 4983230072969 + 3 ^ 40 * 68778 * 2
def baseEnd_68778 : Nat := 31392153293366346185513

theorem tailTrace_68778 : CollatzResearch.WordTrace tailWord_68778 prefixEnd_68778 31392153293366346185513 := by
  unfold tailWord_68778
  simp only [CollatzResearch.WordTrace]
  refine ⟨627134936209131798083747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1672359829891018128223325 627134936209131798083747)
  ·
    refine ⟨940702404313697697125621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627134936209131798083747 940702404313697697125621)
    ·
      refine ⟨88190850404409159105527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 940702404313697697125621 88190850404409159105527)
      ·
        refine ⟨132286275606613738658291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88190850404409159105527 132286275606613738658291)
        ·
          refine ⟨198429413409920607987437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132286275606613738658291 198429413409920607987437)
          ·
            refine ⟨74411030028720227995289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198429413409920607987437 74411030028720227995289)
            ·
              refine ⟨55808272521540170996467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74411030028720227995289 55808272521540170996467)
              ·
                refine ⟨83712408782310256494701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55808272521540170996467 83712408782310256494701)
                ·
                  refine ⟨31392153293366346185513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83712408782310256494701 31392153293366346185513)
                  ·
                    rfl

theorem cell20_68778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_68778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68778 prefixEnd_68778 := by exact prefixLift 68778
  have htrace : WordTrace (prefixWord ++ tailWord_68778) baseStart_68778 baseEnd_68778 := by
    simpa [prefixWord, tailWord_68778, baseEnd_68778] using wordTrace_append hprefix tailTrace_68778
  have hstable : (prefixWord ++ tailWord_68778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68778).length < 2 ^ (prefixWord ++ tailWord_68778).sum := by decide
  have hdescent : baseEnd_68778 < baseStart_68778 := by decide
  rcases family_descends (prefixWord ++ tailWord_68778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68813 : List Nat := [1, 6, 2, 2, 1, 8]
def baseStart_68813 : Nat := 118140960795 + 68813 * 2 ^ 59
def prefixEnd_68813 : Nat := 4983230072969 + 3 ^ 40 * 68813 * 2
def baseEnd_68813 : Nat := 1163264009150436296989

theorem tailTrace_68813 : CollatzResearch.WordTrace tailWord_68813 prefixEnd_68813 1163264009150436296989 := by
  unfold tailWord_68813
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509816299709728169859093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1673210866473152113239395 2509816299709728169859093)
  ·
    refine ⟨117647639048893507962145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2509816299709728169859093 117647639048893507962145)
    ·
      refine ⟨88235729286670130971609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117647639048893507962145 88235729286670130971609)
      ·
        refine ⟨66176796965002598228707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88235729286670130971609 66176796965002598228707)
        ·
          refine ⟨99265195447503897343061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66176796965002598228707 99265195447503897343061)
          ·
            refine ⟨1163264009150436296989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 99265195447503897343061 1163264009150436296989)
            ·
              rfl

theorem cell20_68813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 8].length) (baseStart_68813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68813 prefixEnd_68813 := by exact prefixLift 68813
  have htrace : WordTrace (prefixWord ++ tailWord_68813) baseStart_68813 baseEnd_68813 := by
    simpa [prefixWord, tailWord_68813, baseEnd_68813] using wordTrace_append hprefix tailTrace_68813
  have hstable : (prefixWord ++ tailWord_68813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68813).length < 2 ^ (prefixWord ++ tailWord_68813).sum := by decide
  have hdescent : baseEnd_68813 < baseStart_68813 := by decide
  rcases family_descends (prefixWord ++ tailWord_68813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68865 : List Nat := [1, 2, 4, 1, 1, 3, 1, 5, 2]
def baseStart_68865 : Nat := 118140960795 + 68865 * 2 ^ 59
def prefixEnd_68865 : Nat := 4983230072969 + 3 ^ 40 * 68865 * 2
def baseEnd_68865 : Nat := 31431862463980710285157

theorem tailTrace_68865 : CollatzResearch.WordTrace tailWord_68865 prefixEnd_68865 31431862463980710285157 := by
  unfold tailWord_68865
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511712895521341050752049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1674475263680894033834699 2511712895521341050752049)
  ·
    refine ⟨1883784671641005788064037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2511712895521341050752049 1883784671641005788064037)
    ·
      refine ⟨353209625932688585262007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1883784671641005788064037 353209625932688585262007)
      ·
        refine ⟨529814438899032877893011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353209625932688585262007 529814438899032877893011)
        ·
          refine ⟨794721658348549316839517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529814438899032877893011 794721658348549316839517)
          ·
            refine ⟨298020621880705993814819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 794721658348549316839517 298020621880705993814819)
            ·
              refine ⟨447030932821058990722229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298020621880705993814819 447030932821058990722229)
              ·
                refine ⟨41909149951974280380209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 447030932821058990722229 41909149951974280380209)
                ·
                  refine ⟨31431862463980710285157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41909149951974280380209 31431862463980710285157)
                  ·
                    rfl

theorem cell20_68865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_68865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68865 prefixEnd_68865 := by exact prefixLift 68865
  have htrace : WordTrace (prefixWord ++ tailWord_68865) baseStart_68865 baseEnd_68865 := by
    simpa [prefixWord, tailWord_68865, baseEnd_68865] using wordTrace_append hprefix tailTrace_68865
  have hstable : (prefixWord ++ tailWord_68865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68865).length < 2 ^ (prefixWord ++ tailWord_68865).sum := by decide
  have hdescent : baseEnd_68865 < baseStart_68865 := by decide
  rcases family_descends (prefixWord ++ tailWord_68865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68869 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_68869 : Nat := 118140960795 + 68869 * 2 ^ 59
def prefixEnd_68869 : Nat := 4983230072969 + 3 ^ 40 * 68869 * 2
def baseEnd_68869 : Nat := 31433688172974474151807

theorem tailTrace_68869 : CollatzResearch.WordTrace tailWord_68869 prefixEnd_68869 31433688172974474151807 := by
  unfold tailWord_68869
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511858787506849733897661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1674572525004566489265107 2511858787506849733897661)
  ·
    refine ⟨941947045315068650211623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2511858787506849733897661 941947045315068650211623)
    ·
      refine ⟨1412920567972602975317435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941947045315068650211623 1412920567972602975317435)
      ·
        refine ⟨2119380851958904462976153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412920567972602975317435 2119380851958904462976153)
        ·
          refine ⟨1589535638969178347232115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2119380851958904462976153 1589535638969178347232115)
          ·
            refine ⟨2384303458453767520848173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589535638969178347232115 2384303458453767520848173)
            ·
              refine ⟨894113796920162820318065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2384303458453767520848173 894113796920162820318065)
              ·
                refine ⟨670585347690122115238549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894113796920162820318065 670585347690122115238549)
                ·
                  refine ⟨31433688172974474151807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 670585347690122115238549 31433688172974474151807)
                  ·
                    rfl

theorem cell20_68869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_68869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68869 prefixEnd_68869 := by exact prefixLift 68869
  have htrace : WordTrace (prefixWord ++ tailWord_68869) baseStart_68869 baseEnd_68869 := by
    simpa [prefixWord, tailWord_68869, baseEnd_68869] using wordTrace_append hprefix tailTrace_68869
  have hstable : (prefixWord ++ tailWord_68869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68869).length < 2 ^ (prefixWord ++ tailWord_68869).sum := by decide
  have hdescent : baseEnd_68869 < baseStart_68869 := by decide
  rcases family_descends (prefixWord ++ tailWord_68869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68962 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_68962 : Nat := 118140960795 + 68962 * 2 ^ 59
def prefixEnd_68962 : Nat := 4983230072969 + 3 ^ 40 * 68962 * 2
def baseEnd_68962 : Nat := 31476135907079484051427

theorem tailTrace_68962 : CollatzResearch.WordTrace tailWord_68962 prefixEnd_68962 31476135907079484051427 := by
  unfold tailWord_68962
  simp only [CollatzResearch.WordTrace]
  refine ⟨628812694042481654258285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1676833850779951078022093 628812694042481654258285)
  ·
    refine ⟨235804760265930620346857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 628812694042481654258285 235804760265930620346857)
    ·
      refine ⟨176853570199447965260143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235804760265930620346857 176853570199447965260143)
      ·
        refine ⟨265280355299171947890215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176853570199447965260143 265280355299171947890215)
        ·
          refine ⟨397920532948757921835323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265280355299171947890215 397920532948757921835323)
          ·
            refine ⟨596880799423136882752985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397920532948757921835323 596880799423136882752985)
            ·
              refine ⟨447660599567352662064739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596880799423136882752985 447660599567352662064739)
              ·
                refine ⟨671490899351028993097109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447660599567352662064739 671490899351028993097109)
                ·
                  refine ⟨31476135907079484051427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 671490899351028993097109 31476135907079484051427)
                  ·
                    rfl

theorem cell20_68962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_68962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68962 prefixEnd_68962 := by exact prefixLift 68962
  have htrace : WordTrace (prefixWord ++ tailWord_68962) baseStart_68962 baseEnd_68962 := by
    simpa [prefixWord, tailWord_68962, baseEnd_68962] using wordTrace_append hprefix tailTrace_68962
  have hstable : (prefixWord ++ tailWord_68962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68962).length < 2 ^ (prefixWord ++ tailWord_68962).sum := by decide
  have hdescent : baseEnd_68962 < baseStart_68962 := by decide
  rcases family_descends (prefixWord ++ tailWord_68962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68996 : List Nat := [2, 3, 2, 1, 1, 3, 4, 2, 2]
def baseStart_68996 : Nat := 118140960795 + 68996 * 2 ^ 59
def prefixEnd_68996 : Nat := 4983230072969 + 3 ^ 40 * 68996 * 2
def baseEnd_68996 : Nat := 31491654433526476917955

theorem tailTrace_68996 : CollatzResearch.WordTrace tailWord_68996 prefixEnd_68996 31491654433526476917955 := by
  unfold tailWord_68996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258245429023375211885421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1677660572031166949180561 1258245429023375211885421)
  ·
    refine ⟨471842035883765704457033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1258245429023375211885421 471842035883765704457033)
    ·
      refine ⟨353881526912824278342775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 471842035883765704457033 353881526912824278342775)
      ·
        refine ⟨530822290369236417514163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353881526912824278342775 530822290369236417514163)
        ·
          refine ⟨796233435553854626271245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530822290369236417514163 796233435553854626271245)
          ·
            refine ⟨298587538332695484851717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 796233435553854626271245 298587538332695484851717)
            ·
              refine ⟨55985163437380403409697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298587538332695484851717 55985163437380403409697)
              ·
                refine ⟨41988872578035302557273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55985163437380403409697 41988872578035302557273)
                ·
                  refine ⟨31491654433526476917955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41988872578035302557273 31491654433526476917955)
                  ·
                    rfl

theorem cell20_68996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_68996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_68996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_68996 prefixEnd_68996 := by exact prefixLift 68996
  have htrace : WordTrace (prefixWord ++ tailWord_68996) baseStart_68996 baseEnd_68996 := by
    simpa [prefixWord, tailWord_68996, baseEnd_68996] using wordTrace_append hprefix tailTrace_68996
  have hstable : (prefixWord ++ tailWord_68996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68996).length < 2 ^ (prefixWord ++ tailWord_68996).sum := by decide
  have hdescent : baseEnd_68996 < baseStart_68996 := by decide
  rcases family_descends (prefixWord ++ tailWord_68996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69045 : List Nat := [1, 3, 3, 2, 2, 2, 7]
def baseStart_69045 : Nat := 118140960795 + 69045 * 2 ^ 59
def prefixEnd_69045 : Nat := 4983230072969 + 3 ^ 40 * 69045 * 2
def baseEnd_69045 : Nat := 3501557707633342698269

theorem tailTrace_69045 : CollatzResearch.WordTrace tailWord_69045 prefixEnd_69045 3501557707633342698269 := by
  unfold tailWord_69045
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518278034869231792304589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1678852023246154528203059 2518278034869231792304589)
  ·
    refine ⟨944354263075961922114221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2518278034869231792304589 944354263075961922114221)
    ·
      refine ⟨354132848653485720792833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 944354263075961922114221 354132848653485720792833)
      ·
        refine ⟨265599636490114290594625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354132848653485720792833 265599636490114290594625)
        ·
          refine ⟨199199727367585717945969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265599636490114290594625 199199727367585717945969)
          ·
            refine ⟨149399795525689288459477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199199727367585717945969 149399795525689288459477)
            ·
              refine ⟨3501557707633342698269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 149399795525689288459477 3501557707633342698269)
              ·
                rfl

theorem cell20_69045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_69045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69045 prefixEnd_69045 := by exact prefixLift 69045
  have htrace : WordTrace (prefixWord ++ tailWord_69045) baseStart_69045 baseEnd_69045 := by
    simpa [prefixWord, tailWord_69045, baseEnd_69045] using wordTrace_append hprefix tailTrace_69045
  have hstable : (prefixWord ++ tailWord_69045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69045).length < 2 ^ (prefixWord ++ tailWord_69045).sum := by decide
  have hdescent : baseEnd_69045 < baseStart_69045 := by decide
  rcases family_descends (prefixWord ++ tailWord_69045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69059 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_69059 : Nat := 118140960795 + 69059 * 2 ^ 59
def prefixEnd_69059 : Nat := 4983230072969 + 3 ^ 40 * 69059 * 2
def baseEnd_69059 : Nat := 31520409350178257817697

theorem tailTrace_69059 : CollatzResearch.WordTrace tailWord_69059 prefixEnd_69059 31520409350178257817697 := by
  unfold tailWord_69059
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518788656818512183314231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1679192437879008122209487 2518788656818512183314231)
  ·
    refine ⟨3778182985227768274971347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518788656818512183314231 3778182985227768274971347)
    ·
      refine ⟨5667274477841652412457021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3778182985227768274971347 5667274477841652412457021)
      ·
        refine ⟨2125227929190619654671383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5667274477841652412457021 2125227929190619654671383)
        ·
          refine ⟨3187841893785929482007075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125227929190619654671383 3187841893785929482007075)
          ·
            refine ⟨4781762840678894223010613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187841893785929482007075 4781762840678894223010613)
            ·
              refine ⟨448290266313646333407245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4781762840678894223010613 448290266313646333407245)
              ·
                refine ⟨168108849867617375027717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448290266313646333407245 168108849867617375027717)
                ·
                  refine ⟨31520409350178257817697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168108849867617375027717 31520409350178257817697)
                  ·
                    rfl

theorem cell20_69059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_69059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69059 prefixEnd_69059 := by exact prefixLift 69059
  have htrace : WordTrace (prefixWord ++ tailWord_69059) baseStart_69059 baseEnd_69059 := by
    simpa [prefixWord, tailWord_69059, baseEnd_69059] using wordTrace_append hprefix tailTrace_69059
  have hstable : (prefixWord ++ tailWord_69059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69059).length < 2 ^ (prefixWord ++ tailWord_69059).sum := by decide
  have hdescent : baseEnd_69059 < baseStart_69059 := by decide
  rcases family_descends (prefixWord ++ tailWord_69059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69104 : List Nat := [2, 1, 1, 1, 3, 4, 8]
def baseStart_69104 : Nat := 118140960795 + 69104 * 2 ^ 59
def prefixEnd_69104 : Nat := 4983230072969 + 3 ^ 40 * 69104 * 2
def baseEnd_69104 : Nat := 3504549841817566813057

theorem tailTrace_69104 : CollatzResearch.WordTrace tailWord_69104 prefixEnd_69104 3504549841817566813057 := by
  unfold tailWord_69104
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260214970827742434351183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1680286627770323245801577 1260214970827742434351183)
  ·
    refine ⟨1890322456241613651526775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260214970827742434351183 1890322456241613651526775)
    ·
      refine ⟨2835483684362420477290163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890322456241613651526775 2835483684362420477290163)
      ·
        refine ⟨4253225526543630715935245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835483684362420477290163 4253225526543630715935245)
        ·
          refine ⟨1594959572453861518475717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4253225526543630715935245 1594959572453861518475717)
          ·
            refine ⟨299054919835099034714197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1594959572453861518475717 299054919835099034714197)
            ·
              refine ⟨3504549841817566813057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 299054919835099034714197 3504549841817566813057)
              ·
                rfl

theorem cell20_69104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 8].length) (baseStart_69104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69104 prefixEnd_69104 := by exact prefixLift 69104
  have htrace : WordTrace (prefixWord ++ tailWord_69104) baseStart_69104 baseEnd_69104 := by
    simpa [prefixWord, tailWord_69104, baseEnd_69104] using wordTrace_append hprefix tailTrace_69104
  have hstable : (prefixWord ++ tailWord_69104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69104).length < 2 ^ (prefixWord ++ tailWord_69104).sum := by decide
  have hdescent : baseEnd_69104 < baseStart_69104 := by decide
  rcases family_descends (prefixWord ++ tailWord_69104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69124 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_69124 : Nat := 118140960795 + 69124 * 2 ^ 59
def prefixEnd_69124 : Nat := 4983230072969 + 3 ^ 40 * 69124 * 2
def baseEnd_69124 : Nat := 31550077121326920650765

theorem tailTrace_69124 : CollatzResearch.WordTrace tailWord_69124 prefixEnd_69124 31550077121326920650765 := by
  unfold tailWord_69124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260579700791514142215213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1680772934388685522953617 1260579700791514142215213)
  ·
    refine ⟨472717387796817803330705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1260579700791514142215213 472717387796817803330705)
    ·
      refine ⟨354538040847613352498029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 472717387796817803330705 354538040847613352498029)
      ·
        refine ⟨132951765317855007186761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354538040847613352498029 132951765317855007186761)
        ·
          refine ⟨99713823988391255390071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132951765317855007186761 99713823988391255390071)
          ·
            refine ⟨149570735982586883085107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99713823988391255390071 149570735982586883085107)
            ·
              refine ⟨224356103973880324627661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149570735982586883085107 224356103973880324627661)
              ·
                refine ⟨84133538990205121735373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224356103973880324627661 84133538990205121735373)
                ·
                  refine ⟨31550077121326920650765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84133538990205121735373 31550077121326920650765)
                  ·
                    rfl

theorem cell20_69124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_69124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69124 prefixEnd_69124 := by exact prefixLift 69124
  have htrace : WordTrace (prefixWord ++ tailWord_69124) baseStart_69124 baseEnd_69124 := by
    simpa [prefixWord, tailWord_69124, baseEnd_69124] using wordTrace_append hprefix tailTrace_69124
  have hstable : (prefixWord ++ tailWord_69124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69124).length < 2 ^ (prefixWord ++ tailWord_69124).sum := by decide
  have hdescent : baseEnd_69124 < baseStart_69124 := by decide
  rcases family_descends (prefixWord ++ tailWord_69124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69187 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_69187 : Nat := 118140960795 + 69187 * 2 ^ 59
def prefixEnd_69187 : Nat := 4983230072969 + 3 ^ 40 * 69187 * 2
def baseEnd_69187 : Nat := 31578832037978701550507

theorem tailTrace_69187 : CollatzResearch.WordTrace tailWord_69187 prefixEnd_69187 31578832037978701550507 := by
  unfold tailWord_69187
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523457200354790043973815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1682304800236526695982543 2523457200354790043973815)
  ·
    refine ⟨3785185800532185065960723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2523457200354790043973815 3785185800532185065960723)
    ·
      refine ⟨5677778700798277598941085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3785185800532185065960723 5677778700798277598941085)
      ·
        refine ⟨2129167012799354099602907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5677778700798277598941085 2129167012799354099602907)
        ·
          refine ⟨3193750519199031149404361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129167012799354099602907 3193750519199031149404361)
          ·
            refine ⟨2395312889399273362053271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3193750519199031149404361 2395312889399273362053271)
            ·
              refine ⟨3592969334098910043079907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395312889399273362053271 3592969334098910043079907)
              ·
                refine ⟨5389454001148365064619861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592969334098910043079907 5389454001148365064619861)
                ·
                  refine ⟨31578832037978701550507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5389454001148365064619861 31578832037978701550507)
                  ·
                    rfl

theorem cell20_69187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_69187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69187 prefixEnd_69187 := by exact prefixLift 69187
  have htrace : WordTrace (prefixWord ++ tailWord_69187) baseStart_69187 baseEnd_69187 := by
    simpa [prefixWord, tailWord_69187, baseEnd_69187] using wordTrace_append hprefix tailTrace_69187
  have hstable : (prefixWord ++ tailWord_69187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69187).length < 2 ^ (prefixWord ++ tailWord_69187).sum := by decide
  have hdescent : baseEnd_69187 < baseStart_69187 := by decide
  rcases family_descends (prefixWord ++ tailWord_69187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69204 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_69204 : Nat := 118140960795 + 69204 * 2 ^ 59
def prefixEnd_69204 : Nat := 4983230072969 + 3 ^ 40 * 69204 * 2
def baseEnd_69204 : Nat := 31586591301202197983771

theorem tailTrace_69204 : CollatzResearch.WordTrace tailWord_69204 prefixEnd_69204 31586591301202197983771 := by
  unfold tailWord_69204
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262038620646600973671333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1682718160862134631561777 1262038620646600973671333)
  ·
    refine ⟨236632241371237682563375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1262038620646600973671333 236632241371237682563375)
    ·
      refine ⟨354948362056856523845063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236632241371237682563375 354948362056856523845063)
      ·
        refine ⟨532422543085284785767595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354948362056856523845063 532422543085284785767595)
        ·
          refine ⟨798633814627927178651393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532422543085284785767595 798633814627927178651393)
          ·
            refine ⟨598975360970945383988545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798633814627927178651393 598975360970945383988545)
            ·
              refine ⟨449231520728209037991409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598975360970945383988545 449231520728209037991409)
              ·
                refine ⟨336923640546156778493557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449231520728209037991409 336923640546156778493557)
                ·
                  refine ⟨31586591301202197983771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 336923640546156778493557 31586591301202197983771)
                  ·
                    rfl

theorem cell20_69204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_69204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69204 prefixEnd_69204 := by exact prefixLift 69204
  have htrace : WordTrace (prefixWord ++ tailWord_69204) baseStart_69204 baseEnd_69204 := by
    simpa [prefixWord, tailWord_69204, baseEnd_69204] using wordTrace_append hprefix tailTrace_69204
  have hstable : (prefixWord ++ tailWord_69204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69204).length < 2 ^ (prefixWord ++ tailWord_69204).sum := by decide
  have hdescent : baseEnd_69204 < baseStart_69204 := by decide
  rcases family_descends (prefixWord ++ tailWord_69204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69207 : List Nat := [1, 1, 3, 2, 2, 4, 2, 3, 2]
def baseStart_69207 : Nat := 118140960795 + 69207 * 2 ^ 59
def prefixEnd_69207 : Nat := 4983230072969 + 3 ^ 40 * 69207 * 2
def baseEnd_69207 : Nat := 31587960582947520883759

theorem tailTrace_69207 : CollatzResearch.WordTrace tailWord_69207 prefixEnd_69207 31587960582947520883759 := by
  unfold tailWord_69207
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524186660282333459701875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1682791106854888973134583 2524186660282333459701875)
  ·
    refine ⟨3786279990423500189552813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2524186660282333459701875 3786279990423500189552813)
    ·
      refine ⟨1419854996408812571082305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3786279990423500189552813 1419854996408812571082305)
      ·
        refine ⟨1064891247306609428311729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1419854996408812571082305 1064891247306609428311729)
        ·
          refine ⟨798668435479957071233797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064891247306609428311729 798668435479957071233797)
          ·
            refine ⟨149750331652491950856337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 798668435479957071233797 149750331652491950856337)
            ·
              refine ⟨112312748739368963142253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149750331652491950856337 112312748739368963142253)
              ·
                refine ⟨42117280777263361178345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112312748739368963142253 42117280777263361178345)
                ·
                  refine ⟨31587960582947520883759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42117280777263361178345 31587960582947520883759)
                  ·
                    rfl

theorem cell20_69207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 2].length) (baseStart_69207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69207 prefixEnd_69207 := by exact prefixLift 69207
  have htrace : WordTrace (prefixWord ++ tailWord_69207) baseStart_69207 baseEnd_69207 := by
    simpa [prefixWord, tailWord_69207, baseEnd_69207] using wordTrace_append hprefix tailTrace_69207
  have hstable : (prefixWord ++ tailWord_69207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69207).length < 2 ^ (prefixWord ++ tailWord_69207).sum := by decide
  have hdescent : baseEnd_69207 < baseStart_69207 := by decide
  rcases family_descends (prefixWord ++ tailWord_69207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69221 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 3]
def baseStart_69221 : Nat := 118140960795 + 69221 * 2 ^ 59
def prefixEnd_69221 : Nat := 4983230072969 + 3 ^ 40 * 69221 * 2
def baseEnd_69221 : Nat := 31594350564425694417035

theorem tailTrace_69221 : CollatzResearch.WordTrace tailWord_69221 prefixEnd_69221 31594350564425694417035 := by
  unfold tailWord_69221
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524697282231613850711517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1683131521487742567141011 2524697282231613850711517)
  ·
    refine ⟨946761480836855194016819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2524697282231613850711517 946761480836855194016819)
    ·
      refine ⟨1420142221255282791025229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 946761480836855194016819 1420142221255282791025229)
      ·
        refine ⟨532553332970731046634461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1420142221255282791025229 532553332970731046634461)
        ·
          refine ⟨199707499864024142487923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 532553332970731046634461 199707499864024142487923)
          ·
            refine ⟨299561249796036213731885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199707499864024142487923 299561249796036213731885)
            ·
              refine ⟨112335468673513580149457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299561249796036213731885 112335468673513580149457)
              ·
                refine ⟨84251601505135185112093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112335468673513580149457 84251601505135185112093)
                ·
                  refine ⟨31594350564425694417035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84251601505135185112093 31594350564425694417035)
                  ·
                    rfl

theorem cell20_69221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_69221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69221 prefixEnd_69221 := by exact prefixLift 69221
  have htrace : WordTrace (prefixWord ++ tailWord_69221) baseStart_69221 baseEnd_69221 := by
    simpa [prefixWord, tailWord_69221, baseEnd_69221] using wordTrace_append hprefix tailTrace_69221
  have hstable : (prefixWord ++ tailWord_69221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69221).length < 2 ^ (prefixWord ++ tailWord_69221).sum := by decide
  have hdescent : baseEnd_69221 < baseStart_69221 := by decide
  rcases family_descends (prefixWord ++ tailWord_69221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69262 : List Nat := [4, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_69262 : Nat := 118140960795 + 69262 * 2 ^ 59
def prefixEnd_69262 : Nat := 4983230072969 + 3 ^ 40 * 69262 * 2
def baseEnd_69262 : Nat := 31613064081611774050201

theorem tailTrace_69262 : CollatzResearch.WordTrace tailWord_69262 prefixEnd_69262 31613064081611774050201 := by
  unfold tailWord_69262
  simp only [CollatzResearch.WordTrace]
  refine ⟨315774084385384731619255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1684128450055385235302693 315774084385384731619255)
  ·
    refine ⟨473661126578077097428883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 315774084385384731619255 473661126578077097428883)
    ·
      refine ⟨710491689867115646143325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473661126578077097428883 710491689867115646143325)
      ·
        refine ⟨266434383700168367303747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 710491689867115646143325 266434383700168367303747)
        ·
          refine ⟨399651575550252550955621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266434383700168367303747 399651575550252550955621)
          ·
            refine ⟨74934670415672353304179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 399651575550252550955621 74934670415672353304179)
            ·
              refine ⟨112402005623508529956269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74934670415672353304179 112402005623508529956269)
              ·
                refine ⟨42150752108815698733601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112402005623508529956269 42150752108815698733601)
                ·
                  refine ⟨31613064081611774050201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42150752108815698733601 31613064081611774050201)
                  ·
                    rfl

theorem cell20_69262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_69262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69262 prefixEnd_69262 := by exact prefixLift 69262
  have htrace : WordTrace (prefixWord ++ tailWord_69262) baseStart_69262 baseEnd_69262 := by
    simpa [prefixWord, tailWord_69262, baseEnd_69262] using wordTrace_append hprefix tailTrace_69262
  have hstable : (prefixWord ++ tailWord_69262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69262).length < 2 ^ (prefixWord ++ tailWord_69262).sum := by decide
  have hdescent : baseEnd_69262 < baseStart_69262 := by decide
  rcases family_descends (prefixWord ++ tailWord_69262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69279 : List Nat := [1, 1, 2, 7, 1, 1, 3, 2, 2]
def baseStart_69279 : Nat := 118140960795 + 69279 * 2 ^ 59
def prefixEnd_69279 : Nat := 4983230072969 + 3 ^ 40 * 69279 * 2
def baseEnd_69279 : Nat := 31620823344835270483465

theorem tailTrace_69279 : CollatzResearch.WordTrace tailWord_69279 prefixEnd_69279 31620823344835270483465 := by
  unfold tailWord_69279
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526812716021489756322891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1684541810680993170881927 2526812716021489756322891)
  ·
    refine ⟨3790219074032234634484337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526812716021489756322891 3790219074032234634484337)
    ·
      refine ⟨2842664305524175975863253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3790219074032234634484337 2842664305524175975863253)
      ·
        refine ⟨66624944660722874434295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2842664305524175975863253 66624944660722874434295)
        ·
          refine ⟨99937416991084311651443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66624944660722874434295 99937416991084311651443)
          ·
            refine ⟨149906125486626467477165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99937416991084311651443 149906125486626467477165)
            ·
              refine ⟨56214797057484925303937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149906125486626467477165 56214797057484925303937)
              ·
                refine ⟨42161097793113693977953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56214797057484925303937 42161097793113693977953)
                ·
                  refine ⟨31620823344835270483465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42161097793113693977953 31620823344835270483465)
                  ·
                    rfl

theorem cell20_69279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 2].length) (baseStart_69279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69279 prefixEnd_69279 := by exact prefixLift 69279
  have htrace : WordTrace (prefixWord ++ tailWord_69279) baseStart_69279 baseEnd_69279 := by
    simpa [prefixWord, tailWord_69279, baseEnd_69279] using wordTrace_append hprefix tailTrace_69279
  have hstable : (prefixWord ++ tailWord_69279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69279).length < 2 ^ (prefixWord ++ tailWord_69279).sum := by decide
  have hdescent : baseEnd_69279 < baseStart_69279 := by decide
  rcases family_descends (prefixWord ++ tailWord_69279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69280 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_69280 : Nat := 118140960795 + 69280 * 2 ^ 59
def prefixEnd_69280 : Nat := 4983230072969 + 3 ^ 40 * 69280 * 2
def baseEnd_69280 : Nat := 31621279772083711450127

theorem tailTrace_69280 : CollatzResearch.WordTrace tailWord_69280 prefixEnd_69280 31621279772083711450127 := by
  unfold tailWord_69280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263424594508933463554647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1684566126011911284739529 1263424594508933463554647)
  ·
    refine ⟨1895136891763400195331971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1263424594508933463554647 1895136891763400195331971)
    ·
      refine ⟨2842705337645100292997957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895136891763400195331971 2842705337645100292997957)
      ·
        refine ⟨533007250808456304937117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2842705337645100292997957 533007250808456304937117)
        ·
          refine ⟨199877719053171114351419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 533007250808456304937117 199877719053171114351419)
          ·
            refine ⟨299816578579756671527129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199877719053171114351419 299816578579756671527129)
            ·
              refine ⟨224862433934817503645347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299816578579756671527129 224862433934817503645347)
              ·
                refine ⟨337293650902226255468021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224862433934817503645347 337293650902226255468021)
                ·
                  refine ⟨31621279772083711450127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 337293650902226255468021 31621279772083711450127)
                  ·
                    rfl

theorem cell20_69280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_69280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69280 prefixEnd_69280 := by exact prefixLift 69280
  have htrace : WordTrace (prefixWord ++ tailWord_69280) baseStart_69280 baseEnd_69280 := by
    simpa [prefixWord, tailWord_69280, baseEnd_69280] using wordTrace_append hprefix tailTrace_69280
  have hstable : (prefixWord ++ tailWord_69280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69280).length < 2 ^ (prefixWord ++ tailWord_69280).sum := by decide
  have hdescent : baseEnd_69280 < baseStart_69280 := by decide
  rcases family_descends (prefixWord ++ tailWord_69280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69283 : List Nat := [1, 1, 1, 4, 1, 1, 7, 2, 2]
def baseStart_69283 : Nat := 118140960795 + 69283 * 2 ^ 59
def prefixEnd_69283 : Nat := 4983230072969 + 3 ^ 40 * 69283 * 2
def baseEnd_69283 : Nat := 31622649053829034350115

theorem tailTrace_69283 : CollatzResearch.WordTrace tailWord_69283 prefixEnd_69283 31622649053829034350115 := by
  unfold tailWord_69283
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526958608006998439468503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1684639072004665626312335 2526958608006998439468503)
  ·
    refine ⟨3790437912010497659202755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526958608006998439468503 3790437912010497659202755)
    ·
      refine ⟨5685656868015746488804133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3790437912010497659202755 5685656868015746488804133)
      ·
        refine ⟨1066060662752952466650775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5685656868015746488804133 1066060662752952466650775)
        ·
          refine ⟨1599090994129428699976163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066060662752952466650775 1599090994129428699976163)
          ·
            refine ⟨2398636491194143049964245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599090994129428699976163 2398636491194143049964245)
            ·
              refine ⟨56218042762362727733537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2398636491194143049964245 56218042762362727733537)
              ·
                refine ⟨42163532071772045800153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56218042762362727733537 42163532071772045800153)
                ·
                  refine ⟨31622649053829034350115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42163532071772045800153 31622649053829034350115)
                  ·
                    rfl

theorem cell20_69283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 2].length) (baseStart_69283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69283 prefixEnd_69283 := by exact prefixLift 69283
  have htrace : WordTrace (prefixWord ++ tailWord_69283) baseStart_69283 baseEnd_69283 := by
    simpa [prefixWord, tailWord_69283, baseEnd_69283] using wordTrace_append hprefix tailTrace_69283
  have hstable : (prefixWord ++ tailWord_69283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69283).length < 2 ^ (prefixWord ++ tailWord_69283).sum := by decide
  have hdescent : baseEnd_69283 < baseStart_69283 := by decide
  rcases family_descends (prefixWord ++ tailWord_69283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69338 : List Nat := [3, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_69338 : Nat := 118140960795 + 69338 * 2 ^ 59
def prefixEnd_69338 : Nat := 4983230072969 + 3 ^ 40 * 69338 * 2
def baseEnd_69338 : Nat := 31647752552493287516557

theorem tailTrace_69338 : CollatzResearch.WordTrace tailWord_69338 prefixEnd_69338 31647752552493287516557 := by
  unfold tailWord_69338
  simp only [CollatzResearch.WordTrace]
  refine ⟨632241155701935708180167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1685976415205161888480445 632241155701935708180167)
  ·
    refine ⟨948361733552903562270251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 632241155701935708180167 948361733552903562270251)
    ·
      refine ⟨1422542600329355343405377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948361733552903562270251 1422542600329355343405377)
      ·
        refine ⟨1066906950247016507554033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1422542600329355343405377 1066906950247016507554033)
        ·
          refine ⟨800180212685262380665525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066906950247016507554033 800180212685262380665525)
          ·
            refine ⟨75016894939243348187393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 800180212685262380665525 75016894939243348187393)
            ·
              refine ⟨56262671204432511140545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75016894939243348187393 56262671204432511140545)
              ·
                refine ⟨42197003403324383355409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56262671204432511140545 42197003403324383355409)
                ·
                  refine ⟨31647752552493287516557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42197003403324383355409 31647752552493287516557)
                  ·
                    rfl

theorem cell20_69338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_69338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69338 prefixEnd_69338 := by exact prefixLift 69338
  have htrace : WordTrace (prefixWord ++ tailWord_69338) baseStart_69338 baseEnd_69338 := by
    simpa [prefixWord, tailWord_69338, baseEnd_69338] using wordTrace_append hprefix tailTrace_69338
  have hstable : (prefixWord ++ tailWord_69338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69338).length < 2 ^ (prefixWord ++ tailWord_69338).sum := by decide
  have hdescent : baseEnd_69338 < baseStart_69338 := by decide
  rcases family_descends (prefixWord ++ tailWord_69338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69356 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_69356 : Nat := 118140960795 + 69356 * 2 ^ 59
def prefixEnd_69356 : Nat := 4983230072969 + 3 ^ 40 * 69356 * 2
def baseEnd_69356 : Nat := 31655968242965224916483

theorem tailTrace_69356 : CollatzResearch.WordTrace tailWord_69356 prefixEnd_69356 31655968242965224916483 := by
  unfold tailWord_69356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264810568371265953437961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1686414091161687937917281 1264810568371265953437961)
  ·
    refine ⟨948607926278449465078471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1264810568371265953437961 948607926278449465078471)
    ·
      refine ⟨1422911889417674197617707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948607926278449465078471 1422911889417674197617707)
      ·
        refine ⟨2134367834126511296426561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422911889417674197617707 2134367834126511296426561)
        ·
          refine ⟨1600775875594883472319921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134367834126511296426561 1600775875594883472319921)
          ·
            refine ⟨1200581906696162604239941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600775875594883472319921 1200581906696162604239941)
            ·
              refine ⟨225109107505530488294989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1200581906696162604239941 225109107505530488294989)
              ·
                refine ⟨84415915314573933110621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225109107505530488294989 84415915314573933110621)
                ·
                  refine ⟨31655968242965224916483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84415915314573933110621 31655968242965224916483)
                  ·
                    rfl

theorem cell20_69356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_69356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69356 prefixEnd_69356 := by exact prefixLift 69356
  have htrace : WordTrace (prefixWord ++ tailWord_69356) baseStart_69356 baseEnd_69356 := by
    simpa [prefixWord, tailWord_69356, baseEnd_69356] using wordTrace_append hprefix tailTrace_69356
  have hstable : (prefixWord ++ tailWord_69356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69356).length < 2 ^ (prefixWord ++ tailWord_69356).sum := by decide
  have hdescent : baseEnd_69356 < baseStart_69356 := by decide
  rcases family_descends (prefixWord ++ tailWord_69356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69366 : List Nat := [5, 1, 1, 1, 1, 4, 3, 4]
def baseStart_69366 : Nat := 118140960795 + 69366 * 2 ^ 59
def prefixEnd_69366 : Nat := 4983230072969 + 3 ^ 40 * 69366 * 2
def baseEnd_69366 : Nat := 10553510838483211527703

theorem tailTrace_69366 : CollatzResearch.WordTrace tailWord_69366 prefixEnd_69366 10553510838483211527703 := by
  unfold tailWord_69366
  simp only [CollatzResearch.WordTrace]
  refine ⟨158124116669143975921247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1686657244470869076493301 158124116669143975921247)
  ·
    refine ⟨237186175003715963881871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158124116669143975921247 237186175003715963881871)
    ·
      refine ⟨355779262505573945822807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237186175003715963881871 355779262505573945822807)
      ·
        refine ⟨533668893758360918734211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355779262505573945822807 533668893758360918734211)
        ·
          refine ⟨800503340637541378101317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533668893758360918734211 800503340637541378101317)
          ·
            refine ⟨150094376369539008393997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 800503340637541378101317 150094376369539008393997)
            ·
              refine ⟨56285391138577128147749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150094376369539008393997 56285391138577128147749)
              ·
                refine ⟨10553510838483211527703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56285391138577128147749 10553510838483211527703)
                ·
                  rfl

theorem cell20_69366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_69366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69366 prefixEnd_69366 := by exact prefixLift 69366
  have htrace : WordTrace (prefixWord ++ tailWord_69366) baseStart_69366 baseEnd_69366 := by
    simpa [prefixWord, tailWord_69366, baseEnd_69366] using wordTrace_append hprefix tailTrace_69366
  have hstable : (prefixWord ++ tailWord_69366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69366).length < 2 ^ (prefixWord ++ tailWord_69366).sum := by decide
  have hdescent : baseEnd_69366 < baseStart_69366 := by decide
  rcases family_descends (prefixWord ++ tailWord_69366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69382 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_69382 : Nat := 118140960795 + 69382 * 2 ^ 59
def prefixEnd_69382 : Nat := 4983230072969 + 3 ^ 40 * 69382 * 2
def baseEnd_69382 : Nat := 31667835351424690049711

theorem tailTrace_69382 : CollatzResearch.WordTrace tailWord_69382 prefixEnd_69382 31667835351424690049711 := by
  unfold tailWord_69382
  simp only [CollatzResearch.WordTrace]
  refine ⟨79080294832760573353825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1687046289765558898214933 79080294832760573353825)
  ·
    refine ⟨59310221124570430015369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79080294832760573353825 59310221124570430015369)
    ·
      refine ⟨44482665843427822511527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59310221124570430015369 44482665843427822511527)
      ·
        refine ⟨66723998765141733767291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44482665843427822511527 66723998765141733767291)
        ·
          refine ⟨100085998147712600650937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66723998765141733767291 100085998147712600650937)
          ·
            refine ⟨75064498610784450488203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100085998147712600650937 75064498610784450488203)
            ·
              refine ⟨112596747916176675732305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75064498610784450488203 112596747916176675732305)
              ·
                refine ⟨84447560937132506799229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112596747916176675732305 84447560937132506799229)
                ·
                  refine ⟨31667835351424690049711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84447560937132506799229 31667835351424690049711)
                  ·
                    rfl

theorem cell20_69382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_69382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69382 prefixEnd_69382 := by exact prefixLift 69382
  have htrace : WordTrace (prefixWord ++ tailWord_69382) baseStart_69382 baseEnd_69382 := by
    simpa [prefixWord, tailWord_69382, baseEnd_69382] using wordTrace_append hprefix tailTrace_69382
  have hstable : (prefixWord ++ tailWord_69382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69382).length < 2 ^ (prefixWord ++ tailWord_69382).sum := by decide
  have hdescent : baseEnd_69382 < baseStart_69382 := by decide
  rcases family_descends (prefixWord ++ tailWord_69382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69408 : List Nat := [2, 1, 1, 5, 1, 1, 2, 7]
def baseStart_69408 : Nat := 118140960795 + 69408 * 2 ^ 59
def prefixEnd_69408 : Nat := 4983230072969 + 3 ^ 40 * 69408 * 2
def baseEnd_69408 : Nat := 10559900819961385060979

theorem tailTrace_69408 : CollatzResearch.WordTrace tailWord_69408 prefixEnd_69408 10559900819961385060979 := by
  unfold tailWord_69408
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265758866277072393884439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1687678488369429858512585 1265758866277072393884439)
  ·
    refine ⟨1898638299415608590826659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1265758866277072393884439 1898638299415608590826659)
    ·
      refine ⟨2847957449123412886239989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1898638299415608590826659 2847957449123412886239989)
      ·
        refine ⟨266996010855319958084999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2847957449123412886239989 266996010855319958084999)
        ·
          refine ⟨400494016282979937127499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266996010855319958084999 400494016282979937127499)
          ·
            refine ⟨600741024424469905691249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400494016282979937127499 600741024424469905691249)
            ·
              refine ⟨450555768318352429268437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600741024424469905691249 450555768318352429268437)
              ·
                refine ⟨10559900819961385060979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 450555768318352429268437 10559900819961385060979)
                ·
                  rfl

theorem cell20_69408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_69408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69408 prefixEnd_69408 := by exact prefixLift 69408
  have htrace : WordTrace (prefixWord ++ tailWord_69408) baseStart_69408 baseEnd_69408 := by
    simpa [prefixWord, tailWord_69408, baseEnd_69408] using wordTrace_append hprefix tailTrace_69408
  have hstable : (prefixWord ++ tailWord_69408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69408).length < 2 ^ (prefixWord ++ tailWord_69408).sum := by decide
  have hdescent : baseEnd_69408 < baseStart_69408 := by decide
  rcases family_descends (prefixWord ++ tailWord_69408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69425 : List Nat := [1, 2, 2, 3, 2, 2, 4, 4]
def baseStart_69425 : Nat := 118140960795 + 69425 * 2 ^ 59
def prefixEnd_69425 : Nat := 4983230072969 + 3 ^ 40 * 69425 * 2
def baseEnd_69425 : Nat := 10562487241035883872067

theorem tailTrace_69425 : CollatzResearch.WordTrace tailWord_69425 prefixEnd_69425 10562487241035883872067 := by
  unfold tailWord_69425
  simp only [CollatzResearch.WordTrace]
  refine ⟨2532137773492556691137729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1688091848995037794091819 2532137773492556691137729)
  ·
    refine ⟨1899103330119417518353297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2532137773492556691137729 1899103330119417518353297)
    ·
      refine ⟨1424327497589563138764973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1899103330119417518353297 1424327497589563138764973)
      ·
        refine ⟨534122811596086177036865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1424327497589563138764973 534122811596086177036865)
        ·
          refine ⟨400592108697064632777649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534122811596086177036865 400592108697064632777649)
          ·
            refine ⟨300444081522798474583237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400592108697064632777649 300444081522798474583237)
            ·
              refine ⟨56333265285524713984357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 300444081522798474583237 56333265285524713984357)
              ·
                refine ⟨10562487241035883872067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56333265285524713984357 10562487241035883872067)
                ·
                  rfl

theorem cell20_69425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_69425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69425 prefixEnd_69425 := by exact prefixLift 69425
  have htrace : WordTrace (prefixWord ++ tailWord_69425) baseStart_69425 baseEnd_69425 := by
    simpa [prefixWord, tailWord_69425, baseEnd_69425] using wordTrace_append hprefix tailTrace_69425
  have hstable : (prefixWord ++ tailWord_69425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69425).length < 2 ^ (prefixWord ++ tailWord_69425).sum := by decide
  have hdescent : baseEnd_69425 < baseStart_69425 := by decide
  rcases family_descends (prefixWord ++ tailWord_69425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69452 : List Nat := [2, 2, 1, 3, 4, 1, 3, 2, 2]
def baseStart_69452 : Nat := 118140960795 + 69452 * 2 ^ 59
def prefixEnd_69452 : Nat := 4983230072969 + 3 ^ 40 * 69452 * 2
def baseEnd_69452 : Nat := 31699785258815557716091

theorem tailTrace_69452 : CollatzResearch.WordTrace tailWord_69452 prefixEnd_69452 31699785258815557716091 := by
  unfold tailWord_69452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266561272197370151185305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1688748362929826868247073 1266561272197370151185305)
  ·
    refine ⟨949920954148027613388979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1266561272197370151185305 949920954148027613388979)
    ·
      refine ⟨1424881431222041420083469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949920954148027613388979 1424881431222041420083469)
      ·
        refine ⟨534330536708265532531301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1424881431222041420083469 534330536708265532531301)
        ·
          refine ⟨100186975632799787349619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 534330536708265532531301 100186975632799787349619)
          ·
            refine ⟨150280463449199681024429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100186975632799787349619 150280463449199681024429)
            ·
              refine ⟨56355173793449880384161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150280463449199681024429 56355173793449880384161)
              ·
                refine ⟨42266380345087410288121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56355173793449880384161 42266380345087410288121)
                ·
                  refine ⟨31699785258815557716091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42266380345087410288121 31699785258815557716091)
                  ·
                    rfl

theorem cell20_69452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_69452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69452 prefixEnd_69452 := by exact prefixLift 69452
  have htrace : WordTrace (prefixWord ++ tailWord_69452) baseStart_69452 baseEnd_69452 := by
    simpa [prefixWord, tailWord_69452, baseEnd_69452] using wordTrace_append hprefix tailTrace_69452
  have hstable : (prefixWord ++ tailWord_69452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69452).length < 2 ^ (prefixWord ++ tailWord_69452).sum := by decide
  have hdescent : baseEnd_69452 < baseStart_69452 := by decide
  rcases family_descends (prefixWord ++ tailWord_69452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69463 : List Nat := [1, 1, 3, 2, 5, 1, 2, 5]
def baseStart_69463 : Nat := 118140960795 + 69463 * 2 ^ 59
def prefixEnd_69463 : Nat := 4983230072969 + 3 ^ 40 * 69463 * 2
def baseEnd_69463 : Nat := 10568268652849469449793

theorem tailTrace_69463 : CollatzResearch.WordTrace tailWord_69463 prefixEnd_69463 10568268652849469449793 := by
  unfold tailWord_69463
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533523747354889181021043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1689015831569926120680695 2533523747354889181021043)
  ·
    refine ⟨3800285621032333771531565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2533523747354889181021043 3800285621032333771531565)
    ·
      refine ⟨1425107107887125164324337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3800285621032333771531565 1425107107887125164324337)
      ·
        refine ⟨1068830330915343873243253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1425107107887125164324337 1068830330915343873243253)
        ·
          refine ⟨100202843523313488116555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1068830330915343873243253 100202843523313488116555)
          ·
            refine ⟨150304265284970232174833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100202843523313488116555 150304265284970232174833)
            ·
              refine ⟨112728198963727674131125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150304265284970232174833 112728198963727674131125)
              ·
                refine ⟨10568268652849469449793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112728198963727674131125 10568268652849469449793)
                ·
                  rfl

theorem cell20_69463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_69463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69463 prefixEnd_69463 := by exact prefixLift 69463
  have htrace : WordTrace (prefixWord ++ tailWord_69463) baseStart_69463 baseEnd_69463 := by
    simpa [prefixWord, tailWord_69463, baseEnd_69463] using wordTrace_append hprefix tailTrace_69463
  have hstable : (prefixWord ++ tailWord_69463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69463).length < 2 ^ (prefixWord ++ tailWord_69463).sum := by decide
  have hdescent : baseEnd_69463 < baseStart_69463 := by decide
  rcases family_descends (prefixWord ++ tailWord_69463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69484 : List Nat := [2, 2, 1, 1, 4, 2, 2, 6]
def baseStart_69484 : Nat := 118140960795 + 69484 * 2 ^ 59
def prefixEnd_69484 : Nat := 4983230072969 + 3 ^ 40 * 69484 * 2
def baseEnd_69484 : Nat := 10571463643588556216431

theorem tailTrace_69484 : CollatzResearch.WordTrace tailWord_69484 prefixEnd_69484 10571463643588556216431 := by
  unfold tailWord_69484
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267144840139404883767753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1689526453519206511690337 1267144840139404883767753)
  ·
    refine ⟨950358630104553662825815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1267144840139404883767753 950358630104553662825815)
    ·
      refine ⟨1425537945156830494238723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950358630104553662825815 1425537945156830494238723)
      ·
        refine ⟨2138306917735245741358085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425537945156830494238723 2138306917735245741358085)
        ·
          refine ⟨400932547075358576504641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2138306917735245741358085 400932547075358576504641)
          ·
            refine ⟨300699410306518932378481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400932547075358576504641 300699410306518932378481)
            ·
              refine ⟨225524557729889199283861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300699410306518932378481 225524557729889199283861)
              ·
                refine ⟨10571463643588556216431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225524557729889199283861 10571463643588556216431)
                ·
                  rfl

theorem cell20_69484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_69484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69484 prefixEnd_69484 := by exact prefixLift 69484
  have htrace : WordTrace (prefixWord ++ tailWord_69484) baseStart_69484 baseEnd_69484 := by
    simpa [prefixWord, tailWord_69484, baseEnd_69484] using wordTrace_append hprefix tailTrace_69484
  have hstable : (prefixWord ++ tailWord_69484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69484).length < 2 ^ (prefixWord ++ tailWord_69484).sum := by decide
  have hdescent : baseEnd_69484 < baseStart_69484 := by decide
  rcases family_descends (prefixWord ++ tailWord_69484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69508 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_69508 : Nat := 118140960795 + 69508 * 2 ^ 59
def prefixEnd_69508 : Nat := 4983230072969 + 3 ^ 40 * 69508 * 2
def baseEnd_69508 : Nat := 31725345184728251849195

theorem tailTrace_69508 : CollatzResearch.WordTrace tailWord_69508 prefixEnd_69508 31725345184728251849195 := by
  unfold tailWord_69508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267582516095930933204589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1690110021461241244272785 1267582516095930933204589)
  ·
    refine ⟨475343443535974099951721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1267582516095930933204589 475343443535974099951721)
    ·
      refine ⟨356507582651980574963791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 475343443535974099951721 356507582651980574963791)
      ·
        refine ⟨534761373977970862445687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356507582651980574963791 534761373977970862445687)
        ·
          refine ⟨802142060966956293668531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534761373977970862445687 802142060966956293668531)
          ·
            refine ⟨1203213091450434440502797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802142060966956293668531 1203213091450434440502797)
            ·
              refine ⟨451204909293912915188549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1203213091450434440502797 451204909293912915188549)
              ·
                refine ⟨84600920492608671597853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451204909293912915188549 84600920492608671597853)
                ·
                  refine ⟨31725345184728251849195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84600920492608671597853 31725345184728251849195)
                  ·
                    rfl

theorem cell20_69508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_69508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69508 prefixEnd_69508 := by exact prefixLift 69508
  have htrace : WordTrace (prefixWord ++ tailWord_69508) baseStart_69508 baseEnd_69508 := by
    simpa [prefixWord, tailWord_69508, baseEnd_69508] using wordTrace_append hprefix tailTrace_69508
  have hstable : (prefixWord ++ tailWord_69508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69508).length < 2 ^ (prefixWord ++ tailWord_69508).sum := by decide
  have hdescent : baseEnd_69508 < baseStart_69508 := by decide
  rcases family_descends (prefixWord ++ tailWord_69508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69511 : List Nat := [1, 1, 4, 2, 4, 1, 1, 4, 2]
def baseStart_69511 : Nat := 118140960795 + 69511 * 2 ^ 59
def prefixEnd_69511 : Nat := 4983230072969 + 3 ^ 40 * 69511 * 2
def baseEnd_69511 : Nat := 31726714466473574749183

theorem tailTrace_69511 : CollatzResearch.WordTrace tailWord_69511 prefixEnd_69511 31726714466473574749183 := by
  unfold tailWord_69511
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535274451180993378768387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1690182967453995585845591 2535274451180993378768387)
  ·
    refine ⟨3802911676771490068152581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2535274451180993378768387 3802911676771490068152581)
    ·
      refine ⟨713045939394654387778609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3802911676771490068152581 713045939394654387778609)
      ·
        refine ⟨534784454545990790833957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 713045939394654387778609 534784454545990790833957)
        ·
          refine ⟨100272085227373273281367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 534784454545990790833957 100272085227373273281367)
          ·
            refine ⟨150408127841059909922051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100272085227373273281367 150408127841059909922051)
            ·
              refine ⟨225612191761589864883077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150408127841059909922051 225612191761589864883077)
              ·
                refine ⟨42302285955298099665577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225612191761589864883077 42302285955298099665577)
                ·
                  refine ⟨31726714466473574749183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42302285955298099665577 31726714466473574749183)
                  ·
                    rfl

theorem cell20_69511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 2].length) (baseStart_69511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69511 prefixEnd_69511 := by exact prefixLift 69511
  have htrace : WordTrace (prefixWord ++ tailWord_69511) baseStart_69511 baseEnd_69511 := by
    simpa [prefixWord, tailWord_69511, baseEnd_69511] using wordTrace_append hprefix tailTrace_69511
  have hstable : (prefixWord ++ tailWord_69511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69511).length < 2 ^ (prefixWord ++ tailWord_69511).sum := by decide
  have hdescent : baseEnd_69511 < baseStart_69511 := by decide
  rcases family_descends (prefixWord ++ tailWord_69511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69532 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_69532 : Nat := 118140960795 + 69532 * 2 ^ 59
def prefixEnd_69532 : Nat := 4983230072969 + 3 ^ 40 * 69532 * 2
def baseEnd_69532 : Nat := 31736299438690835049097

theorem tailTrace_69532 : CollatzResearch.WordTrace tailWord_69532 prefixEnd_69532 31736299438690835049097 := by
  unfold tailWord_69532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268020192052456982641425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1690693589403275976855233 1268020192052456982641425)
  ·
    refine ⟨951015144039342736981069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1268020192052456982641425 951015144039342736981069)
    ·
      refine ⟨356630679014753526367901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 951015144039342736981069 356630679014753526367901)
      ·
        refine ⟨133736504630532572387963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356630679014753526367901 133736504630532572387963)
        ·
          refine ⟨200604756945798858581945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133736504630532572387963 200604756945798858581945)
          ·
            refine ⟨150453567709349143936459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200604756945798858581945 150453567709349143936459)
            ·
              refine ⟨225680351564023715904689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150453567709349143936459 225680351564023715904689)
              ·
                refine ⟨169260263673017786928517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225680351564023715904689 169260263673017786928517)
                ·
                  refine ⟨31736299438690835049097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169260263673017786928517 31736299438690835049097)
                  ·
                    rfl

theorem cell20_69532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_69532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69532 prefixEnd_69532 := by exact prefixLift 69532
  have htrace : WordTrace (prefixWord ++ tailWord_69532) baseStart_69532 baseEnd_69532 := by
    simpa [prefixWord, tailWord_69532, baseEnd_69532] using wordTrace_append hprefix tailTrace_69532
  have hstable : (prefixWord ++ tailWord_69532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69532).length < 2 ^ (prefixWord ++ tailWord_69532).sum := by decide
  have hdescent : baseEnd_69532 < baseStart_69532 := by decide
  rcases family_descends (prefixWord ++ tailWord_69532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69556 : List Nat := [2, 5, 2, 1, 2, 1, 7]
def baseStart_69556 : Nat := 118140960795 + 69556 * 2 ^ 59
def prefixEnd_69556 : Nat := 4983230072969 + 3 ^ 40 * 69556 * 2
def baseEnd_69556 : Nat := 3527472632517046472111

theorem tailTrace_69556 : CollatzResearch.WordTrace tailWord_69556 prefixEnd_69556 3527472632517046472111 := by
  unfold tailWord_69556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268457868008983032078261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1691277157345310709437681 1268457868008983032078261)
  ·
    refine ⟨118917925125842159257337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1268457868008983032078261 118917925125842159257337)
    ·
      refine ⟨89188443844381619443003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118917925125842159257337 89188443844381619443003)
      ·
        refine ⟨133782665766572429164505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89188443844381619443003 133782665766572429164505)
        ·
          refine ⟨100336999324929321873379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133782665766572429164505 100336999324929321873379)
          ·
            refine ⟨150505498987393982810069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100336999324929321873379 150505498987393982810069)
            ·
              refine ⟨3527472632517046472111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150505498987393982810069 3527472632517046472111)
              ·
                rfl

theorem cell20_69556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 7].length) (baseStart_69556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69556 prefixEnd_69556 := by exact prefixLift 69556
  have htrace : WordTrace (prefixWord ++ tailWord_69556) baseStart_69556 baseEnd_69556 := by
    simpa [prefixWord, tailWord_69556, baseEnd_69556] using wordTrace_append hprefix tailTrace_69556
  have hstable : (prefixWord ++ tailWord_69556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69556).length < 2 ^ (prefixWord ++ tailWord_69556).sum := by decide
  have hdescent : baseEnd_69556 < baseStart_69556 := by decide
  rcases family_descends (prefixWord ++ tailWord_69556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69567 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_69567 : Nat := 118140960795 + 69567 * 2 ^ 59
def prefixEnd_69567 : Nat := 4983230072969 + 3 ^ 40 * 69567 * 2
def baseEnd_69567 : Nat := 31752274392386268882287

theorem tailTrace_69567 : CollatzResearch.WordTrace tailWord_69567 prefixEnd_69567 31752274392386268882287 := by
  unfold tailWord_69567
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537316938978114942806955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1691544625985409961871303 2537316938978114942806955)
  ·
    refine ⟨3805975408467172414210433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2537316938978114942806955 3805975408467172414210433)
    ·
      refine ⟨2854481556350379310657825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3805975408467172414210433 2854481556350379310657825)
      ·
        refine ⟨2140861167262784482993369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2854481556350379310657825 2140861167262784482993369)
        ·
          refine ⟨1605645875447088362245027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2140861167262784482993369 1605645875447088362245027)
          ·
            refine ⟨2408468813170632543367541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605645875447088362245027 2408468813170632543367541)
            ·
              refine ⟨225793951234746800940707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2408468813170632543367541 225793951234746800940707)
              ·
                refine ⟨338690926852120201411061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225793951234746800940707 338690926852120201411061)
                ·
                  refine ⟨31752274392386268882287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338690926852120201411061 31752274392386268882287)
                  ·
                    rfl

theorem cell20_69567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_69567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69567 prefixEnd_69567 := by exact prefixLift 69567
  have htrace : WordTrace (prefixWord ++ tailWord_69567) baseStart_69567 baseEnd_69567 := by
    simpa [prefixWord, tailWord_69567, baseEnd_69567] using wordTrace_append hprefix tailTrace_69567
  have hstable : (prefixWord ++ tailWord_69567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69567).length < 2 ^ (prefixWord ++ tailWord_69567).sum := by decide
  have hdescent : baseEnd_69567 < baseStart_69567 := by decide
  rcases family_descends (prefixWord ++ tailWord_69567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69590 : List Nat := [5, 2, 1, 1, 4, 1, 2, 4]
def baseStart_69590 : Nat := 118140960795 + 69590 * 2 ^ 59
def prefixEnd_69590 : Nat := 4983230072969 + 3 ^ 40 * 69590 * 2
def baseEnd_69590 : Nat := 10587590739700137038509

theorem tailTrace_69590 : CollatzResearch.WordTrace tailWord_69590 prefixEnd_69590 10587590739700137038509 := by
  unfold tailWord_69590
  simp only [CollatzResearch.WordTrace]
  refine ⟨158634738618424366930889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1692103878596526580596149 158634738618424366930889)
  ·
    refine ⟨118976053963818275198167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158634738618424366930889 118976053963818275198167)
    ·
      refine ⟨178464080945727412797251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118976053963818275198167 178464080945727412797251)
      ·
        refine ⟨267696121418591119195877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178464080945727412797251 267696121418591119195877)
        ·
          refine ⟨50193022765985834849227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267696121418591119195877 50193022765985834849227)
          ·
            refine ⟨75289534148978752273841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50193022765985834849227 75289534148978752273841)
            ·
              refine ⟨56467150611734064205381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75289534148978752273841 56467150611734064205381)
              ·
                refine ⟨10587590739700137038509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56467150611734064205381 10587590739700137038509)
                ·
                  rfl

theorem cell20_69590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_69590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69590 prefixEnd_69590 := by exact prefixLift 69590
  have htrace : WordTrace (prefixWord ++ tailWord_69590) baseStart_69590 baseEnd_69590 := by
    simpa [prefixWord, tailWord_69590, baseEnd_69590] using wordTrace_append hprefix tailTrace_69590
  have hstable : (prefixWord ++ tailWord_69590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69590).length < 2 ^ (prefixWord ++ tailWord_69590).sum := by decide
  have hdescent : baseEnd_69590 < baseStart_69590 := by decide
  rcases family_descends (prefixWord ++ tailWord_69590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69594 : List Nat := [3, 1, 1, 2, 5, 2, 2, 4]
def baseStart_69594 : Nat := 118140960795 + 69594 * 2 ^ 59
def prefixEnd_69594 : Nat := 4983230072969 + 3 ^ 40 * 69594 * 2
def baseEnd_69594 : Nat := 10588199309364724994059

theorem tailTrace_69594 : CollatzResearch.WordTrace tailWord_69594 prefixEnd_69594 10588199309364724994059 := by
  unfold tailWord_69594
  simp only [CollatzResearch.WordTrace]
  refine ⟨634575427470074638509959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1692201139920199036026557 634575427470074638509959)
  ·
    refine ⟨951863141205111957764939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 634575427470074638509959 951863141205111957764939)
    ·
      refine ⟨1427794711807667936647409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 951863141205111957764939 1427794711807667936647409)
      ·
        refine ⟨1070846033855750952485557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1427794711807667936647409 1070846033855750952485557)
        ·
          refine ⟨100391815673976651795521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1070846033855750952485557 100391815673976651795521)
          ·
            refine ⟨75293861755482488846641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100391815673976651795521 75293861755482488846641)
            ·
              refine ⟨56470396316611866634981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75293861755482488846641 56470396316611866634981)
              ·
                refine ⟨10588199309364724994059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56470396316611866634981 10588199309364724994059)
                ·
                  rfl

theorem cell20_69594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_69594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69594 prefixEnd_69594 := by exact prefixLift 69594
  have htrace : WordTrace (prefixWord ++ tailWord_69594) baseStart_69594 baseEnd_69594 := by
    simpa [prefixWord, tailWord_69594, baseEnd_69594] using wordTrace_append hprefix tailTrace_69594
  have hstable : (prefixWord ++ tailWord_69594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69594).length < 2 ^ (prefixWord ++ tailWord_69594).sum := by decide
  have hdescent : baseEnd_69594 < baseStart_69594 := by decide
  rcases family_descends (prefixWord ++ tailWord_69594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69612 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_69612 : Nat := 118140960795 + 69612 * 2 ^ 59
def prefixEnd_69612 : Nat := 4983230072969 + 3 ^ 40 * 69612 * 2
def baseEnd_69612 : Nat := 31772813618566112382103

theorem tailTrace_69612 : CollatzResearch.WordTrace tailWord_69612 prefixEnd_69612 31772813618566112382103 := by
  unfold tailWord_69612
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269479111907543814097545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1692638815876725085463393 1269479111907543814097545)
  ·
    refine ⟨952109333930657860573159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1269479111907543814097545 952109333930657860573159)
    ·
      refine ⟨1428164000895986790859739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952109333930657860573159 1428164000895986790859739)
      ·
        refine ⟨2142246001343980186289609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428164000895986790859739 2142246001343980186289609)
        ·
          refine ⟨1606684501007985139717207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2142246001343980186289609 1606684501007985139717207)
          ·
            refine ⟨2410026751511977709575811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606684501007985139717207 2410026751511977709575811)
            ·
              refine ⟨3615040127267966564363717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410026751511977709575811 3615040127267966564363717)
              ·
                refine ⟨677820023862743730818197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3615040127267966564363717 677820023862743730818197)
                ·
                  refine ⟨31772813618566112382103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 677820023862743730818197 31772813618566112382103)
                  ·
                    rfl

theorem cell20_69612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_69612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69612 prefixEnd_69612 := by exact prefixLift 69612
  have htrace : WordTrace (prefixWord ++ tailWord_69612) baseStart_69612 baseEnd_69612 := by
    simpa [prefixWord, tailWord_69612, baseEnd_69612] using wordTrace_append hprefix tailTrace_69612
  have hstable : (prefixWord ++ tailWord_69612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69612).length < 2 ^ (prefixWord ++ tailWord_69612).sum := by decide
  have hdescent : baseEnd_69612 < baseStart_69612 := by decide
  rcases family_descends (prefixWord ++ tailWord_69612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69625 : List Nat := [1, 2, 1, 3, 1, 5, 3, 2, 2]
def baseStart_69625 : Nat := 118140960795 + 69625 * 2 ^ 59
def prefixEnd_69625 : Nat := 4983230072969 + 3 ^ 40 * 69625 * 2
def baseEnd_69625 : Nat := 31778747172795844948717

theorem tailTrace_69625 : CollatzResearch.WordTrace tailWord_69625 prefixEnd_69625 31778747172795844948717 := by
  unfold tailWord_69625
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539432372767990848418329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1692954915178660565612219 2539432372767990848418329)
  ·
    refine ⟨1904574279575993136313747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2539432372767990848418329 1904574279575993136313747)
    ·
      refine ⟨2856861419363989704470621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1904574279575993136313747 2856861419363989704470621)
      ·
        refine ⟨1071323032261496139176483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2856861419363989704470621 1071323032261496139176483)
        ·
          refine ⟨1606984548392244208764725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071323032261496139176483 1606984548392244208764725)
          ·
            refine ⟨150654801411772894571693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1606984548392244208764725 150654801411772894571693)
            ·
              refine ⟨56495550529414835464385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150654801411772894571693 56495550529414835464385)
              ·
                refine ⟨42371662897061126598289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56495550529414835464385 42371662897061126598289)
                ·
                  refine ⟨31778747172795844948717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42371662897061126598289 31778747172795844948717)
                  ·
                    rfl

theorem cell20_69625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_69625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69625 prefixEnd_69625 := by exact prefixLift 69625
  have htrace : WordTrace (prefixWord ++ tailWord_69625) baseStart_69625 baseEnd_69625 := by
    simpa [prefixWord, tailWord_69625, baseEnd_69625] using wordTrace_append hprefix tailTrace_69625
  have hstable : (prefixWord ++ tailWord_69625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69625).length < 2 ^ (prefixWord ++ tailWord_69625).sum := by decide
  have hdescent : baseEnd_69625 < baseStart_69625 := by decide
  rcases family_descends (prefixWord ++ tailWord_69625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69629 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_69629 : Nat := 118140960795 + 69629 * 2 ^ 59
def prefixEnd_69629 : Nat := 4983230072969 + 3 ^ 40 * 69629 * 2
def baseEnd_69629 : Nat := 31780572881789608815367

theorem tailTrace_69629 : CollatzResearch.WordTrace tailWord_69629 prefixEnd_69629 31780572881789608815367 := by
  unfold tailWord_69629
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539578264753499531563941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1693052176502333021042627 2539578264753499531563941)
  ·
    refine ⟨476170924641281162168239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2539578264753499531563941 476170924641281162168239)
    ·
      refine ⟨714256386961921743252359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476170924641281162168239 714256386961921743252359)
      ·
        refine ⟨1071384580442882614878539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714256386961921743252359 1071384580442882614878539)
        ·
          refine ⟨1607076870664323922317809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071384580442882614878539 1607076870664323922317809)
          ·
            refine ⟨1205307652998242941738357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607076870664323922317809 1205307652998242941738357)
            ·
              refine ⟨112997592468585275787971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1205307652998242941738357 112997592468585275787971)
              ·
                refine ⟨169496388702877913681957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112997592468585275787971 169496388702877913681957)
                ·
                  refine ⟨31780572881789608815367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169496388702877913681957 31780572881789608815367)
                  ·
                    rfl

theorem cell20_69629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_69629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69629 prefixEnd_69629 := by exact prefixLift 69629
  have htrace : WordTrace (prefixWord ++ tailWord_69629) baseStart_69629 baseEnd_69629 := by
    simpa [prefixWord, tailWord_69629, baseEnd_69629] using wordTrace_append hprefix tailTrace_69629
  have hstable : (prefixWord ++ tailWord_69629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69629).length < 2 ^ (prefixWord ++ tailWord_69629).sum := by decide
  have hdescent : baseEnd_69629 < baseStart_69629 := by decide
  rcases family_descends (prefixWord ++ tailWord_69629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69639 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 3]
def baseStart_69639 : Nat := 118140960795 + 69639 * 2 ^ 59
def prefixEnd_69639 : Nat := 4983230072969 + 3 ^ 40 * 69639 * 2
def baseEnd_69639 : Nat := 31785137154274018481993

theorem tailTrace_69639 : CollatzResearch.WordTrace tailWord_69639 prefixEnd_69639 31785137154274018481993 := by
  unfold tailWord_69639
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539942994717271239427971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1693295329811514159618647 2539942994717271239427971)
  ·
    refine ⟨3809914492075906859141957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2539942994717271239427971 3809914492075906859141957)
    ·
      refine ⟨714358967264232536089117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3809914492075906859141957 714358967264232536089117)
      ·
        refine ⟨267884612724087201033419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 714358967264232536089117 267884612724087201033419)
        ·
          refine ⟨401826919086130801550129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267884612724087201033419 401826919086130801550129)
          ·
            refine ⟨301370189314598101162597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401826919086130801550129 301370189314598101162597)
            ·
              refine ⟨56506910496487143967987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301370189314598101162597 56506910496487143967987)
              ·
                refine ⟨84760365744730715951981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56506910496487143967987 84760365744730715951981)
                ·
                  refine ⟨31785137154274018481993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84760365744730715951981 31785137154274018481993)
                  ·
                    rfl

theorem cell20_69639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 3].length) (baseStart_69639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69639 prefixEnd_69639 := by exact prefixLift 69639
  have htrace : WordTrace (prefixWord ++ tailWord_69639) baseStart_69639 baseEnd_69639 := by
    simpa [prefixWord, tailWord_69639, baseEnd_69639] using wordTrace_append hprefix tailTrace_69639
  have hstable : (prefixWord ++ tailWord_69639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69639).length < 2 ^ (prefixWord ++ tailWord_69639).sum := by decide
  have hdescent : baseEnd_69639 < baseStart_69639 := by decide
  rcases family_descends (prefixWord ++ tailWord_69639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69674 : List Nat := [3, 1, 4, 1, 2, 9]
def baseStart_69674 : Nat := 118140960795 + 69674 * 2 ^ 59
def prefixEnd_69674 : Nat := 4983230072969 + 3 ^ 40 * 69674 * 2
def baseEnd_69674 : Nat := 1177818966961831567229

theorem tailTrace_69674 : CollatzResearch.WordTrace tailWord_69674 prefixEnd_69674 1177818966961831567229 := by
  unfold tailWord_69674
  simp only [CollatzResearch.WordTrace]
  refine ⟨635304887397618054238019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1694146366393648144634717 635304887397618054238019)
  ·
    refine ⟨952957331096427081357029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 635304887397618054238019 952957331096427081357029)
    ·
      refine ⟨178679499580580077754443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 952957331096427081357029 178679499580580077754443)
      ·
        refine ⟨268019249370870116631665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178679499580580077754443 268019249370870116631665)
        ·
          refine ⟨201014437028152587473749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268019249370870116631665 201014437028152587473749)
          ·
            refine ⟨1177818966961831567229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 201014437028152587473749 1177818966961831567229)
            ·
              rfl

theorem cell20_69674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 9].length) (baseStart_69674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69674 prefixEnd_69674 := by exact prefixLift 69674
  have htrace : WordTrace (prefixWord ++ tailWord_69674) baseStart_69674 baseEnd_69674 := by
    simpa [prefixWord, tailWord_69674, baseEnd_69674] using wordTrace_append hprefix tailTrace_69674
  have hstable : (prefixWord ++ tailWord_69674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69674).length < 2 ^ (prefixWord ++ tailWord_69674).sum := by decide
  have hdescent : baseEnd_69674 < baseStart_69674 := by decide
  rcases family_descends (prefixWord ++ tailWord_69674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69718 : List Nat := [5, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_69718 : Nat := 118140960795 + 69718 * 2 ^ 59
def prefixEnd_69718 : Nat := 4983230072969 + 3 ^ 40 * 69718 * 2
def baseEnd_69718 : Nat := 31821194906900854848337

theorem tailTrace_69718 : CollatzResearch.WordTrace tailWord_69718 prefixEnd_69718 31821194906900854848337 := by
  unfold tailWord_69718
  simp only [CollatzResearch.WordTrace]
  refine ⟨158926522589441733222113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1695216240954045154369205 158926522589441733222113)
  ·
    refine ⟨119194891942081299916585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158926522589441733222113 119194891942081299916585)
    ·
      refine ⟨89396168956560974937439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119194891942081299916585 89396168956560974937439)
      ·
        refine ⟨134094253434841462406159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89396168956560974937439 134094253434841462406159)
        ·
          refine ⟨201141380152262193609239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134094253434841462406159 201141380152262193609239)
          ·
            refine ⟨301712070228393290413859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201141380152262193609239 301712070228393290413859)
            ·
              refine ⟨452568105342589935620789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301712070228393290413859 452568105342589935620789)
              ·
                refine ⟨42428259875867806464449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 452568105342589935620789 42428259875867806464449)
                ·
                  refine ⟨31821194906900854848337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42428259875867806464449 31821194906900854848337)
                  ·
                    rfl

theorem cell20_69718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_69718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69718 prefixEnd_69718 := by exact prefixLift 69718
  have htrace : WordTrace (prefixWord ++ tailWord_69718) baseStart_69718 baseEnd_69718 := by
    simpa [prefixWord, tailWord_69718, baseEnd_69718] using wordTrace_append hprefix tailTrace_69718
  have hstable : (prefixWord ++ tailWord_69718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69718).length < 2 ^ (prefixWord ++ tailWord_69718).sum := by decide
  have hdescent : baseEnd_69718 < baseStart_69718 := by decide
  rcases family_descends (prefixWord ++ tailWord_69718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69722 : List Nat := [3, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_69722 : Nat := 118140960795 + 69722 * 2 ^ 59
def prefixEnd_69722 : Nat := 4983230072969 + 3 ^ 40 * 69722 * 2
def baseEnd_69722 : Nat := 31823020615894618714987

theorem tailTrace_69722 : CollatzResearch.WordTrace tailWord_69722 prefixEnd_69722 31823020615894618714987 := by
  unfold tailWord_69722
  simp only [CollatzResearch.WordTrace]
  refine ⟨635742563354144103674855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1695313502277717609799613 635742563354144103674855)
  ·
    refine ⟨953613845031216155512283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 635742563354144103674855 953613845031216155512283)
    ·
      refine ⟨1430420767546824233268425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953613845031216155512283 1430420767546824233268425)
      ·
        refine ⟨1072815575660118174951319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1430420767546824233268425 1072815575660118174951319)
        ·
          refine ⟨1609223363490177262426979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072815575660118174951319 1609223363490177262426979)
          ·
            refine ⟨2413835045235265893640469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609223363490177262426979 2413835045235265893640469)
            ·
              refine ⟨113148517745403088764397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2413835045235265893640469 113148517745403088764397)
              ·
                refine ⟨42430694154526158286649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113148517745403088764397 42430694154526158286649)
                ·
                  refine ⟨31823020615894618714987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42430694154526158286649 31823020615894618714987)
                  ·
                    rfl

theorem cell20_69722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_69722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69722 prefixEnd_69722 := by exact prefixLift 69722
  have htrace : WordTrace (prefixWord ++ tailWord_69722) baseStart_69722 baseEnd_69722 := by
    simpa [prefixWord, tailWord_69722, baseEnd_69722] using wordTrace_append hprefix tailTrace_69722
  have hstable : (prefixWord ++ tailWord_69722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69722).length < 2 ^ (prefixWord ++ tailWord_69722).sum := by decide
  have hdescent : baseEnd_69722 < baseStart_69722 := by decide
  rcases family_descends (prefixWord ++ tailWord_69722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69743 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_69743 : Nat := 118140960795 + 69743 * 2 ^ 59
def prefixEnd_69743 : Nat := 4983230072969 + 3 ^ 40 * 69743 * 2
def baseEnd_69743 : Nat := 31832605588111879014901

theorem tailTrace_69743 : CollatzResearch.WordTrace tailWord_69743 prefixEnd_69743 31832605588111879014901 := by
  unfold tailWord_69743
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543736186340497001213883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1695824124226998000809255 2543736186340497001213883)
  ·
    refine ⟨3815604279510745501820825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2543736186340497001213883 3815604279510745501820825)
    ·
      refine ⟨2861703209633059126365619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3815604279510745501820825 2861703209633059126365619)
      ·
        refine ⟨4292554814449588689548429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861703209633059126365619 4292554814449588689548429)
        ·
          refine ⟨1609708055418595758580661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4292554814449588689548429 1609708055418595758580661)
          ·
            refine ⟨150910130195493352366937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1609708055418595758580661 150910130195493352366937)
            ·
              refine ⟨113182597646620014275203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150910130195493352366937 113182597646620014275203)
              ·
                refine ⟨169773896469930021412805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113182597646620014275203 169773896469930021412805)
                ·
                  refine ⟨31832605588111879014901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169773896469930021412805 31832605588111879014901)
                  ·
                    rfl

theorem cell20_69743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_69743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69743 prefixEnd_69743 := by exact prefixLift 69743
  have htrace : WordTrace (prefixWord ++ tailWord_69743) baseStart_69743 baseEnd_69743 := by
    simpa [prefixWord, tailWord_69743, baseEnd_69743] using wordTrace_append hprefix tailTrace_69743
  have hstable : (prefixWord ++ tailWord_69743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69743).length < 2 ^ (prefixWord ++ tailWord_69743).sum := by decide
  have hdescent : baseEnd_69743 < baseStart_69743 := by decide
  rcases family_descends (prefixWord ++ tailWord_69743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69753 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 3]
def baseStart_69753 : Nat := 118140960795 + 69753 * 2 ^ 59
def prefixEnd_69753 : Nat := 4983230072969 + 3 ^ 40 * 69753 * 2
def baseEnd_69753 : Nat := 31837169860596288681527

theorem tailTrace_69753 : CollatzResearch.WordTrace tailWord_69753 prefixEnd_69753 31837169860596288681527 := by
  unfold tailWord_69753
  simp only [CollatzResearch.WordTrace]
  refine ⟨2544100916304268709077913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1696067277536179139385275 2544100916304268709077913)
  ·
    refine ⟨1908075687228201531808435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2544100916304268709077913 1908075687228201531808435)
    ·
      refine ⟨2862113530842302297712653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1908075687228201531808435 2862113530842302297712653)
      ·
        refine ⟨1073292574065863361642245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2862113530842302297712653 1073292574065863361642245)
        ·
          refine ⟨201242357637349380307921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1073292574065863361642245 201242357637349380307921)
          ·
            refine ⟨150931768228012035230941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201242357637349380307921 150931768228012035230941)
            ·
              refine ⟨56599413085504513211603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150931768228012035230941 56599413085504513211603)
              ·
                refine ⟨84899119628256769817405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56599413085504513211603 84899119628256769817405)
                ·
                  refine ⟨31837169860596288681527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84899119628256769817405 31837169860596288681527)
                  ·
                    rfl

theorem cell20_69753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_69753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69753 prefixEnd_69753 := by exact prefixLift 69753
  have htrace : WordTrace (prefixWord ++ tailWord_69753) baseStart_69753 baseEnd_69753 := by
    simpa [prefixWord, tailWord_69753, baseEnd_69753] using wordTrace_append hprefix tailTrace_69753
  have hstable : (prefixWord ++ tailWord_69753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69753).length < 2 ^ (prefixWord ++ tailWord_69753).sum := by decide
  have hdescent : baseEnd_69753 < baseStart_69753 := by decide
  rcases family_descends (prefixWord ++ tailWord_69753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69794 : List Nat := [3, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_69794 : Nat := 118140960795 + 69794 * 2 ^ 59
def prefixEnd_69794 : Nat := 4983230072969 + 3 ^ 40 * 69794 * 2
def baseEnd_69794 : Nat := 31855883377782368314693

theorem tailTrace_69794 : CollatzResearch.WordTrace tailWord_69794 prefixEnd_69794 31855883377782368314693 := by
  unfold tailWord_69794
  simp only [CollatzResearch.WordTrace]
  refine ⟨636399077288933177830109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1697064206103821807546957 636399077288933177830109)
  ·
    refine ⟨238649653983349941686291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 636399077288933177830109 238649653983349941686291)
    ·
      refine ⟨357974480975024912529437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238649653983349941686291 357974480975024912529437)
      ·
        refine ⟨134240430365634342198539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357974480975024912529437 134240430365634342198539)
        ·
          refine ⟨201360645548451513297809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134240430365634342198539 201360645548451513297809)
          ·
            refine ⟨151020484161338634973357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201360645548451513297809 151020484161338634973357)
            ·
              refine ⟨56632681560501988115009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151020484161338634973357 56632681560501988115009)
              ·
                refine ⟨42474511170376491086257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56632681560501988115009 42474511170376491086257)
                ·
                  refine ⟨31855883377782368314693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42474511170376491086257 31855883377782368314693)
                  ·
                    rfl

theorem cell20_69794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_69794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69794 prefixEnd_69794 := by exact prefixLift 69794
  have htrace : WordTrace (prefixWord ++ tailWord_69794) baseStart_69794 baseEnd_69794 := by
    simpa [prefixWord, tailWord_69794, baseEnd_69794] using wordTrace_append hprefix tailTrace_69794
  have hstable : (prefixWord ++ tailWord_69794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69794).length < 2 ^ (prefixWord ++ tailWord_69794).sum := by decide
  have hdescent : baseEnd_69794 < baseStart_69794 := by decide
  rcases family_descends (prefixWord ++ tailWord_69794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69805 : List Nat := [1, 5, 2, 1, 2, 2, 2, 5]
def baseStart_69805 : Nat := 118140960795 + 69805 * 2 ^ 59
def prefixEnd_69805 : Nat := 4983230072969 + 3 ^ 40 * 69805 * 2
def baseEnd_69805 : Nat := 10620301359171739649327

theorem tailTrace_69805 : CollatzResearch.WordTrace tailWord_69805 prefixEnd_69805 10620301359171739649327 := by
  unfold tailWord_69805
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545997512115881589970869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1697331674743921059980579 2545997512115881589970869)
  ·
    refine ⟨238687266760863899059769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2545997512115881589970869 238687266760863899059769)
    ·
      refine ⟨179015450070647924294827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238687266760863899059769 179015450070647924294827)
      ·
        refine ⟨268523175105971886442241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179015450070647924294827 268523175105971886442241)
        ·
          refine ⟨201392381329478914831681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268523175105971886442241 201392381329478914831681)
          ·
            refine ⟨151044285997109186123761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201392381329478914831681 151044285997109186123761)
            ·
              refine ⟨113283214497831889592821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151044285997109186123761 113283214497831889592821)
              ·
                refine ⟨10620301359171739649327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113283214497831889592821 10620301359171739649327)
                ·
                  rfl

theorem cell20_69805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_69805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69805 prefixEnd_69805 := by exact prefixLift 69805
  have htrace : WordTrace (prefixWord ++ tailWord_69805) baseStart_69805 baseEnd_69805 := by
    simpa [prefixWord, tailWord_69805, baseEnd_69805] using wordTrace_append hprefix tailTrace_69805
  have hstable : (prefixWord ++ tailWord_69805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69805).length < 2 ^ (prefixWord ++ tailWord_69805).sum := by decide
  have hdescent : baseEnd_69805 < baseStart_69805 := by decide
  rcases family_descends (prefixWord ++ tailWord_69805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69846 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_69846 : Nat := 118140960795 + 69846 * 2 ^ 59
def prefixEnd_69846 : Nat := 4983230072969 + 3 ^ 40 * 69846 * 2
def baseEnd_69846 : Nat := 31879617594701298581147

theorem tailTrace_69846 : CollatzResearch.WordTrace tailWord_69846 prefixEnd_69846 31879617594701298581147 := by
  unfold tailWord_69846
  simp only [CollatzResearch.WordTrace]
  refine ⟨159218306560459099513337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1698328603311563728142261 159218306560459099513337)
  ·
    refine ⟨119413729920344324635003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159218306560459099513337 119413729920344324635003)
    ·
      refine ⟨179120594880516486952505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119413729920344324635003 179120594880516486952505)
      ·
        refine ⟨134340446160387365214379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179120594880516486952505 134340446160387365214379)
        ·
          refine ⟨201510669240581047821569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134340446160387365214379 201510669240581047821569)
          ·
            refine ⟨151133001930435785866177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201510669240581047821569 151133001930435785866177)
            ·
              refine ⟨113349751447826839399633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151133001930435785866177 113349751447826839399633)
              ·
                refine ⟨85012313585870129549725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113349751447826839399633 85012313585870129549725)
                ·
                  refine ⟨31879617594701298581147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85012313585870129549725 31879617594701298581147)
                  ·
                    rfl

theorem cell20_69846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_69846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69846 prefixEnd_69846 := by exact prefixLift 69846
  have htrace : WordTrace (prefixWord ++ tailWord_69846) baseStart_69846 baseEnd_69846 := by
    simpa [prefixWord, tailWord_69846, baseEnd_69846] using wordTrace_append hprefix tailTrace_69846
  have hstable : (prefixWord ++ tailWord_69846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69846).length < 2 ^ (prefixWord ++ tailWord_69846).sum := by decide
  have hdescent : baseEnd_69846 < baseStart_69846 := by decide
  rcases family_descends (prefixWord ++ tailWord_69846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69853 : List Nat := [1, 4, 3, 2, 1, 2, 1, 4, 2]
def baseStart_69853 : Nat := 118140960795 + 69853 * 2 ^ 59
def prefixEnd_69853 : Nat := 4983230072969 + 3 ^ 40 * 69853 * 2
def baseEnd_69853 : Nat := 31882812585440385347785

theorem tailTrace_69853 : CollatzResearch.WordTrace tailWord_69853 prefixEnd_69853 31882812585440385347785 := by
  unfold tailWord_69853
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547748215941985787718213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1698498810627990525145475 2547748215941985787718213)
  ·
    refine ⟨477702790489122335197165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2547748215941985787718213 477702790489122335197165)
    ·
      refine ⟨179138546433420875698937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 477702790489122335197165 179138546433420875698937)
      ·
        refine ⟨134353909825065656774203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179138546433420875698937 134353909825065656774203)
        ·
          refine ⟨201530864737598485161305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134353909825065656774203 201530864737598485161305)
          ·
            refine ⟨151148148553198863870979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201530864737598485161305 151148148553198863870979)
            ·
              refine ⟨226722222829798295806469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151148148553198863870979 226722222829798295806469)
              ·
                refine ⟨42510416780587180463713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 226722222829798295806469 42510416780587180463713)
                ·
                  refine ⟨31882812585440385347785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42510416780587180463713 31882812585440385347785)
                  ·
                    rfl

theorem cell20_69853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_69853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69853 prefixEnd_69853 := by exact prefixLift 69853
  have htrace : WordTrace (prefixWord ++ tailWord_69853) baseStart_69853 baseEnd_69853 := by
    simpa [prefixWord, tailWord_69853, baseEnd_69853] using wordTrace_append hprefix tailTrace_69853
  have hstable : (prefixWord ++ tailWord_69853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69853).length < 2 ^ (prefixWord ++ tailWord_69853).sum := by decide
  have hdescent : baseEnd_69853 < baseStart_69853 := by decide
  rcases family_descends (prefixWord ++ tailWord_69853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69864 : List Nat := [2, 1, 4, 1, 2, 2, 3, 5]
def baseStart_69864 : Nat := 118140960795 + 69864 * 2 ^ 59
def prefixEnd_69864 : Nat := 4983230072969 + 3 ^ 40 * 69864 * 2
def baseEnd_69864 : Nat := 10629277761724411993691

theorem tailTrace_69864 : CollatzResearch.WordTrace tailWord_69864 prefixEnd_69864 10629277761724411993691 := by
  unfold tailWord_69864
  simp only [CollatzResearch.WordTrace]
  refine ⟨1274074709451067333184323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1698766279268089777579097 1274074709451067333184323)
  ·
    refine ⟨1911112064176600999776485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1274074709451067333184323 1911112064176600999776485)
    ·
      refine ⟨358333512033112687458091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1911112064176600999776485 358333512033112687458091)
      ·
        refine ⟨537500268049669031187137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358333512033112687458091 537500268049669031187137)
        ·
          refine ⟨403125201037251773390353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537500268049669031187137 403125201037251773390353)
          ·
            refine ⟨302343900777938830042765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403125201037251773390353 302343900777938830042765)
            ·
              refine ⟨113378962791727061266037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302343900777938830042765 113378962791727061266037)
              ·
                refine ⟨10629277761724411993691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113378962791727061266037 10629277761724411993691)
                ·
                  rfl

theorem cell20_69864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_69864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69864 prefixEnd_69864 := by exact prefixLift 69864
  have htrace : WordTrace (prefixWord ++ tailWord_69864) baseStart_69864 baseEnd_69864 := by
    simpa [prefixWord, tailWord_69864, baseEnd_69864] using wordTrace_append hprefix tailTrace_69864
  have hstable : (prefixWord ++ tailWord_69864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69864).length < 2 ^ (prefixWord ++ tailWord_69864).sum := by decide
  have hdescent : baseEnd_69864 < baseStart_69864 := by decide
  rcases family_descends (prefixWord ++ tailWord_69864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69885 : List Nat := [1, 4, 1, 1, 1, 1, 1, 10]
def baseStart_69885 : Nat := 118140960795 + 69885 * 2 ^ 59
def prefixEnd_69885 : Nat := 4983230072969 + 3 ^ 40 * 69885 * 2
def baseEnd_69885 : Nat := 10632472752463498760329

theorem tailTrace_69885 : CollatzResearch.WordTrace tailWord_69885 prefixEnd_69885 10632472752463498760329 := by
  unfold tailWord_69885
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548915351826055252883109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1699276901217370168588739 2548915351826055252883109)
  ·
    refine ⟨477921628467385359915583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2548915351826055252883109 477921628467385359915583)
    ·
      refine ⟨716882442701078039873375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477921628467385359915583 716882442701078039873375)
      ·
        refine ⟨1075323664051617059810063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716882442701078039873375 1075323664051617059810063)
        ·
          refine ⟨1612985496077425589715095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075323664051617059810063 1612985496077425589715095)
          ·
            refine ⟨2419478244116138384572643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612985496077425589715095 2419478244116138384572643)
            ·
              refine ⟨3629217366174207576858965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2419478244116138384572643 3629217366174207576858965)
              ·
                refine ⟨10632472752463498760329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3629217366174207576858965 10632472752463498760329)
                ·
                  rfl

theorem cell20_69885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_69885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69885 prefixEnd_69885 := by exact prefixLift 69885
  have htrace : WordTrace (prefixWord ++ tailWord_69885) baseStart_69885 baseEnd_69885 := by
    simpa [prefixWord, tailWord_69885, baseEnd_69885] using wordTrace_append hprefix tailTrace_69885
  have hstable : (prefixWord ++ tailWord_69885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69885).length < 2 ^ (prefixWord ++ tailWord_69885).sum := by decide
  have hdescent : baseEnd_69885 < baseStart_69885 := by decide
  rcases family_descends (prefixWord ++ tailWord_69885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69923 : List Nat := [1, 1, 1, 4, 2, 2, 2, 7]
def baseStart_69923 : Nat := 118140960795 + 69923 * 2 ^ 59
def prefixEnd_69923 : Nat := 4983230072969 + 3 ^ 40 * 69923 * 2
def baseEnd_69923 : Nat := 10638254164277084338055

theorem tailTrace_69923 : CollatzResearch.WordTrace tailWord_69923 prefixEnd_69923 10638254164277084338055 := by
  unfold tailWord_69923
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550301325688387742766423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1700200883792258495177615 2550301325688387742766423)
  ·
    refine ⟨3825451988532581614149635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2550301325688387742766423 3825451988532581614149635)
    ·
      refine ⟨5738177982798872421224453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3825451988532581614149635 5738177982798872421224453)
      ·
        refine ⟨1075908371774788578979585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5738177982798872421224453 1075908371774788578979585)
        ·
          refine ⟨806931278831091434234689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075908371774788578979585 806931278831091434234689)
          ·
            refine ⟨605198459123318575676017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806931278831091434234689 605198459123318575676017)
            ·
              refine ⟨453898844342488931757013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605198459123318575676017 453898844342488931757013)
              ·
                refine ⟨10638254164277084338055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 453898844342488931757013 10638254164277084338055)
                ·
                  rfl

theorem cell20_69923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_69923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_69923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_69923 prefixEnd_69923 := by exact prefixLift 69923
  have htrace : WordTrace (prefixWord ++ tailWord_69923) baseStart_69923 baseEnd_69923 := by
    simpa [prefixWord, tailWord_69923, baseEnd_69923] using wordTrace_append hprefix tailTrace_69923
  have hstable : (prefixWord ++ tailWord_69923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69923).length < 2 ^ (prefixWord ++ tailWord_69923).sum := by decide
  have hdescent : baseEnd_69923 < baseStart_69923 := by decide
  rcases family_descends (prefixWord ++ tailWord_69923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70009 : List Nat := [1, 2, 1, 3, 2, 1, 1, 7, 2]
def baseStart_70009 : Nat := 118140960795 + 70009 * 2 ^ 59
def prefixEnd_70009 : Nat := 4983230072969 + 3 ^ 40 * 70009 * 2
def baseEnd_70009 : Nat := 31954015236197176147147

theorem tailTrace_70009 : CollatzResearch.WordTrace tailWord_70009 prefixEnd_70009 31954015236197176147147 := by
  unfold tailWord_70009
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553438003376824430397081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1702292002251216286931387 2553438003376824430397081)
  ·
    refine ⟨1915078502532618322797811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2553438003376824430397081 1915078502532618322797811)
    ·
      refine ⟨2872617753798927484196717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915078502532618322797811 2872617753798927484196717)
      ·
        refine ⟨1077231657674597806573769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2872617753798927484196717 1077231657674597806573769)
        ·
          refine ⟨807923743255948354930327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077231657674597806573769 807923743255948354930327)
          ·
            refine ⟨1211885614883922532395491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807923743255948354930327 1211885614883922532395491)
            ·
              refine ⟨1817828422325883798593237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211885614883922532395491 1817828422325883798593237)
              ·
                refine ⟨42605353648262901529529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1817828422325883798593237 42605353648262901529529)
                ·
                  refine ⟨31954015236197176147147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42605353648262901529529 31954015236197176147147)
                  ·
                    rfl

theorem cell20_70009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_70009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70009 prefixEnd_70009 := by exact prefixLift 70009
  have htrace : WordTrace (prefixWord ++ tailWord_70009) baseStart_70009 baseEnd_70009 := by
    simpa [prefixWord, tailWord_70009, baseEnd_70009] using wordTrace_append hprefix tailTrace_70009
  have hstable : (prefixWord ++ tailWord_70009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70009).length < 2 ^ (prefixWord ++ tailWord_70009).sum := by decide
  have hdescent : baseEnd_70009 < baseStart_70009 := by decide
  rcases family_descends (prefixWord ++ tailWord_70009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70018 : List Nat := [3, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_70018 : Nat := 118140960795 + 70018 * 2 ^ 59
def prefixEnd_70018 : Nat := 4983230072969 + 3 ^ 40 * 70018 * 2
def baseEnd_70018 : Nat := 31958123081433144847111

theorem tailTrace_70018 : CollatzResearch.WordTrace tailWord_70018 prefixEnd_70018 31958123081433144847111 := by
  unfold tailWord_70018
  simp only [CollatzResearch.WordTrace]
  refine ⟨638441565086054741868677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1702510840229479311649805 638441565086054741868677)
  ·
    refine ⟨119707793453635264100377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 638441565086054741868677 119707793453635264100377)
    ·
      refine ⟨89780845090226448075283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119707793453635264100377 89780845090226448075283)
      ·
        refine ⟨134671267635339672112925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89780845090226448075283 134671267635339672112925)
        ·
          refine ⟨50501725363252377042347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134671267635339672112925 50501725363252377042347)
          ·
            refine ⟨75752588044878565563521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50501725363252377042347 75752588044878565563521)
            ·
              refine ⟨56814441033658924172641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75752588044878565563521 56814441033658924172641)
              ·
                refine ⟨42610830775244193129481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56814441033658924172641 42610830775244193129481)
                ·
                  refine ⟨31958123081433144847111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42610830775244193129481 31958123081433144847111)
                  ·
                    rfl

theorem cell20_70018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_70018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70018 prefixEnd_70018 := by exact prefixLift 70018
  have htrace : WordTrace (prefixWord ++ tailWord_70018) baseStart_70018 baseEnd_70018 := by
    simpa [prefixWord, tailWord_70018, baseEnd_70018] using wordTrace_append hprefix tailTrace_70018
  have hstable : (prefixWord ++ tailWord_70018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70018).length < 2 ^ (prefixWord ++ tailWord_70018).sum := by decide
  have hdescent : baseEnd_70018 < baseStart_70018 := by decide
  rcases family_descends (prefixWord ++ tailWord_70018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70040 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_70040 : Nat := 118140960795 + 70040 * 2 ^ 59
def prefixEnd_70040 : Nat := 4983230072969 + 3 ^ 40 * 70040 * 2
def baseEnd_70040 : Nat := 31968164480898846113687

theorem tailTrace_70040 : CollatzResearch.WordTrace tailWord_70040 prefixEnd_70040 31968164480898846113687 := by
  unfold tailWord_70040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1277284333132258362387787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1703045777509677816517049 1277284333132258362387787)
  ·
    refine ⟨1915926499698387543581681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1277284333132258362387787 1915926499698387543581681)
    ·
      refine ⟨1436944874773790657686261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1915926499698387543581681 1436944874773790657686261)
      ·
        refine ⟨134713582010042874158087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1436944874773790657686261 134713582010042874158087)
        ·
          refine ⟨202070373015064311237131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134713582010042874158087 202070373015064311237131)
          ·
            refine ⟨303105559522596466855697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202070373015064311237131 303105559522596466855697)
            ·
              refine ⟨227329169641947350141773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303105559522596466855697 227329169641947350141773)
              ·
                refine ⟨85248438615730256303165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227329169641947350141773 85248438615730256303165)
                ·
                  refine ⟨31968164480898846113687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85248438615730256303165 31968164480898846113687)
                  ·
                    rfl

theorem cell20_70040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_70040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70040 prefixEnd_70040 := by exact prefixLift 70040
  have htrace : WordTrace (prefixWord ++ tailWord_70040) baseStart_70040 baseEnd_70040 := by
    simpa [prefixWord, tailWord_70040, baseEnd_70040] using wordTrace_append hprefix tailTrace_70040
  have hstable : (prefixWord ++ tailWord_70040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70040).length < 2 ^ (prefixWord ++ tailWord_70040).sum := by decide
  have hdescent : baseEnd_70040 < baseStart_70040 := by decide
  rcases family_descends (prefixWord ++ tailWord_70040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70078 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_70078 : Nat := 118140960795 + 70078 * 2 ^ 59
def prefixEnd_70078 : Nat := 4983230072969 + 3 ^ 40 * 70078 * 2
def baseEnd_70078 : Nat := 31985508716339602846865

theorem tailTrace_70078 : CollatzResearch.WordTrace tailWord_70078 prefixEnd_70078 31985508716339602846865 := by
  unfold tailWord_70078
  simp only [CollatzResearch.WordTrace]
  refine ⟨319494330015856151832361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1703969760084566143105925 319494330015856151832361)
  ·
    refine ⟨239620747511892113874271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 319494330015856151832361 239620747511892113874271)
    ·
      refine ⟨359431121267838170811407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239620747511892113874271 359431121267838170811407)
      ·
        refine ⟨539146681901757256217111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359431121267838170811407 539146681901757256217111)
        ·
          refine ⟨808720022852635884325667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539146681901757256217111 808720022852635884325667)
          ·
            refine ⟨1213080034278953826488501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808720022852635884325667 1213080034278953826488501)
            ·
              refine ⟨113726253213651921233297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1213080034278953826488501 113726253213651921233297)
              ·
                refine ⟨85294689910238940924973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113726253213651921233297 85294689910238940924973)
                ·
                  refine ⟨31985508716339602846865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85294689910238940924973 31985508716339602846865)
                  ·
                    rfl

theorem cell20_70078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_70078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70078 prefixEnd_70078 := by exact prefixLift 70078
  have htrace : WordTrace (prefixWord ++ tailWord_70078) baseStart_70078 baseEnd_70078 := by
    simpa [prefixWord, tailWord_70078, baseEnd_70078] using wordTrace_append hprefix tailTrace_70078
  have hstable : (prefixWord ++ tailWord_70078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70078).length < 2 ^ (prefixWord ++ tailWord_70078).sum := by decide
  have hdescent : baseEnd_70078 < baseStart_70078 := by decide
  rcases family_descends (prefixWord ++ tailWord_70078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70106 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_70106 : Nat := 118140960795 + 70106 * 2 ^ 59
def prefixEnd_70106 : Nat := 4983230072969 + 3 ^ 40 * 70106 * 2
def baseEnd_70106 : Nat := 31998288679295949913417

theorem tailTrace_70106 : CollatzResearch.WordTrace tailWord_70106 prefixEnd_70106 31998288679295949913417 := by
  unfold tailWord_70106
  simp only [CollatzResearch.WordTrace]
  refine ⟨639243971006352499169543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1704650589350273331118781 639243971006352499169543)
  ·
    refine ⟨958865956509528748754315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 639243971006352499169543 958865956509528748754315)
    ·
      refine ⟨1438298934764293123131473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 958865956509528748754315 1438298934764293123131473)
      ·
        refine ⟨1078724201073219842348605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1438298934764293123131473 1078724201073219842348605)
        ·
          refine ⟨404521575402457440880727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1078724201073219842348605 404521575402457440880727)
          ·
            refine ⟨606782363103686161321091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404521575402457440880727 606782363103686161321091)
            ·
              refine ⟨910173544655529241981637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606782363103686161321091 910173544655529241981637)
              ·
                refine ⟨170657539622911732871557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 910173544655529241981637 170657539622911732871557)
                ·
                  refine ⟨31998288679295949913417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170657539622911732871557 31998288679295949913417)
                  ·
                    rfl

theorem cell20_70106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_70106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70106 prefixEnd_70106 := by exact prefixLift 70106
  have htrace : WordTrace (prefixWord ++ tailWord_70106) baseStart_70106 baseEnd_70106 := by
    simpa [prefixWord, tailWord_70106, baseEnd_70106] using wordTrace_append hprefix tailTrace_70106
  have hstable : (prefixWord ++ tailWord_70106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70106).length < 2 ^ (prefixWord ++ tailWord_70106).sum := by decide
  have hdescent : baseEnd_70106 < baseStart_70106 := by decide
  rcases family_descends (prefixWord ++ tailWord_70106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70113 : List Nat := [1, 2, 3, 1, 2, 2, 3, 6]
def baseStart_70113 : Nat := 118140960795 + 70113 * 2 ^ 59
def prefixEnd_70113 : Nat := 4983230072969 + 3 ^ 40 * 70113 * 2
def baseEnd_70113 : Nat := 10667161223345012226685

theorem tailTrace_70113 : CollatzResearch.WordTrace tailWord_70113 prefixEnd_70113 10667161223345012226685 := by
  unfold tailWord_70113
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557231195000050192182993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1704820796666700128121995 2557231195000050192182993)
  ·
    refine ⟨1917923396250037644137245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2557231195000050192182993 1917923396250037644137245)
    ·
      refine ⟨719221273593764116551467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1917923396250037644137245 719221273593764116551467)
      ·
        refine ⟨1078831910390646174827201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719221273593764116551467 1078831910390646174827201)
        ·
          refine ⟨809123932792984631120401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1078831910390646174827201 809123932792984631120401)
          ·
            refine ⟨606842949594738473340301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809123932792984631120401 606842949594738473340301)
            ·
              refine ⟨227566106098026927502613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606842949594738473340301 227566106098026927502613)
              ·
                refine ⟨10667161223345012226685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 227566106098026927502613 10667161223345012226685)
                ·
                  rfl

theorem cell20_70113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_70113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70113 prefixEnd_70113 := by exact prefixLift 70113
  have htrace : WordTrace (prefixWord ++ tailWord_70113) baseStart_70113 baseEnd_70113 := by
    simpa [prefixWord, tailWord_70113, baseEnd_70113] using wordTrace_append hprefix tailTrace_70113
  have hstable : (prefixWord ++ tailWord_70113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70113).length < 2 ^ (prefixWord ++ tailWord_70113).sum := by decide
  have hdescent : baseEnd_70113 < baseStart_70113 := by decide
  rcases family_descends (prefixWord ++ tailWord_70113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70199 : List Nat := [1, 1, 3, 1, 2, 3, 3, 4, 2]
def baseStart_70199 : Nat := 118140960795 + 70199 * 2 ^ 59
def prefixEnd_70199 : Nat := 4983230072969 + 3 ^ 40 * 70199 * 2
def baseEnd_70199 : Nat := 32040736413400959813037

theorem tailTrace_70199 : CollatzResearch.WordTrace tailWord_70199 prefixEnd_70199 32040736413400959813037 := by
  unfold tailWord_70199
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560367872688486879813651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1706911915125657919875767 2560367872688486879813651)
  ·
    refine ⟨3840551809032730319720477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560367872688486879813651 3840551809032730319720477)
    ·
      refine ⟨1440206928387273869895179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3840551809032730319720477 1440206928387273869895179)
      ·
        refine ⟨2160310392580910804842769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440206928387273869895179 2160310392580910804842769)
        ·
          refine ⟨1620232794435683103632077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160310392580910804842769 1620232794435683103632077)
          ·
            refine ⟨607587297913381163862029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1620232794435683103632077 607587297913381163862029)
            ·
              refine ⟨227845236717517936448261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607587297913381163862029 227845236717517936448261)
              ·
                refine ⟨42720981884534613084049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227845236717517936448261 42720981884534613084049)
                ·
                  refine ⟨32040736413400959813037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42720981884534613084049 32040736413400959813037)
                  ·
                    rfl

theorem cell20_70199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 2].length) (baseStart_70199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70199 prefixEnd_70199 := by exact prefixLift 70199
  have htrace : WordTrace (prefixWord ++ tailWord_70199) baseStart_70199 baseEnd_70199 := by
    simpa [prefixWord, tailWord_70199, baseEnd_70199] using wordTrace_append hprefix tailTrace_70199
  have hstable : (prefixWord ++ tailWord_70199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70199).length < 2 ^ (prefixWord ++ tailWord_70199).sum := by decide
  have hdescent : baseEnd_70199 < baseStart_70199 := by decide
  rcases family_descends (prefixWord ++ tailWord_70199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70213 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 3]
def baseStart_70213 : Nat := 118140960795 + 70213 * 2 ^ 59
def prefixEnd_70213 : Nat := 4983230072969 + 3 ^ 40 * 70213 * 2
def baseEnd_70213 : Nat := 32047126394879133346313

theorem tailTrace_70213 : CollatzResearch.WordTrace tailWord_70213 prefixEnd_70213 32047126394879133346313 := by
  unfold tailWord_70213
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560878494637767270823293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1707252329758511513882195 2560878494637767270823293)
  ·
    refine ⟨960329435489162726558735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2560878494637767270823293 960329435489162726558735)
    ·
      refine ⟨1440494153233744089838103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960329435489162726558735 1440494153233744089838103)
      ·
        refine ⟨2160741229850616134757155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440494153233744089838103 2160741229850616134757155)
        ·
          refine ⟨3241111844775924202135733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160741229850616134757155 3241111844775924202135733)
          ·
            refine ⟨303854235447742893950225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3241111844775924202135733 303854235447742893950225)
            ·
              refine ⟨227890676585807170462669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303854235447742893950225 227890676585807170462669)
              ·
                refine ⟨85459003719677688923501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227890676585807170462669 85459003719677688923501)
                ·
                  refine ⟨32047126394879133346313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85459003719677688923501 32047126394879133346313)
                  ·
                    rfl

theorem cell20_70213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_70213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70213 prefixEnd_70213 := by exact prefixLift 70213
  have htrace : WordTrace (prefixWord ++ tailWord_70213) baseStart_70213 baseEnd_70213 := by
    simpa [prefixWord, tailWord_70213, baseEnd_70213] using wordTrace_append hprefix tailTrace_70213
  have hstable : (prefixWord ++ tailWord_70213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70213).length < 2 ^ (prefixWord ++ tailWord_70213).sum := by decide
  have hdescent : baseEnd_70213 < baseStart_70213 := by decide
  rcases family_descends (prefixWord ++ tailWord_70213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70220 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_70220 : Nat := 118140960795 + 70220 * 2 ^ 59
def prefixEnd_70220 : Nat := 4983230072969 + 3 ^ 40 * 70220 * 2
def baseEnd_70220 : Nat := 32050321385618220112951

theorem tailTrace_70220 : CollatzResearch.WordTrace tailWord_70220 prefixEnd_70220 32050321385618220112951 := by
  unfold tailWord_70220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280566902806203733164057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1707422537074938310885409 1280566902806203733164057)
  ·
    refine ⟨960425177104652799873043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1280566902806203733164057 960425177104652799873043)
    ·
      refine ⟨1440637765656979199809565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960425177104652799873043 1440637765656979199809565)
      ·
        refine ⟨540239162121367199928587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1440637765656979199809565 540239162121367199928587)
        ·
          refine ⟨810358743182050799892881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540239162121367199928587 810358743182050799892881)
          ·
            refine ⟨607769057386538099919661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810358743182050799892881 607769057386538099919661)
            ·
              refine ⟨227913396519951787469873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607769057386538099919661 227913396519951787469873)
              ·
                refine ⟨170935047389963840602405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227913396519951787469873 170935047389963840602405)
                ·
                  refine ⟨32050321385618220112951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170935047389963840602405 32050321385618220112951)
                  ·
                    rfl

theorem cell20_70220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_70220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70220 prefixEnd_70220 := by exact prefixLift 70220
  have htrace : WordTrace (prefixWord ++ tailWord_70220) baseStart_70220 baseEnd_70220 := by
    simpa [prefixWord, tailWord_70220, baseEnd_70220] using wordTrace_append hprefix tailTrace_70220
  have hstable : (prefixWord ++ tailWord_70220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70220).length < 2 ^ (prefixWord ++ tailWord_70220).sum := by decide
  have hdescent : baseEnd_70220 < baseStart_70220 := by decide
  rcases family_descends (prefixWord ++ tailWord_70220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70254 : List Nat := [4, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_70254 : Nat := 118140960795 + 70254 * 2 ^ 59
def prefixEnd_70254 : Nat := 4983230072969 + 3 ^ 40 * 70254 * 2
def baseEnd_70254 : Nat := 32065839912065212979479

theorem tailTrace_70254 : CollatzResearch.WordTrace tailWord_70254 prefixEnd_70254 32065839912065212979479 := by
  unfold tailWord_70254
  simp only [CollatzResearch.WordTrace]
  refine ⟨320296735936153909133227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1708249258326154182043877 320296735936153909133227)
  ·
    refine ⟨480445103904230863699841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320296735936153909133227 480445103904230863699841)
    ·
      refine ⟨360333827928173147774881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 480445103904230863699841 360333827928173147774881)
      ·
        refine ⟨270250370946129860831161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360333827928173147774881 270250370946129860831161)
        ·
          refine ⟨202687778209597395623371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270250370946129860831161 202687778209597395623371)
          ·
            refine ⟨304031667314396093435057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202687778209597395623371 304031667314396093435057)
            ·
              refine ⟨228023750485797070076293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304031667314396093435057 228023750485797070076293)
              ·
                refine ⟨42754453216086950639305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228023750485797070076293 42754453216086950639305)
                ·
                  refine ⟨32065839912065212979479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42754453216086950639305 32065839912065212979479)
                  ·
                    rfl

theorem cell20_70254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_70254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70254 prefixEnd_70254 := by exact prefixLift 70254
  have htrace : WordTrace (prefixWord ++ tailWord_70254) baseStart_70254 baseEnd_70254 := by
    simpa [prefixWord, tailWord_70254, baseEnd_70254] using wordTrace_append hprefix tailTrace_70254
  have hstable : (prefixWord ++ tailWord_70254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70254).length < 2 ^ (prefixWord ++ tailWord_70254).sum := by decide
  have hdescent : baseEnd_70254 < baseStart_70254 := by decide
  rcases family_descends (prefixWord ++ tailWord_70254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70274 : List Nat := [3, 4, 3, 1, 1, 2, 2, 4]
def baseStart_70274 : Nat := 118140960795 + 70274 * 2 ^ 59
def prefixEnd_70274 : Nat := 4983230072969 + 3 ^ 40 * 70274 * 2
def baseEnd_70274 : Nat := 10691656152344677437577

theorem tailTrace_70274 : CollatzResearch.WordTrace tailWord_70274 prefixEnd_70274 10691656152344677437577 := by
  unfold tailWord_70274
  simp only [CollatzResearch.WordTrace]
  refine ⟨640775836854193672198469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1708735564944516459195917 640775836854193672198469)
  ·
    refine ⟨120145469410161313537213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 640775836854193672198469 120145469410161313537213)
    ·
      refine ⟨45054551028810492576455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120145469410161313537213 45054551028810492576455)
      ·
        refine ⟨67581826543215738864683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45054551028810492576455 67581826543215738864683)
        ·
          refine ⟨101372739814823608297025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67581826543215738864683 101372739814823608297025)
          ·
            refine ⟨76029554861117706222769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101372739814823608297025 76029554861117706222769)
            ·
              refine ⟨57022166145838279667077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76029554861117706222769 57022166145838279667077)
              ·
                refine ⟨10691656152344677437577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57022166145838279667077 10691656152344677437577)
                ·
                  rfl

theorem cell20_70274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_70274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70274 prefixEnd_70274 := by exact prefixLift 70274
  have htrace : WordTrace (prefixWord ++ tailWord_70274) baseStart_70274 baseEnd_70274 := by
    simpa [prefixWord, tailWord_70274, baseEnd_70274] using wordTrace_append hprefix tailTrace_70274
  have hstable : (prefixWord ++ tailWord_70274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70274).length < 2 ^ (prefixWord ++ tailWord_70274).sum := by decide
  have hdescent : baseEnd_70274 < baseStart_70274 := by decide
  rcases family_descends (prefixWord ++ tailWord_70274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70282 : List Nat := [3, 1, 2, 3, 3, 1, 1, 6]
def baseStart_70282 : Nat := 118140960795 + 70282 * 2 ^ 59
def prefixEnd_70282 : Nat := 4983230072969 + 3 ^ 40 * 70282 * 2
def baseEnd_70282 : Nat := 10692873291673853348677

theorem tailTrace_70282 : CollatzResearch.WordTrace tailWord_70282 prefixEnd_70282 10692873291673853348677 := by
  unfold tailWord_70282
  simp only [CollatzResearch.WordTrace]
  refine ⟨640848782846948013771275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1708930087591861370056733 640848782846948013771275)
  ·
    refine ⟨961273174270422020656913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640848782846948013771275 961273174270422020656913)
    ·
      refine ⟨720954880702816515492685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 961273174270422020656913 720954880702816515492685)
      ·
        refine ⟨270358080263556193309757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 720954880702816515492685 270358080263556193309757)
        ·
          refine ⟨101384280098833572491159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270358080263556193309757 101384280098833572491159)
          ·
            refine ⟨152076420148250358736739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101384280098833572491159 152076420148250358736739)
            ·
              refine ⟨228114630222375538105109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152076420148250358736739 228114630222375538105109)
              ·
                refine ⟨10692873291673853348677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228114630222375538105109 10692873291673853348677)
                ·
                  rfl

theorem cell20_70282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_70282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70282 prefixEnd_70282 := by exact prefixLift 70282
  have htrace : WordTrace (prefixWord ++ tailWord_70282) baseStart_70282 baseEnd_70282 := by
    simpa [prefixWord, tailWord_70282, baseEnd_70282] using wordTrace_append hprefix tailTrace_70282
  have hstable : (prefixWord ++ tailWord_70282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70282).length < 2 ^ (prefixWord ++ tailWord_70282).sum := by decide
  have hdescent : baseEnd_70282 < baseStart_70282 := by decide
  rcases family_descends (prefixWord ++ tailWord_70282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70334 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_70334 : Nat := 118140960795 + 70334 * 2 ^ 59
def prefixEnd_70334 : Nat := 4983230072969 + 3 ^ 40 * 70334 * 2
def baseEnd_70334 : Nat := 32102354091940490312485

theorem tailTrace_70334 : CollatzResearch.WordTrace tailWord_70334 prefixEnd_70334 32102354091940490312485 := by
  unfold tailWord_70334
  simp only [CollatzResearch.WordTrace]
  refine ⟨320661465899925616997257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1710194484799603290652037 320661465899925616997257)
  ·
    refine ⟨240496099424944212747943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 320661465899925616997257 240496099424944212747943)
    ·
      refine ⟨360744149137416319121915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240496099424944212747943 360744149137416319121915)
      ·
        refine ⟨541116223706124478682873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360744149137416319121915 541116223706124478682873)
        ·
          refine ⟨405837167779593359012155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541116223706124478682873 405837167779593359012155)
          ·
            refine ⟨608755751669390038518233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405837167779593359012155 608755751669390038518233)
            ·
              refine ⟨456566813752042528888675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608755751669390038518233 456566813752042528888675)
              ·
                refine ⟨684850220628063793333013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456566813752042528888675 684850220628063793333013)
                ·
                  refine ⟨32102354091940490312485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 684850220628063793333013 32102354091940490312485)
                  ·
                    rfl

theorem cell20_70334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_70334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70334 prefixEnd_70334 := by exact prefixLift 70334
  have htrace : WordTrace (prefixWord ++ tailWord_70334) baseStart_70334 baseEnd_70334 := by
    simpa [prefixWord, tailWord_70334, baseEnd_70334] using wordTrace_append hprefix tailTrace_70334
  have hstable : (prefixWord ++ tailWord_70334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70334).length < 2 ^ (prefixWord ++ tailWord_70334).sum := by decide
  have hdescent : baseEnd_70334 < baseStart_70334 := by decide
  rcases family_descends (prefixWord ++ tailWord_70334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70364 : List Nat := [2, 2, 5, 1, 1, 3, 2, 2, 2]
def baseStart_70364 : Nat := 118140960795 + 70364 * 2 ^ 59
def prefixEnd_70364 : Nat := 4983230072969 + 3 ^ 40 * 70364 * 2
def baseEnd_70364 : Nat := 32116046909393719312363

theorem tailTrace_70364 : CollatzResearch.WordTrace tailWord_70364 prefixEnd_70364 32116046909393719312363 := by
  unfold tailWord_70364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283192958545360029785073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1710923944727146706380097 1283192958545360029785073)
  ·
    refine ⟨962394718909020022338805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1283192958545360029785073 962394718909020022338805)
    ·
      refine ⟨90224504897720627094263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 962394718909020022338805 90224504897720627094263)
      ·
        refine ⟨135336757346580940641395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90224504897720627094263 135336757346580940641395)
        ·
          refine ⟨203005136019871410962093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135336757346580940641395 203005136019871410962093)
          ·
            refine ⟨76126926007451779110785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203005136019871410962093 76126926007451779110785)
            ·
              refine ⟨57095194505588834333089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76126926007451779110785 57095194505588834333089)
              ·
                refine ⟨42821395879191625749817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57095194505588834333089 42821395879191625749817)
                ·
                  refine ⟨32116046909393719312363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42821395879191625749817 32116046909393719312363)
                  ·
                    rfl

theorem cell20_70364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_70364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70364 prefixEnd_70364 := by exact prefixLift 70364
  have htrace : WordTrace (prefixWord ++ tailWord_70364) baseStart_70364 baseEnd_70364 := by
    simpa [prefixWord, tailWord_70364, baseEnd_70364] using wordTrace_append hprefix tailTrace_70364
  have hstable : (prefixWord ++ tailWord_70364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70364).length < 2 ^ (prefixWord ++ tailWord_70364).sum := by decide
  have hdescent : baseEnd_70364 < baseStart_70364 := by decide
  rcases family_descends (prefixWord ++ tailWord_70364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70396 : List Nat := [2, 2, 2, 1, 3, 3, 3, 4]
def baseStart_70396 : Nat := 118140960795 + 70396 * 2 ^ 59
def prefixEnd_70396 : Nat := 4983230072969 + 3 ^ 40 * 70396 * 2
def baseEnd_70396 : Nat := 10710217527114610081855

theorem tailTrace_70396 : CollatzResearch.WordTrace tailWord_70396 prefixEnd_70396 10710217527114610081855 := by
  unfold tailWord_70396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283776526487394762367521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1711702035316526349823361 1283776526487394762367521)
  ·
    refine ⟨962832394865546071775641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1283776526487394762367521 962832394865546071775641)
    ·
      refine ⟨722124296149159553831731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 962832394865546071775641 722124296149159553831731)
      ·
        refine ⟨1083186444223739330747597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722124296149159553831731 1083186444223739330747597)
        ·
          refine ⟨406194916583902249030349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1083186444223739330747597 406194916583902249030349)
          ·
            refine ⟨152323093718963343386381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 406194916583902249030349 152323093718963343386381)
            ·
              refine ⟨57121160144611253769893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152323093718963343386381 57121160144611253769893)
              ·
                refine ⟨10710217527114610081855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57121160144611253769893 10710217527114610081855)
                ·
                  rfl

theorem cell20_70396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_70396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70396 prefixEnd_70396 := by exact prefixLift 70396
  have htrace : WordTrace (prefixWord ++ tailWord_70396) baseStart_70396 baseEnd_70396 := by
    simpa [prefixWord, tailWord_70396, baseEnd_70396] using wordTrace_append hprefix tailTrace_70396
  have hstable : (prefixWord ++ tailWord_70396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70396).length < 2 ^ (prefixWord ++ tailWord_70396).sum := by decide
  have hdescent : baseEnd_70396 < baseStart_70396 := by decide
  rcases family_descends (prefixWord ++ tailWord_70396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70461 : List Nat := [1, 4, 1, 4, 2, 2, 1, 3, 2]
def baseStart_70461 : Nat := 118140960795 + 70461 * 2 ^ 59
def prefixEnd_70461 : Nat := 4983230072969 + 3 ^ 40 * 70461 * 2
def baseEnd_70461 : Nat := 32160320352492493078633

theorem tailTrace_70461 : CollatzResearch.WordTrace tailWord_70461 prefixEnd_70461 32160320352492493078633 := by
  unfold tailWord_70461
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569923797739305625851237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1713282531826203750567491 2569923797739305625851237)
  ·
    refine ⟨481860712076119804847107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2569923797739305625851237 481860712076119804847107)
    ·
      refine ⟨722791068114179707270661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481860712076119804847107 722791068114179707270661)
      ·
        refine ⟨135523325271408695113249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 722791068114179707270661 135523325271408695113249)
        ·
          refine ⟨101642493953556521334937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135523325271408695113249 101642493953556521334937)
          ·
            refine ⟨76231870465167391001203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101642493953556521334937 76231870465167391001203)
            ·
              refine ⟨114347805697751086501805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76231870465167391001203 114347805697751086501805)
              ·
                refine ⟨42880427136656657438177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114347805697751086501805 42880427136656657438177)
                ·
                  refine ⟨32160320352492493078633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42880427136656657438177 32160320352492493078633)
                  ·
                    rfl

theorem cell20_70461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_70461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70461 prefixEnd_70461 := by exact prefixLift 70461
  have htrace : WordTrace (prefixWord ++ tailWord_70461) baseStart_70461 baseEnd_70461 := by
    simpa [prefixWord, tailWord_70461, baseEnd_70461] using wordTrace_append hprefix tailTrace_70461
  have hstable : (prefixWord ++ tailWord_70461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70461).length < 2 ^ (prefixWord ++ tailWord_70461).sum := by decide
  have hdescent : baseEnd_70461 < baseStart_70461 := by decide
  rcases family_descends (prefixWord ++ tailWord_70461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70468 : List Nat := [2, 3, 4, 2, 2, 1, 6]
def baseStart_70468 : Nat := 118140960795 + 70468 * 2 ^ 59
def prefixEnd_70468 : Nat := 4983230072969 + 3 ^ 40 * 70468 * 2
def baseEnd_70468 : Nat := 3573723927025731093919

theorem tailTrace_70468 : CollatzResearch.WordTrace tailWord_70468 prefixEnd_70468 3573723927025731093919 := by
  unfold tailWord_70468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285089554356972910678029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1713452739142630547570705 1285089554356972910678029)
  ·
    refine ⟨481908582883864841504261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1285089554356972910678029 481908582883864841504261)
    ·
      refine ⟨90357859290724657782049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 481908582883864841504261 90357859290724657782049)
      ·
        refine ⟨67768394468043493336537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90357859290724657782049 67768394468043493336537)
        ·
          refine ⟨50826295851032620002403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67768394468043493336537 50826295851032620002403)
          ·
            refine ⟨76239443776548930003605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50826295851032620002403 76239443776548930003605)
            ·
              refine ⟨3573723927025731093919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76239443776548930003605 3573723927025731093919)
              ·
                rfl

theorem cell20_70468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 6].length) (baseStart_70468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70468 prefixEnd_70468 := by exact prefixLift 70468
  have htrace : WordTrace (prefixWord ++ tailWord_70468) baseStart_70468 baseEnd_70468 := by
    simpa [prefixWord, tailWord_70468, baseEnd_70468] using wordTrace_append hprefix tailTrace_70468
  have hstable : (prefixWord ++ tailWord_70468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70468).length < 2 ^ (prefixWord ++ tailWord_70468).sum := by decide
  have hdescent : baseEnd_70468 < baseStart_70468 := by decide
  rcases family_descends (prefixWord ++ tailWord_70468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70482 : List Nat := [3, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_70482 : Nat := 118140960795 + 70482 * 2 ^ 59
def prefixEnd_70482 : Nat := 4983230072969 + 3 ^ 40 * 70482 * 2
def baseEnd_70482 : Nat := 32169905324709753378547

theorem tailTrace_70482 : CollatzResearch.WordTrace tailWord_70482 prefixEnd_70482 32169905324709753378547 := by
  unfold tailWord_70482
  simp only [CollatzResearch.WordTrace]
  refine ⟨642672432665806553091425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1713793153775484141577133 642672432665806553091425)
  ·
    refine ⟨482004324499354914818569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 642672432665806553091425 482004324499354914818569)
    ·
      refine ⟨361503243374516186113927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 482004324499354914818569 361503243374516186113927)
      ·
        refine ⟨542254865061774279170891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361503243374516186113927 542254865061774279170891)
        ·
          refine ⟨813382297592661418756337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542254865061774279170891 813382297592661418756337)
          ·
            refine ⟨610036723194496064067253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 813382297592661418756337 610036723194496064067253)
            ·
              refine ⟨57190942799484006006305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 610036723194496064067253 57190942799484006006305)
              ·
                refine ⟨42893207099613004504729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57190942799484006006305 42893207099613004504729)
                ·
                  refine ⟨32169905324709753378547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42893207099613004504729 32169905324709753378547)
                  ·
                    rfl

theorem cell20_70482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_70482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70482 prefixEnd_70482 := by exact prefixLift 70482
  have htrace : WordTrace (prefixWord ++ tailWord_70482) baseStart_70482 baseEnd_70482 := by
    simpa [prefixWord, tailWord_70482, baseEnd_70482] using wordTrace_append hprefix tailTrace_70482
  have hstable : (prefixWord ++ tailWord_70482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70482).length < 2 ^ (prefixWord ++ tailWord_70482).sum := by decide
  have hdescent : baseEnd_70482 < baseStart_70482 := by decide
  rcases family_descends (prefixWord ++ tailWord_70482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70507 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_70507 : Nat := 118140960795 + 70507 * 2 ^ 59
def prefixEnd_70507 : Nat := 4983230072969 + 3 ^ 40 * 70507 * 2
def baseEnd_70507 : Nat := 32181316005920777545111

theorem tailTrace_70507 : CollatzResearch.WordTrace tailWord_70507 prefixEnd_70507 32181316005920777545111 := by
  unfold tailWord_70507
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571601555572655482025775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1714401037048436988017183 2571601555572655482025775)
  ·
    refine ⟨3857402333358983223038663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2571601555572655482025775 3857402333358983223038663)
    ·
      refine ⟨5786103500038474834557995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3857402333358983223038663 5786103500038474834557995)
      ·
        refine ⟨8679155250057712251836993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5786103500038474834557995 8679155250057712251836993)
        ·
          refine ⟨6509366437543284188877745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8679155250057712251836993 6509366437543284188877745)
          ·
            refine ⟨4882024828157463141658309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509366437543284188877745 4882024828157463141658309)
            ·
              refine ⟨915379655279524339060933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4882024828157463141658309 915379655279524339060933)
              ·
                refine ⟨171633685364910813573925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 915379655279524339060933 171633685364910813573925)
                ·
                  refine ⟨32181316005920777545111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171633685364910813573925 32181316005920777545111)
                  ·
                    rfl

theorem cell20_70507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_70507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70507 prefixEnd_70507 := by exact prefixLift 70507
  have htrace : WordTrace (prefixWord ++ tailWord_70507) baseStart_70507 baseEnd_70507 := by
    simpa [prefixWord, tailWord_70507, baseEnd_70507] using wordTrace_append hprefix tailTrace_70507
  have hstable : (prefixWord ++ tailWord_70507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70507).length < 2 ^ (prefixWord ++ tailWord_70507).sum := by decide
  have hdescent : baseEnd_70507 < baseStart_70507 := by decide
  rcases family_descends (prefixWord ++ tailWord_70507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70530 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_70530 : Nat := 118140960795 + 70530 * 2 ^ 59
def prefixEnd_70530 : Nat := 4983230072969 + 3 ^ 40 * 70530 * 2
def baseEnd_70530 : Nat := 32191813832634919778351

theorem tailTrace_70530 : CollatzResearch.WordTrace tailWord_70530 prefixEnd_70530 32191813832634919778351 := by
  unfold tailWord_70530
  simp only [CollatzResearch.WordTrace]
  refine ⟨643110108622332602528261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1714960289659553606742029 643110108622332602528261)
  ·
    refine ⟨120583145366687362974049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 643110108622332602528261 120583145366687362974049)
    ·
      refine ⟨90437359025015522230537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120583145366687362974049 90437359025015522230537)
      ·
        refine ⟨67828019268761641672903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90437359025015522230537 67828019268761641672903)
        ·
          refine ⟨101742028903142462509355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67828019268761641672903 101742028903142462509355)
          ·
            refine ⟨152613043354713693764033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101742028903142462509355 152613043354713693764033)
            ·
              refine ⟨114459782516035270323025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152613043354713693764033 114459782516035270323025)
              ·
                refine ⟨85844836887026452742269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114459782516035270323025 85844836887026452742269)
                ·
                  refine ⟨32191813832634919778351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85844836887026452742269 32191813832634919778351)
                  ·
                    rfl

theorem cell20_70530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_70530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70530 prefixEnd_70530 := by exact prefixLift 70530
  have htrace : WordTrace (prefixWord ++ tailWord_70530) baseStart_70530 baseEnd_70530 := by
    simpa [prefixWord, tailWord_70530, baseEnd_70530] using wordTrace_append hprefix tailTrace_70530
  have hstable : (prefixWord ++ tailWord_70530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70530).length < 2 ^ (prefixWord ++ tailWord_70530).sum := by decide
  have hdescent : baseEnd_70530 < baseStart_70530 := by decide
  rcases family_descends (prefixWord ++ tailWord_70530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70545 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_70545 : Nat := 118140960795 + 70545 * 2 ^ 59
def prefixEnd_70545 : Nat := 4983230072969 + 3 ^ 40 * 70545 * 2
def baseEnd_70545 : Nat := 32198660241361534278289

theorem tailTrace_70545 : CollatzResearch.WordTrace tailWord_70545 prefixEnd_70545 32198660241361534278289 := by
  unfold tailWord_70545
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572987529434987971909089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1715325019623325314606059 2572987529434987971909089)
  ·
    refine ⟨1929740647076240978931817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2572987529434987971909089 1929740647076240978931817)
    ·
      refine ⟨1447305485307180734198863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1929740647076240978931817 1447305485307180734198863)
      ·
        refine ⟨2170958227960771101298295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447305485307180734198863 2170958227960771101298295)
        ·
          refine ⟨3256437341941156651947443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2170958227960771101298295 3256437341941156651947443)
          ·
            refine ⟨4884656012911734977921165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256437341941156651947443 4884656012911734977921165)
            ·
              refine ⟨1831746004841900616720437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4884656012911734977921165 1831746004841900616720437)
              ·
                refine ⟨171726187953928182817541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1831746004841900616720437 171726187953928182817541)
                ·
                  refine ⟨32198660241361534278289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171726187953928182817541 32198660241361534278289)
                  ·
                    rfl

theorem cell20_70545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_70545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70545 prefixEnd_70545 := by exact prefixLift 70545
  have htrace : WordTrace (prefixWord ++ tailWord_70545) baseStart_70545 baseEnd_70545 := by
    simpa [prefixWord, tailWord_70545, baseEnd_70545] using wordTrace_append hprefix tailTrace_70545
  have hstable : (prefixWord ++ tailWord_70545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70545).length < 2 ^ (prefixWord ++ tailWord_70545).sum := by decide
  have hdescent : baseEnd_70545 < baseStart_70545 := by decide
  rcases family_descends (prefixWord ++ tailWord_70545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70562 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_70562 : Nat := 118140960795 + 70562 * 2 ^ 59
def prefixEnd_70562 : Nat := 4983230072969 + 3 ^ 40 * 70562 * 2
def baseEnd_70562 : Nat := 32206419504585030711553

theorem tailTrace_70562 : CollatzResearch.WordTrace tailWord_70562 prefixEnd_70562 32206419504585030711553 := by
  unfold tailWord_70562
  simp only [CollatzResearch.WordTrace]
  refine ⟨643401892593349968819485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1715738380248933250185293 643401892593349968819485)
  ·
    refine ⟨241275709722506238307307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 643401892593349968819485 241275709722506238307307)
    ·
      refine ⟨361913564583759357460961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241275709722506238307307 361913564583759357460961)
      ·
        refine ⟨271435173437819518095721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361913564583759357460961 271435173437819518095721)
        ·
          refine ⟨203576380078364638571791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271435173437819518095721 203576380078364638571791)
          ·
            refine ⟨305364570117546957857687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203576380078364638571791 305364570117546957857687)
            ·
              refine ⟨458046855176320436786531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305364570117546957857687 458046855176320436786531)
              ·
                refine ⟨687070282764480655179797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458046855176320436786531 687070282764480655179797)
                ·
                  refine ⟨32206419504585030711553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 687070282764480655179797 32206419504585030711553)
                  ·
                    rfl

theorem cell20_70562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_70562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70562 prefixEnd_70562 := by exact prefixLift 70562
  have htrace : WordTrace (prefixWord ++ tailWord_70562) baseStart_70562 baseEnd_70562 := by
    simpa [prefixWord, tailWord_70562, baseEnd_70562] using wordTrace_append hprefix tailTrace_70562
  have hstable : (prefixWord ++ tailWord_70562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70562).length < 2 ^ (prefixWord ++ tailWord_70562).sum := by decide
  have hdescent : baseEnd_70562 < baseStart_70562 := by decide
  rcases family_descends (prefixWord ++ tailWord_70562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70569 : List Nat := [1, 2, 1, 1, 1, 1, 9, 4]
def baseStart_70569 : Nat := 118140960795 + 70569 * 2 ^ 59
def prefixEnd_70569 : Nat := 4983230072969 + 3 ^ 40 * 70569 * 2
def baseEnd_70569 : Nat := 10736538165108039159397

theorem tailTrace_70569 : CollatzResearch.WordTrace tailWord_70569 prefixEnd_70569 10736538165108039159397 := by
  unfold tailWord_70569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2573862881348040070782761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1715908587565360047188507 2573862881348040070782761)
  ·
    refine ⟨1930397161011030053087071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2573862881348040070782761 1930397161011030053087071)
    ·
      refine ⟨2895595741516545079630607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1930397161011030053087071 2895595741516545079630607)
      ·
        refine ⟨4343393612274817619445911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895595741516545079630607 4343393612274817619445911)
        ·
          refine ⟨6515090418412226429168867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343393612274817619445911 6515090418412226429168867)
          ·
            refine ⟨9772635627618339643753301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515090418412226429168867 9772635627618339643753301)
            ·
              refine ⟨57261536880576208850117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9772635627618339643753301 57261536880576208850117)
              ·
                refine ⟨10736538165108039159397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57261536880576208850117 10736538165108039159397)
                ·
                  rfl

theorem cell20_70569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_70569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70569 prefixEnd_70569 := by exact prefixLift 70569
  have htrace : WordTrace (prefixWord ++ tailWord_70569) baseStart_70569 baseEnd_70569 := by
    simpa [prefixWord, tailWord_70569, baseEnd_70569] using wordTrace_append hprefix tailTrace_70569
  have hstable : (prefixWord ++ tailWord_70569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70569).length < 2 ^ (prefixWord ++ tailWord_70569).sum := by decide
  have hdescent : baseEnd_70569 < baseStart_70569 := by decide
  rcases family_descends (prefixWord ++ tailWord_70569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70582 : List Nat := [5, 1, 4, 1, 1, 1, 7]
def baseStart_70582 : Nat := 118140960795 + 70582 * 2 ^ 59
def prefixEnd_70582 : Nat := 4983230072969 + 3 ^ 40 * 70582 * 2
def baseEnd_70582 : Nat := 3579505338839316671645

theorem tailTrace_70582 : CollatzResearch.WordTrace tailWord_70582 prefixEnd_70582 3579505338839316671645 := by
  unfold tailWord_70582
  simp only [CollatzResearch.WordTrace]
  refine ⟨160896064393808955687875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1716224686867295527337333 160896064393808955687875)
  ·
    refine ⟨241344096590713433531813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160896064393808955687875 241344096590713433531813)
    ·
      refine ⟨45252018110758768787215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241344096590713433531813 45252018110758768787215)
      ·
        refine ⟨67878027166138153180823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45252018110758768787215 67878027166138153180823)
        ·
          refine ⟨101817040749207229771235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67878027166138153180823 101817040749207229771235)
          ·
            refine ⟨152725561123810844656853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101817040749207229771235 152725561123810844656853)
            ·
              refine ⟨3579505338839316671645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 152725561123810844656853 3579505338839316671645)
              ·
                rfl

theorem cell20_70582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 7].length) (baseStart_70582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70582 prefixEnd_70582 := by exact prefixLift 70582
  have htrace : WordTrace (prefixWord ++ tailWord_70582) baseStart_70582 baseEnd_70582 := by
    simpa [prefixWord, tailWord_70582, baseEnd_70582] using wordTrace_append hprefix tailTrace_70582
  have hstable : (prefixWord ++ tailWord_70582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70582).length < 2 ^ (prefixWord ++ tailWord_70582).sum := by decide
  have hdescent : baseEnd_70582 < baseStart_70582 := by decide
  rcases family_descends (prefixWord ++ tailWord_70582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70589 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 3]
def baseStart_70589 : Nat := 118140960795 + 70589 * 2 ^ 59
def prefixEnd_70589 : Nat := 4983230072969 + 3 ^ 40 * 70589 * 2
def baseEnd_70589 : Nat := 32218743040292936811443

theorem tailTrace_70589 : CollatzResearch.WordTrace tailWord_70589 prefixEnd_70589 32218743040292936811443 := by
  unfold tailWord_70589
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574592341275583486510821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1716394894183722324340547 2574592341275583486510821)
  ·
    refine ⟨482736063989171903720779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2574592341275583486510821 482736063989171903720779)
    ·
      refine ⟨724104095983757855581169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482736063989171903720779 724104095983757855581169)
      ·
        refine ⟨543078071987818391685877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 724104095983757855581169 543078071987818391685877)
        ·
          refine ⟨50913569248857974220551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 543078071987818391685877 50913569248857974220551)
          ·
            refine ⟨76370353873286961330827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50913569248857974220551 76370353873286961330827)
            ·
              refine ⟨114555530809930441996241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76370353873286961330827 114555530809930441996241)
              ·
                refine ⟨85916648107447831497181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114555530809930441996241 85916648107447831497181)
                ·
                  refine ⟨32218743040292936811443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85916648107447831497181 32218743040292936811443)
                  ·
                    rfl

theorem cell20_70589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_70589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70589 prefixEnd_70589 := by exact prefixLift 70589
  have htrace : WordTrace (prefixWord ++ tailWord_70589) baseStart_70589 baseEnd_70589 := by
    simpa [prefixWord, tailWord_70589, baseEnd_70589] using wordTrace_append hprefix tailTrace_70589
  have hstable : (prefixWord ++ tailWord_70589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70589).length < 2 ^ (prefixWord ++ tailWord_70589).sum := by decide
  have hdescent : baseEnd_70589 < baseStart_70589 := by decide
  rcases family_descends (prefixWord ++ tailWord_70589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70596 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_70596 : Nat := 118140960795 + 70596 * 2 ^ 59
def prefixEnd_70596 : Nat := 4983230072969 + 3 ^ 40 * 70596 * 2
def baseEnd_70596 : Nat := 32221938031032023578081

theorem tailTrace_70596 : CollatzResearch.WordTrace tailWord_70596 prefixEnd_70596 32221938031032023578081 := by
  unfold tailWord_70596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1287423826125111841007821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1716565101500149121343761 1287423826125111841007821)
  ·
    refine ⟨482783934796916940377933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1287423826125111841007821 482783934796916940377933)
    ·
      refine ⟨181043975548843852641725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 482783934796916940377933 181043975548843852641725)
      ·
        refine ⟨67891490830816444740647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181043975548843852641725 67891490830816444740647)
        ·
          refine ⟨101837236246224667110971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67891490830816444740647 101837236246224667110971)
          ·
            refine ⟨152755854369337000666457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101837236246224667110971 152755854369337000666457)
            ·
              refine ⟨114566890777002750499843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152755854369337000666457 114566890777002750499843)
              ·
                refine ⟨171850336165504125749765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114566890777002750499843 171850336165504125749765)
                ·
                  refine ⟨32221938031032023578081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171850336165504125749765 32221938031032023578081)
                  ·
                    rfl

theorem cell20_70596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_70596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70596 prefixEnd_70596 := by exact prefixLift 70596
  have htrace : WordTrace (prefixWord ++ tailWord_70596) baseStart_70596 baseEnd_70596 := by
    simpa [prefixWord, tailWord_70596, baseEnd_70596] using wordTrace_append hprefix tailTrace_70596
  have hstable : (prefixWord ++ tailWord_70596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70596).length < 2 ^ (prefixWord ++ tailWord_70596).sum := by decide
  have hdescent : baseEnd_70596 < baseStart_70596 := by decide
  rcases family_descends (prefixWord ++ tailWord_70596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70634 : List Nat := [3, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_70634 : Nat := 118140960795 + 70634 * 2 ^ 59
def prefixEnd_70634 : Nat := 4983230072969 + 3 ^ 40 * 70634 * 2
def baseEnd_70634 : Nat := 32239282266472780311259

theorem tailTrace_70634 : CollatzResearch.WordTrace tailWord_70634 prefixEnd_70634 32239282266472780311259 := by
  unfold tailWord_70634
  simp only [CollatzResearch.WordTrace]
  refine ⟨644058406528139042974739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1717489084075037447932637 644058406528139042974739)
  ·
    refine ⟨966087609792208564462109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 644058406528139042974739 966087609792208564462109)
    ·
      refine ⟨362282853672078211673291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 966087609792208564462109 362282853672078211673291)
      ·
        refine ⟨543424280508117317509937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362282853672078211673291 543424280508117317509937)
        ·
          refine ⟨407568210381087988132453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543424280508117317509937 407568210381087988132453)
          ·
            refine ⟨76419039446453997774835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 407568210381087988132453 76419039446453997774835)
            ·
              refine ⟨114628559169680996662253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76419039446453997774835 114628559169680996662253)
              ·
                refine ⟨42985709688630373748345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114628559169680996662253 42985709688630373748345)
                ·
                  refine ⟨32239282266472780311259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42985709688630373748345 32239282266472780311259)
                  ·
                    rfl

theorem cell20_70634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_70634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70634 prefixEnd_70634 := by exact prefixLift 70634
  have htrace : WordTrace (prefixWord ++ tailWord_70634) baseStart_70634 baseEnd_70634 := by
    simpa [prefixWord, tailWord_70634, baseEnd_70634] using wordTrace_append hprefix tailTrace_70634
  have hstable : (prefixWord ++ tailWord_70634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70634).length < 2 ^ (prefixWord ++ tailWord_70634).sum := by decide
  have hdescent : baseEnd_70634 < baseStart_70634 := by decide
  rcases family_descends (prefixWord ++ tailWord_70634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70652 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_70652 : Nat := 118140960795 + 70652 * 2 ^ 59
def prefixEnd_70652 : Nat := 4983230072969 + 3 ^ 40 * 70652 * 2
def baseEnd_70652 : Nat := 32247497956944717711185

theorem tailTrace_70652 : CollatzResearch.WordTrace tailWord_70652 prefixEnd_70652 32247497956944717711185 := by
  unfold tailWord_70652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288445070023672623027105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1717926760031563497369473 1288445070023672623027105)
  ·
    refine ⟨966333802517754467270329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1288445070023672623027105 966333802517754467270329)
    ·
      refine ⟨724750351888315850452747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 966333802517754467270329 724750351888315850452747)
      ·
        refine ⟨1087125527832473775679121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724750351888315850452747 1087125527832473775679121)
        ·
          refine ⟨815344145874355331759341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087125527832473775679121 815344145874355331759341)
          ·
            refine ⟨305754054702883249409753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 815344145874355331759341 305754054702883249409753)
            ·
              refine ⟨229315541027162437057315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305754054702883249409753 229315541027162437057315)
              ·
                refine ⟨343973311540743655585973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229315541027162437057315 343973311540743655585973)
                ·
                  refine ⟨32247497956944717711185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 343973311540743655585973 32247497956944717711185)
                  ·
                    rfl

theorem cell20_70652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_70652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70652 prefixEnd_70652 := by exact prefixLift 70652
  have htrace : WordTrace (prefixWord ++ tailWord_70652) baseStart_70652 baseEnd_70652 := by
    simpa [prefixWord, tailWord_70652, baseEnd_70652] using wordTrace_append hprefix tailTrace_70652
  have hstable : (prefixWord ++ tailWord_70652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70652).length < 2 ^ (prefixWord ++ tailWord_70652).sum := by decide
  have hdescent : baseEnd_70652 < baseStart_70652 := by decide
  rcases family_descends (prefixWord ++ tailWord_70652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70710 : List Nat := [5, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_70710 : Nat := 118140960795 + 70710 * 2 ^ 59
def prefixEnd_70710 : Nat := 4983230072969 + 3 ^ 40 * 70710 * 2
def baseEnd_70710 : Nat := 32273970737354293777615

theorem tailTrace_70710 : CollatzResearch.WordTrace tailWord_70710 prefixEnd_70710 32273970737354293777615 := by
  unfold tailWord_70710
  simp only [CollatzResearch.WordTrace]
  refine ⟨161187848364826321979099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1719337049224814101110389 161187848364826321979099)
  ·
    refine ⟨241781772547239482968649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161187848364826321979099 241781772547239482968649)
    ·
      refine ⟨181336329410429612226487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241781772547239482968649 181336329410429612226487)
      ·
        refine ⟨272004494115644418339731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181336329410429612226487 272004494115644418339731)
        ·
          refine ⟨408006741173466627509597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272004494115644418339731 408006741173466627509597)
          ·
            refine ⟨153002527940049985316099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408006741173466627509597 153002527940049985316099)
            ·
              refine ⟨229503791910074977974149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153002527940049985316099 229503791910074977974149)
              ·
                refine ⟨43031960983139058370153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229503791910074977974149 43031960983139058370153)
                ·
                  refine ⟨32273970737354293777615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43031960983139058370153 32273970737354293777615)
                  ·
                    rfl

theorem cell20_70710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_70710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70710 prefixEnd_70710 := by exact prefixLift 70710
  have htrace : WordTrace (prefixWord ++ tailWord_70710) baseStart_70710 baseEnd_70710 := by
    simpa [prefixWord, tailWord_70710, baseEnd_70710] using wordTrace_append hprefix tailTrace_70710
  have hstable : (prefixWord ++ tailWord_70710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70710).length < 2 ^ (prefixWord ++ tailWord_70710).sum := by decide
  have hdescent : baseEnd_70710 < baseStart_70710 := by decide
  rcases family_descends (prefixWord ++ tailWord_70710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70728 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_70728 : Nat := 118140960795 + 70728 * 2 ^ 59
def prefixEnd_70728 : Nat := 4983230072969 + 3 ^ 40 * 70728 * 2
def baseEnd_70728 : Nat := 32282186427826231177541

theorem tailTrace_70728 : CollatzResearch.WordTrace tailWord_70728 prefixEnd_70728 32282186427826231177541 := by
  unfold tailWord_70728
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289831043886005112910419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1719774725181340150547225 1289831043886005112910419)
  ·
    refine ⟨1934746565829007669365629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289831043886005112910419 1934746565829007669365629)
    ·
      refine ⟨725529962185877876012111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1934746565829007669365629 725529962185877876012111)
      ·
        refine ⟨1088294943278816814018167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725529962185877876012111 1088294943278816814018167)
        ·
          refine ⟨1632442414918225221027251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088294943278816814018167 1632442414918225221027251)
          ·
            refine ⟨2448663622377337831540877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632442414918225221027251 2448663622377337831540877)
            ·
              refine ⟨918248858391501686827829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2448663622377337831540877 918248858391501686827829)
              ·
                refine ⟨86085830474203283140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 918248858391501686827829 86085830474203283140109)
                ·
                  refine ⟨32282186427826231177541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86085830474203283140109 32282186427826231177541)
                  ·
                    rfl

theorem cell20_70728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_70728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70728 prefixEnd_70728 := by exact prefixLift 70728
  have htrace : WordTrace (prefixWord ++ tailWord_70728) baseStart_70728 baseEnd_70728 := by
    simpa [prefixWord, tailWord_70728, baseEnd_70728] using wordTrace_append hprefix tailTrace_70728
  have hstable : (prefixWord ++ tailWord_70728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70728).length < 2 ^ (prefixWord ++ tailWord_70728).sum := by decide
  have hdescent : baseEnd_70728 < baseStart_70728 := by decide
  rcases family_descends (prefixWord ++ tailWord_70728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70738 : List Nat := [3, 2, 2, 1, 3, 2, 3, 4]
def baseStart_70738 : Nat := 118140960795 + 70738 * 2 ^ 59
def prefixEnd_70738 : Nat := 4983230072969 + 3 ^ 40 * 70738 * 2
def baseEnd_70738 : Nat := 10762250233436880281389

theorem tailTrace_70738 : CollatzResearch.WordTrace tailWord_70738 prefixEnd_70738 10762250233436880281389 := by
  unfold tailWord_70738
  simp only [CollatzResearch.WordTrace]
  refine ⟨645006704433945483421217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1720017878490521289123245 645006704433945483421217)
  ·
    refine ⟨483755028325459112565913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 645006704433945483421217 483755028325459112565913)
    ·
      refine ⟨362816271244094334424435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 483755028325459112565913 362816271244094334424435)
      ·
        refine ⟨544224406866141501636653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362816271244094334424435 544224406866141501636653)
        ·
          refine ⟨204084152574803063113745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 544224406866141501636653 204084152574803063113745)
          ·
            refine ⟨153063114431102297335309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204084152574803063113745 153063114431102297335309)
            ·
              refine ⟨57398667911663361500741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153063114431102297335309 57398667911663361500741)
              ·
                refine ⟨10762250233436880281389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57398667911663361500741 10762250233436880281389)
                ·
                  rfl

theorem cell20_70738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_70738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70738 prefixEnd_70738 := by exact prefixLift 70738
  have htrace : WordTrace (prefixWord ++ tailWord_70738) baseStart_70738 baseEnd_70738 := by
    simpa [prefixWord, tailWord_70738, baseEnd_70738] using wordTrace_append hprefix tailTrace_70738
  have hstable : (prefixWord ++ tailWord_70738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70738).length < 2 ^ (prefixWord ++ tailWord_70738).sum := by decide
  have hdescent : baseEnd_70738 < baseStart_70738 := by decide
  rcases family_descends (prefixWord ++ tailWord_70738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70762 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_70762 : Nat := 118140960795 + 70762 * 2 ^ 59
def prefixEnd_70762 : Nat := 4983230072969 + 3 ^ 40 * 70762 * 2
def baseEnd_70762 : Nat := 32297704954273224044069

theorem tailTrace_70762 : CollatzResearch.WordTrace tailWord_70762 prefixEnd_70762 32297704954273224044069 := by
  unfold tailWord_70762
  simp only [CollatzResearch.WordTrace]
  refine ⟨645225542412208508139635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1720601446432556021705693 645225542412208508139635)
  ·
    refine ⟨967838313618312762209453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 645225542412208508139635 967838313618312762209453)
    ·
      refine ⟨362939367606867285828545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 967838313618312762209453 362939367606867285828545)
      ·
        refine ⟨272204525705150464371409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362939367606867285828545 272204525705150464371409)
        ·
          refine ⟨204153394278862848278557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272204525705150464371409 204153394278862848278557)
          ·
            refine ⟨76557522854573568104459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204153394278862848278557 76557522854573568104459)
            ·
              refine ⟨114836284281860352156689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76557522854573568104459 114836284281860352156689)
              ·
                refine ⟨86127213211395264117517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114836284281860352156689 86127213211395264117517)
                ·
                  refine ⟨32297704954273224044069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86127213211395264117517 32297704954273224044069)
                  ·
                    rfl

theorem cell20_70762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_70762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70762 prefixEnd_70762 := by exact prefixLift 70762
  have htrace : WordTrace (prefixWord ++ tailWord_70762) baseStart_70762 baseEnd_70762 := by
    simpa [prefixWord, tailWord_70762, baseEnd_70762] using wordTrace_append hprefix tailTrace_70762
  have hstable : (prefixWord ++ tailWord_70762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70762).length < 2 ^ (prefixWord ++ tailWord_70762).sum := by decide
  have hdescent : baseEnd_70762 < baseStart_70762 := by decide
  rcases family_descends (prefixWord ++ tailWord_70762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70780 : List Nat := [2, 2, 2, 1, 1, 3, 2, 7]
def baseStart_70780 : Nat := 118140960795 + 70780 * 2 ^ 59
def prefixEnd_70780 : Nat := 4983230072969 + 3 ^ 40 * 70780 * 2
def baseEnd_70780 : Nat := 10768640214915053814665

theorem tailTrace_70780 : CollatzResearch.WordTrace tailWord_70780 prefixEnd_70780 10768640214915053814665 := by
  unfold tailWord_70780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290779341791811553356897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1721039122389082071142529 1290779341791811553356897)
  ·
    refine ⟨968084506343858665017673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1290779341791811553356897 968084506343858665017673)
    ·
      refine ⟨726063379757893998763255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 968084506343858665017673 726063379757893998763255)
      ·
        refine ⟨1089095069636840998144883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726063379757893998763255 1089095069636840998144883)
        ·
          refine ⟨1633642604455261497217325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089095069636840998144883 1633642604455261497217325)
          ·
            refine ⟨612615976670723061456497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1633642604455261497217325 612615976670723061456497)
            ·
              refine ⟨459461982503042296092373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612615976670723061456497 459461982503042296092373)
              ·
                refine ⟨10768640214915053814665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 459461982503042296092373 10768640214915053814665)
                ·
                  rfl

theorem cell20_70780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_70780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70780 prefixEnd_70780 := by exact prefixLift 70780
  have htrace : WordTrace (prefixWord ++ tailWord_70780) baseStart_70780 baseEnd_70780 := by
    simpa [prefixWord, tailWord_70780, baseEnd_70780] using wordTrace_append hprefix tailTrace_70780
  have hstable : (prefixWord ++ tailWord_70780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70780).length < 2 ^ (prefixWord ++ tailWord_70780).sum := by decide
  have hdescent : baseEnd_70780 < baseStart_70780 := by decide
  rcases family_descends (prefixWord ++ tailWord_70780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70807 : List Nat := [1, 1, 3, 3, 3, 1, 3, 3, 2]
def baseStart_70807 : Nat := 118140960795 + 70807 * 2 ^ 59
def prefixEnd_70807 : Nat := 4983230072969 + 3 ^ 40 * 70807 * 2
def baseEnd_70807 : Nat := 32318244180453067543885

theorem tailTrace_70807 : CollatzResearch.WordTrace tailWord_70807 prefixEnd_70807 32318244180453067543885 := by
  unfold tailWord_70807
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582543454485806717946675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1721695636323871145297783 2582543454485806717946675)
  ·
    refine ⟨3873815181728710076920013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2582543454485806717946675 3873815181728710076920013)
    ·
      refine ⟨1452680693148266278845005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3873815181728710076920013 1452680693148266278845005)
      ·
        refine ⟨544755259930599854566877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1452680693148266278845005 544755259930599854566877)
        ·
          refine ⟨204283222473974945462579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 544755259930599854566877 204283222473974945462579)
          ·
            refine ⟨306424833710962418193869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204283222473974945462579 306424833710962418193869)
            ·
              refine ⟨114909312641610906822701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306424833710962418193869 114909312641610906822701)
              ·
                refine ⟨43090992240604090058513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114909312641610906822701 43090992240604090058513)
                ·
                  refine ⟨32318244180453067543885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43090992240604090058513 32318244180453067543885)
                  ·
                    rfl

theorem cell20_70807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 2].length) (baseStart_70807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70807 prefixEnd_70807 := by exact prefixLift 70807
  have htrace : WordTrace (prefixWord ++ tailWord_70807) baseStart_70807 baseEnd_70807 := by
    simpa [prefixWord, tailWord_70807, baseEnd_70807] using wordTrace_append hprefix tailTrace_70807
  have hstable : (prefixWord ++ tailWord_70807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70807).length < 2 ^ (prefixWord ++ tailWord_70807).sum := by decide
  have hdescent : baseEnd_70807 < baseStart_70807 := by decide
  rcases family_descends (prefixWord ++ tailWord_70807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70814 : List Nat := [4, 3, 1, 1, 2, 3, 6]
def baseStart_70814 : Nat := 118140960795 + 70814 * 2 ^ 59
def prefixEnd_70814 : Nat := 4983230072969 + 3 ^ 40 * 70814 * 2
def baseEnd_70814 : Nat := 3591271019021350478947

theorem tailTrace_70814 : CollatzResearch.WordTrace tailWord_70814 prefixEnd_70814 3591271019021350478947 := by
  unfold tailWord_70814
  simp only [CollatzResearch.WordTrace]
  refine ⟨322849845682555864181437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1721865843640297942300997 322849845682555864181437)
  ·
    refine ⟨121068692130958449068039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 322849845682555864181437 121068692130958449068039)
    ·
      refine ⟨181603038196437673602059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121068692130958449068039 181603038196437673602059)
      ·
        refine ⟨272404557294656510403089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181603038196437673602059 272404557294656510403089)
        ·
          refine ⟨204303417970992382802317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272404557294656510403089 204303417970992382802317)
          ·
            refine ⟨76613781739122143550869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204303417970992382802317 76613781739122143550869)
            ·
              refine ⟨3591271019021350478947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76613781739122143550869 3591271019021350478947)
              ·
                rfl

theorem cell20_70814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 6].length) (baseStart_70814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70814 prefixEnd_70814 := by exact prefixLift 70814
  have htrace : WordTrace (prefixWord ++ tailWord_70814) baseStart_70814 baseEnd_70814 := by
    simpa [prefixWord, tailWord_70814, baseEnd_70814] using wordTrace_append hprefix tailTrace_70814
  have hstable : (prefixWord ++ tailWord_70814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70814).length < 2 ^ (prefixWord ++ tailWord_70814).sum := by decide
  have hdescent : baseEnd_70814 < baseStart_70814 := by decide
  rcases family_descends (prefixWord ++ tailWord_70814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70856 : List Nat := [2, 1, 3, 1, 2, 1, 4, 6]
def baseStart_70856 : Nat := 118140960795 + 70856 * 2 ^ 59
def prefixEnd_70856 : Nat := 4983230072969 + 3 ^ 40 * 70856 * 2
def baseEnd_70856 : Nat := 10780203038542224970117

theorem tailTrace_70856 : CollatzResearch.WordTrace tailWord_70856 prefixEnd_70856 10780203038542224970117 := by
  unfold tailWord_70856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292165315654144043240211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1722887087538858724320281 1292165315654144043240211)
  ·
    refine ⟨1938247973481216064860317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1292165315654144043240211 1938247973481216064860317)
    ·
      refine ⟨726842990055456024322619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1938247973481216064860317 726842990055456024322619)
      ·
        refine ⟨1090264485083184036483929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726842990055456024322619 1090264485083184036483929)
        ·
          refine ⟨817698363812388027362947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1090264485083184036483929 817698363812388027362947)
          ·
            refine ⟨1226547545718582041044421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817698363812388027362947 1226547545718582041044421)
            ·
              refine ⟨229977664822234132695829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1226547545718582041044421 229977664822234132695829)
              ·
                refine ⟨10780203038542224970117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229977664822234132695829 10780203038542224970117)
                ·
                  rfl

theorem cell20_70856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_70856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70856 prefixEnd_70856 := by exact prefixLift 70856
  have htrace : WordTrace (prefixWord ++ tailWord_70856) baseStart_70856 baseEnd_70856 := by
    simpa [prefixWord, tailWord_70856, baseEnd_70856] using wordTrace_append hprefix tailTrace_70856
  have hstable : (prefixWord ++ tailWord_70856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70856).length < 2 ^ (prefixWord ++ tailWord_70856).sum := by decide
  have hdescent : baseEnd_70856 < baseStart_70856 := by decide
  rcases family_descends (prefixWord ++ tailWord_70856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70863 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_70863 : Nat := 118140960795 + 70863 * 2 ^ 59
def prefixEnd_70863 : Nat := 4983230072969 + 3 ^ 40 * 70863 * 2
def baseEnd_70863 : Nat := 32343804106365761676989

theorem tailTrace_70863 : CollatzResearch.WordTrace tailWord_70863 prefixEnd_70863 32343804106365761676989 := by
  unfold tailWord_70863
  simp only [CollatzResearch.WordTrace]
  refine ⟨2584585942282928281985243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1723057294855285521323495 2584585942282928281985243)
  ·
    refine ⟨3876878913424392422977865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2584585942282928281985243 3876878913424392422977865)
    ·
      refine ⟨2907659185068294317233399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3876878913424392422977865 2907659185068294317233399)
      ·
        refine ⟨4361488777602441475850099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907659185068294317233399 4361488777602441475850099)
        ·
          refine ⟨6542233166403662213775149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361488777602441475850099 6542233166403662213775149)
          ·
            refine ⟨2453337437401373330165681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6542233166403662213775149 2453337437401373330165681)
            ·
              refine ⟨1840003078051029997624261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2453337437401373330165681 1840003078051029997624261)
              ·
                refine ⟨345000577134568124554549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1840003078051029997624261 345000577134568124554549)
                ·
                  refine ⟨32343804106365761676989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345000577134568124554549 32343804106365761676989)
                  ·
                    rfl

theorem cell20_70863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_70863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70863 prefixEnd_70863 := by exact prefixLift 70863
  have htrace : WordTrace (prefixWord ++ tailWord_70863) baseStart_70863 baseEnd_70863 := by
    simpa [prefixWord, tailWord_70863, baseEnd_70863] using wordTrace_append hprefix tailTrace_70863
  have hstable : (prefixWord ++ tailWord_70863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70863).length < 2 ^ (prefixWord ++ tailWord_70863).sum := by decide
  have hdescent : baseEnd_70863 < baseStart_70863 := by decide
  rcases family_descends (prefixWord ++ tailWord_70863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70880 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_70880 : Nat := 118140960795 + 70880 * 2 ^ 59
def prefixEnd_70880 : Nat := 4983230072969 + 3 ^ 40 * 70880 * 2
def baseEnd_70880 : Nat := 32351563369589258110253

theorem tailTrace_70880 : CollatzResearch.WordTrace tailWord_70880 prefixEnd_70880 32351563369589258110253 := by
  unfold tailWord_70880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292602991610670092677047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1723470655480893456902729 1292602991610670092677047)
  ·
    refine ⟨1938904487416005139015571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1292602991610670092677047 1938904487416005139015571)
    ·
      refine ⟨2908356731124007708523357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1938904487416005139015571 2908356731124007708523357)
      ·
        refine ⟨1090633774171502890696259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2908356731124007708523357 1090633774171502890696259)
        ·
          refine ⟨1635950661257254336044389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090633774171502890696259 1635950661257254336044389)
          ·
            refine ⟨306740748985735188008323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1635950661257254336044389 306740748985735188008323)
            ·
              refine ⟨460111123478602782012485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306740748985735188008323 460111123478602782012485)
              ·
                refine ⟨86270835652238021627341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 460111123478602782012485 86270835652238021627341)
                ·
                  refine ⟨32351563369589258110253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86270835652238021627341 32351563369589258110253)
                  ·
                    rfl

theorem cell20_70880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_70880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70880 prefixEnd_70880 := by exact prefixLift 70880
  have htrace : WordTrace (prefixWord ++ tailWord_70880) baseStart_70880 baseEnd_70880 := by
    simpa [prefixWord, tailWord_70880, baseEnd_70880] using wordTrace_append hprefix tailTrace_70880
  have hstable : (prefixWord ++ tailWord_70880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70880).length < 2 ^ (prefixWord ++ tailWord_70880).sum := by decide
  have hdescent : baseEnd_70880 < baseStart_70880 := by decide
  rcases family_descends (prefixWord ++ tailWord_70880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70911 : List Nat := [1, 1, 2, 2, 1, 6, 3, 4]
def baseStart_70911 : Nat := 118140960795 + 70911 * 2 ^ 59
def prefixEnd_70911 : Nat := 4983230072969 + 3 ^ 40 * 70911 * 2
def baseEnd_70911 : Nat := 10788570871430309358931

theorem tailTrace_70911 : CollatzResearch.WordTrace tailWord_70911 prefixEnd_70911 10788570871430309358931 := by
  unfold tailWord_70911
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586336646109032479732587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1724224430739354986488391 2586336646109032479732587)
  ·
    refine ⟨3879504969163548719598881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2586336646109032479732587 3879504969163548719598881)
    ·
      refine ⟨2909628726872661539699161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3879504969163548719598881 2909628726872661539699161)
      ·
        refine ⟨2182221545154496154774371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2909628726872661539699161 2182221545154496154774371)
        ·
          refine ⟨3273332317731744232161557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182221545154496154774371 3273332317731744232161557)
          ·
            refine ⟨153437452393675510882573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3273332317731744232161557 153437452393675510882573)
            ·
              refine ⟨57539044647628316580965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153437452393675510882573 57539044647628316580965)
              ·
                refine ⟨10788570871430309358931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57539044647628316580965 10788570871430309358931)
                ·
                  rfl

theorem cell20_70911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_70911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70911 prefixEnd_70911 := by exact prefixLift 70911
  have htrace : WordTrace (prefixWord ++ tailWord_70911) baseStart_70911 baseEnd_70911 := by
    simpa [prefixWord, tailWord_70911, baseEnd_70911] using wordTrace_append hprefix tailTrace_70911
  have hstable : (prefixWord ++ tailWord_70911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70911).length < 2 ^ (prefixWord ++ tailWord_70911).sum := by decide
  have hdescent : baseEnd_70911 < baseStart_70911 := by decide
  rcases family_descends (prefixWord ++ tailWord_70911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70952 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_70952 : Nat := 118140960795 + 70952 * 2 ^ 59
def prefixEnd_70952 : Nat := 4983230072969 + 3 ^ 40 * 70952 * 2
def baseEnd_70952 : Nat := 32384426131477007709959

theorem tailTrace_70952 : CollatzResearch.WordTrace tailWord_70952 prefixEnd_70952 32384426131477007709959 := by
  unfold tailWord_70952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1293916019480248240987555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1725221359306997654650073 1293916019480248240987555)
  ·
    refine ⟨1940874029220372361481333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1293916019480248240987555 1940874029220372361481333)
    ·
      refine ⟨181956940239409908888875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1940874029220372361481333 181956940239409908888875)
      ·
        refine ⟨272935410359114863333313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181956940239409908888875 272935410359114863333313)
        ·
          refine ⟨204701557769336147499985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272935410359114863333313 204701557769336147499985)
          ·
            refine ⟨153526168327002110624989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204701557769336147499985 153526168327002110624989)
            ·
              refine ⟨57572313122625791484371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153526168327002110624989 57572313122625791484371)
              ·
                refine ⟨86358469683938687226557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57572313122625791484371 86358469683938687226557)
                ·
                  refine ⟨32384426131477007709959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86358469683938687226557 32384426131477007709959)
                  ·
                    rfl

theorem cell20_70952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_70952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70952 prefixEnd_70952 := by exact prefixLift 70952
  have htrace : WordTrace (prefixWord ++ tailWord_70952) baseStart_70952 baseEnd_70952 := by
    simpa [prefixWord, tailWord_70952, baseEnd_70952] using wordTrace_append hprefix tailTrace_70952
  have hstable : (prefixWord ++ tailWord_70952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70952).length < 2 ^ (prefixWord ++ tailWord_70952).sum := by decide
  have hdescent : baseEnd_70952 < baseStart_70952 := by decide
  rcases family_descends (prefixWord ++ tailWord_70952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70963 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_70963 : Nat := 118140960795 + 70963 * 2 ^ 59
def prefixEnd_70963 : Nat := 4983230072969 + 3 ^ 40 * 70963 * 2
def baseEnd_70963 : Nat := 32389446831209858343247

theorem tailTrace_70963 : CollatzResearch.WordTrace tailWord_70963 prefixEnd_70963 32389446831209858343247 := by
  unfold tailWord_70963
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588233241920645360625543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1725488827947096907083695 2588233241920645360625543)
  ·
    refine ⟨3882349862880968040938315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2588233241920645360625543 3882349862880968040938315)
    ·
      refine ⟨5823524794321452061407473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3882349862880968040938315 5823524794321452061407473)
      ·
        refine ⟨4367643595741089046055605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5823524794321452061407473 4367643595741089046055605)
        ·
          refine ⟨409466587100727098067713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4367643595741089046055605 409466587100727098067713)
          ·
            refine ⟨307099940325545323550785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409466587100727098067713 307099940325545323550785)
            ·
              refine ⟨230324955244158992663089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307099940325545323550785 230324955244158992663089)
              ·
                refine ⟨172743716433119244497317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230324955244158992663089 172743716433119244497317)
                ·
                  refine ⟨32389446831209858343247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172743716433119244497317 32389446831209858343247)
                  ·
                    rfl

theorem cell20_70963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_70963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70963 prefixEnd_70963 := by exact prefixLift 70963
  have htrace : WordTrace (prefixWord ++ tailWord_70963) baseStart_70963 baseEnd_70963 := by
    simpa [prefixWord, tailWord_70963, baseEnd_70963] using wordTrace_append hprefix tailTrace_70963
  have hstable : (prefixWord ++ tailWord_70963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70963).length < 2 ^ (prefixWord ++ tailWord_70963).sum := by decide
  have hdescent : baseEnd_70963 < baseStart_70963 := by decide
  rcases family_descends (prefixWord ++ tailWord_70963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70970 : List Nat := [3, 1, 1, 1, 4, 1, 3, 6]
def baseStart_70970 : Nat := 118140960795 + 70970 * 2 ^ 59
def prefixEnd_70970 : Nat := 4983230072969 + 3 ^ 40 * 70970 * 2
def baseEnd_70970 : Nat := 10797547273982981703295

theorem tailTrace_70970 : CollatzResearch.WordTrace tailWord_70970 prefixEnd_70970 10797547273982981703295 := by
  unfold tailWord_70970
  simp only [CollatzResearch.WordTrace]
  refine ⟨647122138223821389032591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1725659035263523704086909 647122138223821389032591)
  ·
    refine ⟨970683207335732083548887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 647122138223821389032591 970683207335732083548887)
    ·
      refine ⟨1456024811003598125323331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970683207335732083548887 1456024811003598125323331)
      ·
        refine ⟨2184037216505397187984997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456024811003598125323331 2184037216505397187984997)
        ·
          refine ⟨409506978094761972747187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2184037216505397187984997 409506978094761972747187)
          ·
            refine ⟨614260467142142959120781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409506978094761972747187 614260467142142959120781)
            ·
              refine ⟨230347675178303609670293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 614260467142142959120781 230347675178303609670293)
              ·
                refine ⟨10797547273982981703295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 230347675178303609670293 10797547273982981703295)
                ·
                  rfl

theorem cell20_70970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_70970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70970 prefixEnd_70970 := by exact prefixLift 70970
  have htrace : WordTrace (prefixWord ++ tailWord_70970) baseStart_70970 baseEnd_70970 := by
    simpa [prefixWord, tailWord_70970, baseEnd_70970] using wordTrace_append hprefix tailTrace_70970
  have hstable : (prefixWord ++ tailWord_70970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70970).length < 2 ^ (prefixWord ++ tailWord_70970).sum := by decide
  have hdescent : baseEnd_70970 < baseStart_70970 := by decide
  rcases family_descends (prefixWord ++ tailWord_70970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70994 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_70994 : Nat := 118140960795 + 70994 * 2 ^ 59
def prefixEnd_70994 : Nat := 4983230072969 + 3 ^ 40 * 70994 * 2
def baseEnd_70994 : Nat := 32403596075911528309787

theorem tailTrace_70994 : CollatzResearch.WordTrace tailWord_70994 prefixEnd_70994 32403596075911528309787 := by
  unfold tailWord_70994
  simp only [CollatzResearch.WordTrace]
  refine ⟨647340976202084413751009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1726242603205558436669357 647340976202084413751009)
  ·
    refine ⟨485505732151563310313257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 647340976202084413751009 485505732151563310313257)
    ·
      refine ⟨364129299113672482734943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 485505732151563310313257 364129299113672482734943)
      ·
        refine ⟨546193948670508724102415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364129299113672482734943 546193948670508724102415)
        ·
          refine ⟨819290923005763086153623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546193948670508724102415 819290923005763086153623)
          ·
            refine ⟨1228936384508644629230435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819290923005763086153623 1228936384508644629230435)
            ·
              refine ⟨1843404576762966943845653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228936384508644629230435 1843404576762966943845653)
              ·
                refine ⟨86409589535764075492765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1843404576762966943845653 86409589535764075492765)
                ·
                  refine ⟨32403596075911528309787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86409589535764075492765 32403596075911528309787)
                  ·
                    rfl

theorem cell20_70994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_70994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_70994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_70994 prefixEnd_70994 := by exact prefixLift 70994
  have htrace : WordTrace (prefixWord ++ tailWord_70994) baseStart_70994 baseEnd_70994 := by
    simpa [prefixWord, tailWord_70994, baseEnd_70994] using wordTrace_append hprefix tailTrace_70994
  have hstable : (prefixWord ++ tailWord_70994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70994).length < 2 ^ (prefixWord ++ tailWord_70994).sum := by decide
  have hdescent : baseEnd_70994 < baseStart_70994 := by decide
  rcases family_descends (prefixWord ++ tailWord_70994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71001 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_71001 : Nat := 118140960795 + 71001 * 2 ^ 59
def prefixEnd_71001 : Nat := 4983230072969 + 3 ^ 40 * 71001 * 2
def baseEnd_71001 : Nat := 32406791066650615076425

theorem tailTrace_71001 : CollatzResearch.WordTrace tailWord_71001 prefixEnd_71001 32406791066650615076425 := by
  unfold tailWord_71001
  simp only [CollatzResearch.WordTrace]
  refine ⟨2589619215782977850508857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1726412810521985233672571 2589619215782977850508857)
  ·
    refine ⟨1942214411837233387881643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2589619215782977850508857 1942214411837233387881643)
    ·
      refine ⟨2913321617755850081822465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942214411837233387881643 2913321617755850081822465)
      ·
        refine ⟨2184991213316887561366849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2913321617755850081822465 2184991213316887561366849)
        ·
          refine ⟨1638743409987665671025137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184991213316887561366849 1638743409987665671025137)
          ·
            refine ⟨1229057557490749253268853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1638743409987665671025137 1229057557490749253268853)
            ·
              refine ⟨115224146014757742493955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1229057557490749253268853 115224146014757742493955)
              ·
                refine ⟨172836219022136613740933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115224146014757742493955 172836219022136613740933)
                ·
                  refine ⟨32406791066650615076425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172836219022136613740933 32406791066650615076425)
                  ·
                    rfl

theorem cell20_71001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_71001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71001 prefixEnd_71001 := by exact prefixLift 71001
  have htrace : WordTrace (prefixWord ++ tailWord_71001) baseStart_71001 baseEnd_71001 := by
    simpa [prefixWord, tailWord_71001, baseEnd_71001] using wordTrace_append hprefix tailTrace_71001
  have hstable : (prefixWord ++ tailWord_71001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71001).length < 2 ^ (prefixWord ++ tailWord_71001).sum := by decide
  have hdescent : baseEnd_71001 < baseStart_71001 := by decide
  rcases family_descends (prefixWord ++ tailWord_71001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71008 : List Nat := [2, 1, 1, 3, 4, 1, 1, 7]
def baseStart_71008 : Nat := 118140960795 + 71008 * 2 ^ 59
def prefixEnd_71008 : Nat := 4983230072969 + 3 ^ 40 * 71008 * 2
def baseEnd_71008 : Nat := 10803328685796567281021

theorem tailTrace_71008 : CollatzResearch.WordTrace tailWord_71008 prefixEnd_71008 10803328685796567281021 := by
  unfold tailWord_71008
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294937263378809023006839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1726583017838412030675785 1294937263378809023006839)
  ·
    refine ⟨1942405895068213534510259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1294937263378809023006839 1942405895068213534510259)
    ·
      refine ⟨2913608842602320301765389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942405895068213534510259 2913608842602320301765389)
      ·
        refine ⟨1092603315975870113162021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2913608842602320301765389 1092603315975870113162021)
        ·
          refine ⟨204863121745475646217879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1092603315975870113162021 204863121745475646217879)
          ·
            refine ⟨307294682618213469326819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204863121745475646217879 307294682618213469326819)
            ·
              refine ⟨460942023927320203990229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307294682618213469326819 460942023927320203990229)
              ·
                refine ⟨10803328685796567281021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 460942023927320203990229 10803328685796567281021)
                ·
                  rfl

theorem cell20_71008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_71008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71008 prefixEnd_71008 := by exact prefixLift 71008
  have htrace : WordTrace (prefixWord ++ tailWord_71008) baseStart_71008 baseEnd_71008 := by
    simpa [prefixWord, tailWord_71008, baseEnd_71008] using wordTrace_append hprefix tailTrace_71008
  have hstable : (prefixWord ++ tailWord_71008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71008).length < 2 ^ (prefixWord ++ tailWord_71008).sum := by decide
  have hdescent : baseEnd_71008 < baseStart_71008 := by decide
  rcases family_descends (prefixWord ++ tailWord_71008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71011 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 3]
def baseStart_71011 : Nat := 118140960795 + 71011 * 2 ^ 59
def prefixEnd_71011 : Nat := 4983230072969 + 3 ^ 40 * 71011 * 2
def baseEnd_71011 : Nat := 32411355339135024743051

theorem tailTrace_71011 : CollatzResearch.WordTrace tailWord_71011 prefixEnd_71011 32411355339135024743051 := by
  unfold tailWord_71011
  simp only [CollatzResearch.WordTrace]
  refine ⟨2589983945746749558372887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1726655963831166372248591 2589983945746749558372887)
  ·
    refine ⟨3884975918620124337559331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2589983945746749558372887 3884975918620124337559331)
    ·
      refine ⟨5827463877930186506338997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3884975918620124337559331 5827463877930186506338997)
      ·
        refine ⟨546324738555954984969281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5827463877930186506338997 546324738555954984969281)
        ·
          refine ⟨409743553916966238726961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546324738555954984969281 409743553916966238726961)
          ·
            refine ⟨307307665437724679045221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409743553916966238726961 307307665437724679045221)
            ·
              refine ⟨57620187269573377320979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 307307665437724679045221 57620187269573377320979)
              ·
                refine ⟨86430280904360065981469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57620187269573377320979 86430280904360065981469)
                ·
                  refine ⟨32411355339135024743051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86430280904360065981469 32411355339135024743051)
                  ·
                    rfl

theorem cell20_71011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 3].length) (baseStart_71011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71011 prefixEnd_71011 := by exact prefixLift 71011
  have htrace : WordTrace (prefixWord ++ tailWord_71011) baseStart_71011 baseEnd_71011 := by
    simpa [prefixWord, tailWord_71011, baseEnd_71011] using wordTrace_append hprefix tailTrace_71011
  have hstable : (prefixWord ++ tailWord_71011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71011).length < 2 ^ (prefixWord ++ tailWord_71011).sum := by decide
  have hdescent : baseEnd_71011 < baseStart_71011 := by decide
  rcases family_descends (prefixWord ++ tailWord_71011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71049 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 3]
def baseStart_71049 : Nat := 118140960795 + 71049 * 2 ^ 59
def prefixEnd_71049 : Nat := 4983230072969 + 3 ^ 40 * 71049 * 2
def baseEnd_71049 : Nat := 32428699574575781476229

theorem tailTrace_71049 : CollatzResearch.WordTrace tailWord_71049 prefixEnd_71049 32428699574575781476229 := by
  unfold tailWord_71049
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591369919609082048256201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1727579946406054698837467 2591369919609082048256201)
  ·
    refine ⟨1943527439706811536192151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2591369919609082048256201 1943527439706811536192151)
    ·
      refine ⟨2915291159560217304288227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943527439706811536192151 2915291159560217304288227)
      ·
        refine ⟨4372936739340325956432341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915291159560217304288227 4372936739340325956432341)
        ·
          refine ⟨102490704828288889603883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4372936739340325956432341 102490704828288889603883)
          ·
            refine ⟨153736057242433334405825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102490704828288889603883 153736057242433334405825)
            ·
              refine ⟨115302042931825000804369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153736057242433334405825 115302042931825000804369)
              ·
                refine ⟨86476532198868750603277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115302042931825000804369 86476532198868750603277)
                ·
                  refine ⟨32428699574575781476229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86476532198868750603277 32428699574575781476229)
                  ·
                    rfl

theorem cell20_71049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_71049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71049 prefixEnd_71049 := by exact prefixLift 71049
  have htrace : WordTrace (prefixWord ++ tailWord_71049) baseStart_71049 baseEnd_71049 := by
    simpa [prefixWord, tailWord_71049, baseEnd_71049] using wordTrace_append hprefix tailTrace_71049
  have hstable : (prefixWord ++ tailWord_71049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71049).length < 2 ^ (prefixWord ++ tailWord_71049).sum := by decide
  have hdescent : baseEnd_71049 < baseStart_71049 := by decide
  rcases family_descends (prefixWord ++ tailWord_71049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71125 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 3]
def baseStart_71125 : Nat := 118140960795 + 71125 * 2 ^ 59
def prefixEnd_71125 : Nat := 4983230072969 + 3 ^ 40 * 71125 * 2
def baseEnd_71125 : Nat := 32463388045457294942585

theorem tailTrace_71125 : CollatzResearch.WordTrace tailWord_71125 prefixEnd_71125 32463388045457294942585 := by
  unfold tailWord_71125
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594141867333747028022829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1729427911555831352015219 2594141867333747028022829)
  ·
    refine ⟨972803200250155135508561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2594141867333747028022829 972803200250155135508561)
    ·
      refine ⟨729602400187616351631421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 972803200250155135508561 729602400187616351631421)
      ·
        refine ⟨273600900070356131861783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 729602400187616351631421 273600900070356131861783)
        ·
          refine ⟨410401350105534197792675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273600900070356131861783 410401350105534197792675)
          ·
            refine ⟨615602025158301296689013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410401350105534197792675 615602025158301296689013)
            ·
              refine ⟨57712689858590746564595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 615602025158301296689013 57712689858590746564595)
              ·
                refine ⟨86569034787886119846893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57712689858590746564595 86569034787886119846893)
                ·
                  refine ⟨32463388045457294942585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86569034787886119846893 32463388045457294942585)
                  ·
                    rfl

theorem cell20_71125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_71125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71125 prefixEnd_71125 := by exact prefixLift 71125
  have htrace : WordTrace (prefixWord ++ tailWord_71125) baseStart_71125 baseEnd_71125 := by
    simpa [prefixWord, tailWord_71125, baseEnd_71125] using wordTrace_append hprefix tailTrace_71125
  have hstable : (prefixWord ++ tailWord_71125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71125).length < 2 ^ (prefixWord ++ tailWord_71125).sum := by decide
  have hdescent : baseEnd_71125 < baseStart_71125 := by decide
  rcases family_descends (prefixWord ++ tailWord_71125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71136 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_71136 : Nat := 118140960795 + 71136 * 2 ^ 59
def prefixEnd_71136 : Nat := 4983230072969 + 3 ^ 40 * 71136 * 2
def baseEnd_71136 : Nat := 32468408745190145575873

theorem tailTrace_71136 : CollatzResearch.WordTrace tailWord_71136 prefixEnd_71136 32468408745190145575873 := by
  unfold tailWord_71136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297271535146947953336631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1729695380195930604448841 1297271535146947953336631)
  ·
    refine ⟨1945907302720421930004947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297271535146947953336631 1945907302720421930004947)
    ·
      refine ⟨2918860954080632895007421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1945907302720421930004947 2918860954080632895007421)
      ·
        refine ⟨1094572857780237335627783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2918860954080632895007421 1094572857780237335627783)
        ·
          refine ⟨1641859286670356003441675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094572857780237335627783 1641859286670356003441675)
          ·
            refine ⟨2462788930005534005162513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641859286670356003441675 2462788930005534005162513)
            ·
              refine ⟨1847091697504150503871885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462788930005534005162513 1847091697504150503871885)
              ·
                refine ⟨692659386564056438951957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1847091697504150503871885 692659386564056438951957)
                ·
                  refine ⟨32468408745190145575873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 692659386564056438951957 32468408745190145575873)
                  ·
                    rfl

theorem cell20_71136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_71136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71136 prefixEnd_71136 := by exact prefixLift 71136
  have htrace : WordTrace (prefixWord ++ tailWord_71136) baseStart_71136 baseEnd_71136 := by
    simpa [prefixWord, tailWord_71136, baseEnd_71136] using wordTrace_append hprefix tailTrace_71136
  have hstable : (prefixWord ++ tailWord_71136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71136).length < 2 ^ (prefixWord ++ tailWord_71136).sum := by decide
  have hdescent : baseEnd_71136 < baseStart_71136 := by decide
  rcases family_descends (prefixWord ++ tailWord_71136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71139 : List Nat := [1, 1, 1, 6, 2, 1, 4, 4]
def baseStart_71139 : Nat := 118140960795 + 71139 * 2 ^ 59
def prefixEnd_71139 : Nat := 4983230072969 + 3 ^ 40 * 71139 * 2
def baseEnd_71139 : Nat := 10823259342311822825287

theorem tailTrace_71139 : CollatzResearch.WordTrace tailWord_71139 prefixEnd_71139 10823259342311822825287 := by
  unfold tailWord_71139
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594652489283027419032471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1729768326188684946021647 2594652489283027419032471)
  ·
    refine ⟨3891978733924541128548707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2594652489283027419032471 3891978733924541128548707)
    ·
      refine ⟨5837968100886811692823061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3891978733924541128548707 5837968100886811692823061)
      ·
        refine ⟨273654754729069298101081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5837968100886811692823061 273654754729069298101081)
        ·
          refine ⟨205241066046801973575811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273654754729069298101081 205241066046801973575811)
          ·
            refine ⟨307861599070202960363717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205241066046801973575811 307861599070202960363717)
            ·
              refine ⟨57724049825663055068197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 307861599070202960363717 57724049825663055068197)
              ·
                refine ⟨10823259342311822825287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57724049825663055068197 10823259342311822825287)
                ·
                  rfl

theorem cell20_71139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_71139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71139 prefixEnd_71139 := by exact prefixLift 71139
  have htrace : WordTrace (prefixWord ++ tailWord_71139) baseStart_71139 baseEnd_71139 := by
    simpa [prefixWord, tailWord_71139, baseEnd_71139] using wordTrace_append hprefix tailTrace_71139
  have hstable : (prefixWord ++ tailWord_71139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71139).length < 2 ^ (prefixWord ++ tailWord_71139).sum := by decide
  have hdescent : baseEnd_71139 < baseStart_71139 := by decide
  rcases family_descends (prefixWord ++ tailWord_71139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71160 : List Nat := [2, 1, 2, 1, 1, 7, 6]
def baseStart_71160 : Nat := 118140960795 + 71160 * 2 ^ 59
def prefixEnd_71160 : Nat := 4983230072969 + 3 ^ 40 * 71160 * 2
def baseEnd_71160 : Nat := 3608818111016969863975

theorem tailTrace_71160 : CollatzResearch.WordTrace tailWord_71160 prefixEnd_71160 3608818111016969863975 := by
  unfold tailWord_71160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297709211103474002773467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1730278948137965337031289 1297709211103474002773467)
  ·
    refine ⟨1946563816655211004160201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297709211103474002773467 1946563816655211004160201)
    ·
      refine ⟨1459922862491408253120151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1946563816655211004160201 1459922862491408253120151)
      ·
        refine ⟨2189884293737112379680227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459922862491408253120151 2189884293737112379680227)
        ·
          refine ⟨3284826440605668569520341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189884293737112379680227 3284826440605668569520341)
          ·
            refine ⟨76988119701695357098133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3284826440605668569520341 76988119701695357098133)
            ·
              refine ⟨3608818111016969863975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76988119701695357098133 3608818111016969863975)
              ·
                rfl

theorem cell20_71160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 6].length) (baseStart_71160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71160 prefixEnd_71160 := by exact prefixLift 71160
  have htrace : WordTrace (prefixWord ++ tailWord_71160) baseStart_71160 baseEnd_71160 := by
    simpa [prefixWord, tailWord_71160, baseEnd_71160] using wordTrace_append hprefix tailTrace_71160
  have hstable : (prefixWord ++ tailWord_71160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71160).length < 2 ^ (prefixWord ++ tailWord_71160).sum := by decide
  have hdescent : baseEnd_71160 < baseStart_71160 := by decide
  rcases family_descends (prefixWord ++ tailWord_71160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71166 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_71166 : Nat := 118140960795 + 71166 * 2 ^ 59
def prefixEnd_71166 : Nat := 4983230072969 + 3 ^ 40 * 71166 * 2
def baseEnd_71166 : Nat := 32482101562643374575751

theorem tailTrace_71166 : CollatzResearch.WordTrace tailWord_71166 prefixEnd_71166 32482101562643374575751 := by
  unfold tailWord_71166
  simp only [CollatzResearch.WordTrace]
  refine ⟨324454657523151378783169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1730424840123474020176901 324454657523151378783169)
  ·
    refine ⟨243340993142363534087377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 324454657523151378783169 243340993142363534087377)
    ·
      refine ⟨182505744856772650565533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243340993142363534087377 182505744856772650565533)
      ·
        refine ⟨68439654321289743962075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182505744856772650565533 68439654321289743962075)
        ·
          refine ⟨102659481481934615943113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68439654321289743962075 102659481481934615943113)
          ·
            refine ⟨76994611111450961957335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102659481481934615943113 76994611111450961957335)
            ·
              refine ⟨115491916667176442936003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76994611111450961957335 115491916667176442936003)
              ·
                refine ⟨173237875000764664404005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115491916667176442936003 173237875000764664404005)
                ·
                  refine ⟨32482101562643374575751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173237875000764664404005 32482101562643374575751)
                  ·
                    rfl

theorem cell20_71166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_71166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71166 prefixEnd_71166 := by exact prefixLift 71166
  have htrace : WordTrace (prefixWord ++ tailWord_71166) baseStart_71166 baseEnd_71166 := by
    simpa [prefixWord, tailWord_71166, baseEnd_71166] using wordTrace_append hprefix tailTrace_71166
  have hstable : (prefixWord ++ tailWord_71166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71166).length < 2 ^ (prefixWord ++ tailWord_71166).sum := by decide
  have hdescent : baseEnd_71166 < baseStart_71166 := by decide
  rcases family_descends (prefixWord ++ tailWord_71166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71180 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_71180 : Nat := 118140960795 + 71180 * 2 ^ 59
def prefixEnd_71180 : Nat := 4983230072969 + 3 ^ 40 * 71180 * 2
def baseEnd_71180 : Nat := 32488491544121548109027

theorem tailTrace_71180 : CollatzResearch.WordTrace tailWord_71180 prefixEnd_71180 32488491544121548109027 := by
  unfold tailWord_71180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298073941067245710637497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1730765254756327614183329 1298073941067245710637497)
  ·
    refine ⟨973555455800434282978123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1298073941067245710637497 973555455800434282978123)
    ·
      refine ⟨1460333183700651424467185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973555455800434282978123 1460333183700651424467185)
      ·
        refine ⟨1095249887775488568350389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460333183700651424467185 1095249887775488568350389)
        ·
          refine ⟨102679676978952053282849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1095249887775488568350389 102679676978952053282849)
          ·
            refine ⟨77009757734214039962137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102679676978952053282849 77009757734214039962137)
            ·
              refine ⟨57757318300660529971603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77009757734214039962137 57757318300660529971603)
              ·
                refine ⟨86635977450990794957405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57757318300660529971603 86635977450990794957405)
                ·
                  refine ⟨32488491544121548109027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86635977450990794957405 32488491544121548109027)
                  ·
                    rfl

theorem cell20_71180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_71180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71180 prefixEnd_71180 := by exact prefixLift 71180
  have htrace : WordTrace (prefixWord ++ tailWord_71180) baseStart_71180 baseEnd_71180 := by
    simpa [prefixWord, tailWord_71180, baseEnd_71180] using wordTrace_append hprefix tailTrace_71180
  have hstable : (prefixWord ++ tailWord_71180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71180).length < 2 ^ (prefixWord ++ tailWord_71180).sum := by decide
  have hdescent : baseEnd_71180 < baseStart_71180 := by decide
  rcases family_descends (prefixWord ++ tailWord_71180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71219 : List Nat := [1, 1, 1, 2, 4, 11]
def baseStart_71219 : Nat := 118140960795 + 71219 * 2 ^ 59
def prefixEnd_71219 : Nat := 4983230072969 + 3 ^ 40 * 71219 * 2
def baseEnd_71219 : Nat := 1203936748400397992921

theorem tailTrace_71219 : CollatzResearch.WordTrace tailWord_71219 prefixEnd_71219 1203936748400397992921 := by
  unfold tailWord_71219
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597570328993201081944711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1731713552662134054629807 2597570328993201081944711)
  ·
    refine ⟨3896355493489801622917067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2597570328993201081944711 3896355493489801622917067)
    ·
      refine ⟨5844533240234702434375601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3896355493489801622917067 5844533240234702434375601)
      ·
        refine ⟨4383399930176026825781701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5844533240234702434375601 4383399930176026825781701)
        ·
          refine ⟨821887486908005029834069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4383399930176026825781701 821887486908005029834069)
          ·
            refine ⟨1203936748400397992921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 821887486908005029834069 1203936748400397992921)
            ·
              rfl

theorem cell20_71219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 11].length) (baseStart_71219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71219 prefixEnd_71219 := by exact prefixLift 71219
  have htrace : WordTrace (prefixWord ++ tailWord_71219) baseStart_71219 baseEnd_71219 := by
    simpa [prefixWord, tailWord_71219, baseEnd_71219] using wordTrace_append hprefix tailTrace_71219
  have hstable : (prefixWord ++ tailWord_71219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71219).length < 2 ^ (prefixWord ++ tailWord_71219).sum := by decide
  have hdescent : baseEnd_71219 < baseStart_71219 := by decide
  rcases family_descends (prefixWord ++ tailWord_71219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71225 : List Nat := [1, 2, 1, 5, 1, 2, 4, 2, 2]
def baseStart_71225 : Nat := 118140960795 + 71225 * 2 ^ 59
def prefixEnd_71225 : Nat := 4983230072969 + 3 ^ 40 * 71225 * 2
def baseEnd_71225 : Nat := 32509030770301391608843

theorem tailTrace_71225 : CollatzResearch.WordTrace tailWord_71225 prefixEnd_71225 32509030770301391608843 := by
  unfold tailWord_71225
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597789166971464106663129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1731859444647642737775419 2597789166971464106663129)
  ·
    refine ⟨1948341875228598079997347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2597789166971464106663129 1948341875228598079997347)
    ·
      refine ⟨2922512812842897119996021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1948341875228598079997347 2922512812842897119996021)
      ·
        refine ⟨273985576204021604999627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2922512812842897119996021 273985576204021604999627)
        ·
          refine ⟨410978364306032407499441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273985576204021604999627 410978364306032407499441)
          ·
            refine ⟨308233773229524305624581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410978364306032407499441 308233773229524305624581)
            ·
              refine ⟨57793832480535807304609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 308233773229524305624581 57793832480535807304609)
              ·
                refine ⟨43345374360401855478457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57793832480535807304609 43345374360401855478457)
                ·
                  refine ⟨32509030770301391608843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43345374360401855478457 32509030770301391608843)
                  ·
                    rfl

theorem cell20_71225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_71225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71225 prefixEnd_71225 := by exact prefixLift 71225
  have htrace : WordTrace (prefixWord ++ tailWord_71225) baseStart_71225 baseEnd_71225 := by
    simpa [prefixWord, tailWord_71225, baseEnd_71225] using wordTrace_append hprefix tailTrace_71225
  have hstable : (prefixWord ++ tailWord_71225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71225).length < 2 ^ (prefixWord ++ tailWord_71225).sum := by decide
  have hdescent : baseEnd_71225 < baseStart_71225 := by decide
  rcases family_descends (prefixWord ++ tailWord_71225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71257 : List Nat := [1, 2, 1, 2, 2, 1, 1, 10]
def baseStart_71257 : Nat := 118140960795 + 71257 * 2 ^ 59
def prefixEnd_71257 : Nat := 4983230072969 + 3 ^ 40 * 71257 * 2
def baseEnd_71257 : Nat := 10841212147417167514015

theorem tailTrace_71257 : CollatzResearch.WordTrace tailWord_71257 prefixEnd_71257 10841212147417167514015 := by
  unfold tailWord_71257
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598956302855533571828025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1732637535237022381218683 2598956302855533571828025)
  ·
    refine ⟨1949217227141650178871019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2598956302855533571828025 1949217227141650178871019)
    ·
      refine ⟨2923825840712475268306529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1949217227141650178871019 2923825840712475268306529)
      ·
        refine ⟨2192869380534356451229897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2923825840712475268306529 2192869380534356451229897)
        ·
          refine ⟨1644652035400767338422423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2192869380534356451229897 1644652035400767338422423)
          ·
            refine ⟨2466978053101151007633635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644652035400767338422423 2466978053101151007633635)
            ·
              refine ⟨3700467079651726511450453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466978053101151007633635 3700467079651726511450453)
              ·
                refine ⟨10841212147417167514015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3700467079651726511450453 10841212147417167514015)
                ·
                  rfl

theorem cell20_71257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_71257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71257 prefixEnd_71257 := by exact prefixLift 71257
  have htrace : WordTrace (prefixWord ++ tailWord_71257) baseStart_71257 baseEnd_71257 := by
    simpa [prefixWord, tailWord_71257, baseEnd_71257] using wordTrace_append hprefix tailTrace_71257
  have hstable : (prefixWord ++ tailWord_71257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71257).length < 2 ^ (prefixWord ++ tailWord_71257).sum := by decide
  have hdescent : baseEnd_71257 < baseStart_71257 := by decide
  rcases family_descends (prefixWord ++ tailWord_71257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71274 : List Nat := [3, 1, 3, 2, 1, 3, 7]
def baseStart_71274 : Nat := 118140960795 + 71274 * 2 ^ 59
def prefixEnd_71274 : Nat := 4983230072969 + 3 ^ 40 * 71274 * 2
def baseEnd_71274 : Nat := 3614599522830555441701

theorem tailTrace_71274 : CollatzResearch.WordTrace tailWord_71274 prefixEnd_71274 3614599522830555441701 := by
  unfold tailWord_71274
  simp only [CollatzResearch.WordTrace]
  refine ⟨649894085948486368799219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1733050895862630316797917 649894085948486368799219)
  ·
    refine ⟨974841128922729553198829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 649894085948486368799219 974841128922729553198829)
    ·
      refine ⟨365565423346023582449561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 974841128922729553198829 365565423346023582449561)
      ·
        refine ⟨274174067509517686837171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365565423346023582449561 274174067509517686837171)
        ·
          refine ⟨411261101264276530255757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274174067509517686837171 411261101264276530255757)
          ·
            refine ⟨154222912974103698845909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 411261101264276530255757 154222912974103698845909)
            ·
              refine ⟨3614599522830555441701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 154222912974103698845909 3614599522830555441701)
              ·
                rfl

theorem cell20_71274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 7].length) (baseStart_71274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71274 prefixEnd_71274 := by exact prefixLift 71274
  have htrace : WordTrace (prefixWord ++ tailWord_71274) baseStart_71274 baseEnd_71274 := by
    simpa [prefixWord, tailWord_71274, baseEnd_71274] using wordTrace_append hprefix tailTrace_71274
  have hstable : (prefixWord ++ tailWord_71274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71274).length < 2 ^ (prefixWord ++ tailWord_71274).sum := by decide
  have hdescent : baseEnd_71274 < baseStart_71274 := by decide
  rcases family_descends (prefixWord ++ tailWord_71274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71319 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_71319 : Nat := 118140960795 + 71319 * 2 ^ 59
def prefixEnd_71319 : Nat := 4983230072969 + 3 ^ 40 * 71319 * 2
def baseEnd_71319 : Nat := 32551934931654842475125

theorem tailTrace_71319 : CollatzResearch.WordTrace tailWord_71319 prefixEnd_71319 32551934931654842475125 := by
  unfold tailWord_71319
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601217628630918160585011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1734145085753945440390007 2601217628630918160585011)
  ·
    refine ⟨3901826442946377240877517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2601217628630918160585011 3901826442946377240877517)
    ·
      refine ⟨1463184916104891465329069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3901826442946377240877517 1463184916104891465329069)
      ·
        refine ⟨548694343539334299498401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1463184916104891465329069 548694343539334299498401)
        ·
          refine ⟨411520757654500724623801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 548694343539334299498401 411520757654500724623801)
          ·
            refine ⟨308640568240875543467851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411520757654500724623801 308640568240875543467851)
            ·
              refine ⟨462960852361313315201777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308640568240875543467851 462960852361313315201777)
              ·
                refine ⟨347220639270984986401333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462960852361313315201777 347220639270984986401333)
                ·
                  refine ⟨32551934931654842475125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 347220639270984986401333 32551934931654842475125)
                  ·
                    rfl

theorem cell20_71319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_71319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71319 prefixEnd_71319 := by exact prefixLift 71319
  have htrace : WordTrace (prefixWord ++ tailWord_71319) baseStart_71319 baseEnd_71319 := by
    simpa [prefixWord, tailWord_71319, baseEnd_71319] using wordTrace_append hprefix tailTrace_71319
  have hstable : (prefixWord ++ tailWord_71319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71319).length < 2 ^ (prefixWord ++ tailWord_71319).sum := by decide
  have hdescent : baseEnd_71319 < baseStart_71319 := by decide
  rcases family_descends (prefixWord ++ tailWord_71319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71333 : List Nat := [1, 3, 1, 2, 1, 2, 10]
def baseStart_71333 : Nat := 118140960795 + 71333 * 2 ^ 59
def prefixEnd_71333 : Nat := 4983230072969 + 3 ^ 40 * 71333 * 2
def baseEnd_71333 : Nat := 3617591657014779556489

theorem tailTrace_71333 : CollatzResearch.WordTrace tailWord_71333 prefixEnd_71333 3617591657014779556489 := by
  unfold tailWord_71333
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601728250580198551594653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1734485500386799034396435 2601728250580198551594653)
  ·
    refine ⟨975648093967574456847995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2601728250580198551594653 975648093967574456847995)
    ·
      refine ⟨1463472140951361685271993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975648093967574456847995 1463472140951361685271993)
      ·
        refine ⟨1097604105713521263953995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1463472140951361685271993 1097604105713521263953995)
        ·
          refine ⟨1646406158570281895930993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097604105713521263953995 1646406158570281895930993)
          ·
            refine ⟨1234804618927711421948245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646406158570281895930993 1234804618927711421948245)
            ·
              refine ⟨3617591657014779556489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1234804618927711421948245 3617591657014779556489)
              ·
                rfl

theorem cell20_71333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_71333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71333 prefixEnd_71333 := by exact prefixLift 71333
  have htrace : WordTrace (prefixWord ++ tailWord_71333) baseStart_71333 baseEnd_71333 := by
    simpa [prefixWord, tailWord_71333, baseEnd_71333] using wordTrace_append hprefix tailTrace_71333
  have hstable : (prefixWord ++ tailWord_71333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71333).length < 2 ^ (prefixWord ++ tailWord_71333).sum := by decide
  have hdescent : baseEnd_71333 < baseStart_71333 := by decide
  rcases family_descends (prefixWord ++ tailWord_71333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71349 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 3]
def baseStart_71349 : Nat := 118140960795 + 71349 * 2 ^ 59
def prefixEnd_71349 : Nat := 4983230072969 + 3 ^ 40 * 71349 * 2
def baseEnd_71349 : Nat := 32565627749108071475003

theorem tailTrace_71349 : CollatzResearch.WordTrace tailWord_71349 prefixEnd_71349 32565627749108071475003 := by
  unfold tailWord_71349
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602311818522233284177101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1734874545681488856118067 2602311818522233284177101)
  ·
    refine ⟨975866931945837481566413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2602311818522233284177101 975866931945837481566413)
    ·
      refine ⟨365950099479689055587405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 975866931945837481566413 365950099479689055587405)
      ·
        refine ⟨137231287304883395845277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365950099479689055587405 137231287304883395845277)
        ·
          refine ⟨51461732739331273441979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137231287304883395845277 51461732739331273441979)
          ·
            refine ⟨77192599108996910162969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51461732739331273441979 77192599108996910162969)
            ·
              refine ⟨57894449331747682622227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77192599108996910162969 57894449331747682622227)
              ·
                refine ⟨86841673997621523933341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57894449331747682622227 86841673997621523933341)
                ·
                  refine ⟨32565627749108071475003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86841673997621523933341 32565627749108071475003)
                  ·
                    rfl

theorem cell20_71349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_71349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71349 prefixEnd_71349 := by exact prefixLift 71349
  have htrace : WordTrace (prefixWord ++ tailWord_71349) baseStart_71349 baseEnd_71349 := by
    simpa [prefixWord, tailWord_71349, baseEnd_71349] using wordTrace_append hprefix tailTrace_71349
  have hstable : (prefixWord ++ tailWord_71349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71349).length < 2 ^ (prefixWord ++ tailWord_71349).sum := by decide
  have hdescent : baseEnd_71349 < baseStart_71349 := by decide
  rcases family_descends (prefixWord ++ tailWord_71349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71388 : List Nat := [2, 2, 5, 1, 10]
def baseStart_71388 : Nat := 118140960795 + 71388 * 2 ^ 59
def prefixEnd_71388 : Nat := 4983230072969 + 3 ^ 40 * 71388 * 2
def baseEnd_71388 : Nat := 402264548293793446603

theorem tailTrace_71388 : CollatzResearch.WordTrace tailWord_71388 prefixEnd_71388 402264548293793446603 := by
  unfold tailWord_71388
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301867132690471472423409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1735822843587295296564545 1301867132690471472423409)
  ·
    refine ⟨976400349517853604317557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1301867132690471472423409 976400349517853604317557)
    ·
      refine ⟨91537532767298775404771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 976400349517853604317557 91537532767298775404771)
      ·
        refine ⟨137306299150948163107157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91537532767298775404771 137306299150948163107157)
        ·
          refine ⟨402264548293793446603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 137306299150948163107157 402264548293793446603)
          ·
            rfl

theorem cell20_71388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 10].length) (baseStart_71388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71388 prefixEnd_71388 := by exact prefixLift 71388
  have htrace : WordTrace (prefixWord ++ tailWord_71388) baseStart_71388 baseEnd_71388 := by
    simpa [prefixWord, tailWord_71388, baseEnd_71388] using wordTrace_append hprefix tailTrace_71388
  have hstable : (prefixWord ++ tailWord_71388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71388).length < 2 ^ (prefixWord ++ tailWord_71388).sum := by decide
  have hdescent : baseEnd_71388 < baseStart_71388 := by decide
  rcases family_descends (prefixWord ++ tailWord_71388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71405 : List Nat := [1, 5, 1, 2, 1, 4, 1, 5]
def baseStart_71405 : Nat := 118140960795 + 71405 * 2 ^ 59
def prefixEnd_71405 : Nat := 4983230072969 + 3 ^ 40 * 71405 * 2
def baseEnd_71405 : Nat := 10863729225006921869369

theorem tailTrace_71405 : CollatzResearch.WordTrace tailWord_71405 prefixEnd_71405 10863729225006921869369 := by
  unfold tailWord_71405
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604354306319354848215669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1736236204212903232143779 2604354306319354848215669)
  ·
    refine ⟨244158216217439517020219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2604354306319354848215669 244158216217439517020219)
    ·
      refine ⟨366237324326159275530329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244158216217439517020219 366237324326159275530329)
      ·
        refine ⟨274677993244619456647747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366237324326159275530329 274677993244619456647747)
        ·
          refine ⟨412016989866929184971621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274677993244619456647747 412016989866929184971621)
          ·
            refine ⟨77253185600049222182179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 412016989866929184971621 77253185600049222182179)
            ·
              refine ⟨115879778400073833273269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77253185600049222182179 115879778400073833273269)
              ·
                refine ⟨10863729225006921869369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115879778400073833273269 10863729225006921869369)
                ·
                  rfl

theorem cell20_71405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_71405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71405 prefixEnd_71405 := by exact prefixLift 71405
  have htrace : WordTrace (prefixWord ++ tailWord_71405) baseStart_71405 baseEnd_71405 := by
    simpa [prefixWord, tailWord_71405, baseEnd_71405] using wordTrace_append hprefix tailTrace_71405
  have hstable : (prefixWord ++ tailWord_71405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71405).length < 2 ^ (prefixWord ++ tailWord_71405).sum := by decide
  have hdescent : baseEnd_71405 < baseStart_71405 := by decide
  rcases family_descends (prefixWord ++ tailWord_71405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71422 : List Nat := [4, 2, 2, 1, 3, 1, 3, 4]
def baseStart_71422 : Nat := 118140960795 + 71422 * 2 ^ 59
def prefixEnd_71422 : Nat := 4983230072969 + 3 ^ 40 * 71422 * 2
def baseEnd_71422 : Nat := 10866315646081420680457

theorem tailTrace_71422 : CollatzResearch.WordTrace tailWord_71422 prefixEnd_71422 10866315646081420680457 := by
  unfold tailWord_71422
  simp only [CollatzResearch.WordTrace]
  refine ⟨325621793407220843948065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1736649564838511167723013 325621793407220843948065)
  ·
    refine ⟨244216345055415632961049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 325621793407220843948065 244216345055415632961049)
    ·
      refine ⟨183162258791561724720787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244216345055415632961049 183162258791561724720787)
      ·
        refine ⟨274743388187342587081181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183162258791561724720787 274743388187342587081181)
        ·
          refine ⟨103028770570253470155443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274743388187342587081181 103028770570253470155443)
          ·
            refine ⟨154543155855380205233165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103028770570253470155443 154543155855380205233165)
            ·
              refine ⟨57953683445767576962437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154543155855380205233165 57953683445767576962437)
              ·
                refine ⟨10866315646081420680457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57953683445767576962437 10866315646081420680457)
                ·
                  rfl

theorem cell20_71422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_71422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71422 prefixEnd_71422 := by exact prefixLift 71422
  have htrace : WordTrace (prefixWord ++ tailWord_71422) baseStart_71422 baseEnd_71422 := by
    simpa [prefixWord, tailWord_71422, baseEnd_71422] using wordTrace_append hprefix tailTrace_71422
  have hstable : (prefixWord ++ tailWord_71422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71422).length < 2 ^ (prefixWord ++ tailWord_71422).sum := by decide
  have hdescent : baseEnd_71422 < baseStart_71422 := by decide
  rcases family_descends (prefixWord ++ tailWord_71422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71450 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_71450 : Nat := 118140960795 + 71450 * 2 ^ 59
def prefixEnd_71450 : Nat := 4983230072969 + 3 ^ 40 * 71450 * 2
def baseEnd_71450 : Nat := 32611726901200609107923

theorem tailTrace_71450 : CollatzResearch.WordTrace tailWord_71450 prefixEnd_71450 32611726901200609107923 := by
  unfold tailWord_71450
  simp only [CollatzResearch.WordTrace]
  refine ⟨651498897789081883400951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1737330394104218355735869 651498897789081883400951)
  ·
    refine ⟨977248346683622825101427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 651498897789081883400951 977248346683622825101427)
    ·
      refine ⟨1465872520025434237652141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977248346683622825101427 1465872520025434237652141)
      ·
        refine ⟨549702195009537839119553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1465872520025434237652141 549702195009537839119553)
        ·
          refine ⟨412276646257153379339665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549702195009537839119553 412276646257153379339665)
          ·
            refine ⟨309207484692865034504749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412276646257153379339665 309207484692865034504749)
            ·
              refine ⟨115952806759824387939281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309207484692865034504749 115952806759824387939281)
              ·
                refine ⟨86964605069868290954461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115952806759824387939281 86964605069868290954461)
                ·
                  refine ⟨32611726901200609107923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86964605069868290954461 32611726901200609107923)
                  ·
                    rfl

theorem cell20_71450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_71450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71450 prefixEnd_71450 := by exact prefixLift 71450
  have htrace : WordTrace (prefixWord ++ tailWord_71450) baseStart_71450 baseEnd_71450 := by
    simpa [prefixWord, tailWord_71450, baseEnd_71450] using wordTrace_append hprefix tailTrace_71450
  have hstable : (prefixWord ++ tailWord_71450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71450).length < 2 ^ (prefixWord ++ tailWord_71450).sum := by decide
  have hdescent : baseEnd_71450 < baseStart_71450 := by decide
  rcases family_descends (prefixWord ++ tailWord_71450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71457 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_71457 : Nat := 118140960795 + 71457 * 2 ^ 59
def prefixEnd_71457 : Nat := 4983230072969 + 3 ^ 40 * 71457 * 2
def baseEnd_71457 : Nat := 32614921891939695874561

theorem tailTrace_71457 : CollatzResearch.WordTrace tailWord_71457 prefixEnd_71457 32614921891939695874561 := by
  unfold tailWord_71457
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606250902130967729108625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1737500601420645152739083 2606250902130967729108625)
  ·
    refine ⟨1954688176598225796831469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2606250902130967729108625 1954688176598225796831469)
    ·
      refine ⟨733008066224334673811801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1954688176598225796831469 733008066224334673811801)
      ·
        refine ⟨549756049668251005358851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 733008066224334673811801 549756049668251005358851)
        ·
          refine ⟨824634074502376508038277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549756049668251005358851 824634074502376508038277)
          ·
            refine ⟨154618888969195595257177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 824634074502376508038277 154618888969195595257177)
            ·
              refine ⟨115964166726896696442883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154618888969195595257177 115964166726896696442883)
              ·
                refine ⟨173946250090345044664325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115964166726896696442883 173946250090345044664325)
                ·
                  refine ⟨32614921891939695874561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173946250090345044664325 32614921891939695874561)
                  ·
                    rfl

theorem cell20_71457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_71457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71457 prefixEnd_71457 := by exact prefixLift 71457
  have htrace : WordTrace (prefixWord ++ tailWord_71457) baseStart_71457 baseEnd_71457 := by
    simpa [prefixWord, tailWord_71457, baseEnd_71457] using wordTrace_append hprefix tailTrace_71457
  have hstable : (prefixWord ++ tailWord_71457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71457).length < 2 ^ (prefixWord ++ tailWord_71457).sum := by decide
  have hdescent : baseEnd_71457 < baseStart_71457 := by decide
  rcases family_descends (prefixWord ++ tailWord_71457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71481 : List Nat := [1, 2, 1, 7, 1, 1, 1, 6]
def baseStart_71481 : Nat := 118140960795 + 71481 * 2 ^ 59
def prefixEnd_71481 : Nat := 4983230072969 + 3 ^ 40 * 71481 * 2
def baseEnd_71481 : Nat := 10875292048634093024821

theorem tailTrace_71481 : CollatzResearch.WordTrace tailWord_71481 prefixEnd_71481 10875292048634093024821 := by
  unfold tailWord_71481
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607126254044019827982297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1738084169362679885321531 2607126254044019827982297)
  ·
    refine ⟨1955344690533014870986723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2607126254044019827982297 1955344690533014870986723)
    ·
      refine ⟨2933017035799522306480085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955344690533014870986723 2933017035799522306480085)
      ·
        refine ⟨68742586776551304058127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2933017035799522306480085 68742586776551304058127)
        ·
          refine ⟨103113880164826956087191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68742586776551304058127 103113880164826956087191)
          ·
            refine ⟨154670820247240434130787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103113880164826956087191 154670820247240434130787)
            ·
              refine ⟨232006230370860651196181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154670820247240434130787 232006230370860651196181)
              ·
                refine ⟨10875292048634093024821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 232006230370860651196181 10875292048634093024821)
                ·
                  rfl

theorem cell20_71481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_71481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71481 prefixEnd_71481 := by exact prefixLift 71481
  have htrace : WordTrace (prefixWord ++ tailWord_71481) baseStart_71481 baseEnd_71481 := by
    simpa [prefixWord, tailWord_71481, baseEnd_71481] using wordTrace_append hprefix tailTrace_71481
  have hstable : (prefixWord ++ tailWord_71481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71481).length < 2 ^ (prefixWord ++ tailWord_71481).sum := by decide
  have hdescent : baseEnd_71481 < baseStart_71481 := by decide
  rcases family_descends (prefixWord ++ tailWord_71481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71509 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_71509 : Nat := 118140960795 + 71509 * 2 ^ 59
def prefixEnd_71509 : Nat := 4983230072969 + 3 ^ 40 * 71509 * 2
def baseEnd_71509 : Nat := 32638656108858626141015

theorem tailTrace_71509 : CollatzResearch.WordTrace tailWord_71509 prefixEnd_71509 32638656108858626141015 := by
  unfold tailWord_71509
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608147497942580610001581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1738764998628387073334387 2608147497942580610001581)
  ·
    refine ⟨978055311728467728750593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2608147497942580610001581 978055311728467728750593)
    ·
      refine ⟨733541483796350796562945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 978055311728467728750593 733541483796350796562945)
      ·
        refine ⟨550156112847263097422209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 733541483796350796562945 550156112847263097422209)
        ·
          refine ⟨412617084635447323066657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550156112847263097422209 412617084635447323066657)
          ·
            refine ⟨309462813476585492299993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412617084635447323066657 309462813476585492299993)
            ·
              refine ⟨232097110107439119224995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309462813476585492299993 232097110107439119224995)
              ·
                refine ⟨348145665161158678837493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232097110107439119224995 348145665161158678837493)
                ·
                  refine ⟨32638656108858626141015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348145665161158678837493 32638656108858626141015)
                  ·
                    rfl

theorem cell20_71509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_71509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71509 prefixEnd_71509 := by exact prefixLift 71509
  have htrace : WordTrace (prefixWord ++ tailWord_71509) baseStart_71509 baseEnd_71509 := by
    simpa [prefixWord, tailWord_71509, baseEnd_71509] using wordTrace_append hprefix tailTrace_71509
  have hstable : (prefixWord ++ tailWord_71509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71509).length < 2 ^ (prefixWord ++ tailWord_71509).sum := by decide
  have hdescent : baseEnd_71509 < baseStart_71509 := by decide
  rcases family_descends (prefixWord ++ tailWord_71509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71522 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_71522 : Nat := 118140960795 + 71522 * 2 ^ 59
def prefixEnd_71522 : Nat := 4983230072969 + 3 ^ 40 * 71522 * 2
def baseEnd_71522 : Nat := 32644589663088358707629

theorem tailTrace_71522 : CollatzResearch.WordTrace tailWord_71522 prefixEnd_71522 32644589663088358707629 := by
  unfold tailWord_71522
  simp only [CollatzResearch.WordTrace]
  refine ⟨652155411723870957556205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1739081097930322553483213 652155411723870957556205)
  ·
    refine ⟨244558279396451609083577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 652155411723870957556205 244558279396451609083577)
    ·
      refine ⟨183418709547338706812683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244558279396451609083577 183418709547338706812683)
      ·
        refine ⟨275128064321008060219025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183418709547338706812683 275128064321008060219025)
        ·
          refine ⟨206346048240756045164269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275128064321008060219025 206346048240756045164269)
          ·
            refine ⟨77379768090283516936601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206346048240756045164269 77379768090283516936601)
            ·
              refine ⟨58034826067712637702451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77379768090283516936601 58034826067712637702451)
              ·
                refine ⟨87052239101568956553677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58034826067712637702451 87052239101568956553677)
                ·
                  refine ⟨32644589663088358707629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87052239101568956553677 32644589663088358707629)
                  ·
                    rfl

theorem cell20_71522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_71522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71522 prefixEnd_71522 := by exact prefixLift 71522
  have htrace : WordTrace (prefixWord ++ tailWord_71522) baseStart_71522 baseEnd_71522 := by
    simpa [prefixWord, tailWord_71522, baseEnd_71522] using wordTrace_append hprefix tailTrace_71522
  have hstable : (prefixWord ++ tailWord_71522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71522).length < 2 ^ (prefixWord ++ tailWord_71522).sum := by decide
  have hdescent : baseEnd_71522 < baseStart_71522 := by decide
  rcases family_descends (prefixWord ++ tailWord_71522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71578 : List Nat := [3, 1, 1, 4, 2, 1, 3, 5]
def baseStart_71578 : Nat := 118140960795 + 71578 * 2 ^ 59
def prefixEnd_71578 : Nat := 4983230072969 + 3 ^ 40 * 71578 * 2
def baseEnd_71578 : Nat := 10890049863000350946911

theorem tailTrace_71578 : CollatzResearch.WordTrace tailWord_71578 prefixEnd_71578 10890049863000350946911 := by
  unfold tailWord_71578
  simp only [CollatzResearch.WordTrace]
  refine ⟨652666033673151348565847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1740442756461736929508925 652666033673151348565847)
  ·
    refine ⟨978999050509727022848771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652666033673151348565847 978999050509727022848771)
    ·
      refine ⟨1468498575764590534273157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978999050509727022848771 1468498575764590534273157)
      ·
        refine ⟨275343482955860725176217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1468498575764590534273157 275343482955860725176217)
        ·
          refine ⟨206507612216895543882163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275343482955860725176217 206507612216895543882163)
          ·
            refine ⟨309761418325343315823245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206507612216895543882163 309761418325343315823245)
            ·
              refine ⟨116160531872003743433717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309761418325343315823245 116160531872003743433717)
              ·
                refine ⟨10890049863000350946911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116160531872003743433717 10890049863000350946911)
                ·
                  rfl

theorem cell20_71578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_71578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71578 prefixEnd_71578 := by exact prefixLift 71578
  have htrace : WordTrace (prefixWord ++ tailWord_71578) baseStart_71578 baseEnd_71578 := by
    simpa [prefixWord, tailWord_71578, baseEnd_71578] using wordTrace_append hprefix tailTrace_71578
  have hstable : (prefixWord ++ tailWord_71578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71578).length < 2 ^ (prefixWord ++ tailWord_71578).sum := by decide
  have hdescent : baseEnd_71578 < baseStart_71578 := by decide
  rcases family_descends (prefixWord ++ tailWord_71578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71640 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_71640 : Nat := 118140960795 + 71640 * 2 ^ 59
def prefixEnd_71640 : Nat := 4983230072969 + 3 ^ 40 * 71640 * 2
def baseEnd_71640 : Nat := 32698448078404392773813

theorem tailTrace_71640 : CollatzResearch.WordTrace tailWord_71640 prefixEnd_71640 32698448078404392773813 := by
  unfold tailWord_71640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306462730233994991510187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1741950306978659988680249 1306462730233994991510187)
  ·
    refine ⟨1959694095350992487265281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306462730233994991510187 1959694095350992487265281)
    ·
      refine ⟨1469770571513244365448961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1959694095350992487265281 1469770571513244365448961)
      ·
        refine ⟨1102327928634933274086721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1469770571513244365448961 1102327928634933274086721)
        ·
          refine ⟨826745946476199955565041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102327928634933274086721 826745946476199955565041)
          ·
            refine ⟨620059459857149966673781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826745946476199955565041 620059459857149966673781)
            ·
              refine ⟨58130574361607809375667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 620059459857149966673781 58130574361607809375667)
              ·
                refine ⟨87195861542411714063501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58130574361607809375667 87195861542411714063501)
                ·
                  refine ⟨32698448078404392773813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87195861542411714063501 32698448078404392773813)
                  ·
                    rfl

theorem cell20_71640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_71640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71640 prefixEnd_71640 := by exact prefixLift 71640
  have htrace : WordTrace (prefixWord ++ tailWord_71640) baseStart_71640 baseEnd_71640 := by
    simpa [prefixWord, tailWord_71640, baseEnd_71640] using wordTrace_append hprefix tailTrace_71640
  have hstable : (prefixWord ++ tailWord_71640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71640).length < 2 ^ (prefixWord ++ tailWord_71640).sum := by decide
  have hdescent : baseEnd_71640 < baseStart_71640 := by decide
  rcases family_descends (prefixWord ++ tailWord_71640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71678 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_71678 : Nat := 118140960795 + 71678 * 2 ^ 59
def prefixEnd_71678 : Nat := 4983230072969 + 3 ^ 40 * 71678 * 2
def baseEnd_71678 : Nat := 32715792313845149506991

theorem tailTrace_71678 : CollatzResearch.WordTrace tailWord_71678 prefixEnd_71678 32715792313845149506991 := by
  unfold tailWord_71678
  simp only [CollatzResearch.WordTrace]
  refine ⟨326788929291290309112961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1742874289553548315269125 326788929291290309112961)
  ·
    refine ⟨245091696968467731834721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 326788929291290309112961 245091696968467731834721)
    ·
      refine ⟨183818772726350798876041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245091696968467731834721 183818772726350798876041)
      ·
        refine ⟨137864079544763099157031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183818772726350798876041 137864079544763099157031)
        ·
          refine ⟨206796119317144648735547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137864079544763099157031 206796119317144648735547)
          ·
            refine ⟨310194178975716973103321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206796119317144648735547 310194178975716973103321)
            ·
              refine ⟨232645634231787729827491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310194178975716973103321 232645634231787729827491)
              ·
                refine ⟨348968451347681594741237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232645634231787729827491 348968451347681594741237)
                ·
                  refine ⟨32715792313845149506991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348968451347681594741237 32715792313845149506991)
                  ·
                    rfl

theorem cell20_71678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_71678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71678 prefixEnd_71678 := by exact prefixLift 71678
  have htrace : WordTrace (prefixWord ++ tailWord_71678) baseStart_71678 baseEnd_71678 := by
    simpa [prefixWord, tailWord_71678, baseEnd_71678] using wordTrace_append hprefix tailTrace_71678
  have hstable : (prefixWord ++ tailWord_71678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71678).length < 2 ^ (prefixWord ++ tailWord_71678).sum := by decide
  have hdescent : baseEnd_71678 < baseStart_71678 := by decide
  rcases family_descends (prefixWord ++ tailWord_71678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71685 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 4]
def baseStart_71685 : Nat := 118140960795 + 71685 * 2 ^ 59
def prefixEnd_71685 : Nat := 4983230072969 + 3 ^ 40 * 71685 * 2
def baseEnd_71685 : Nat := 32718987304584236273629

theorem tailTrace_71685 : CollatzResearch.WordTrace tailWord_71685 prefixEnd_71685 32718987304584236273629 := by
  unfold tailWord_71685
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614566745304962668408509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1743044496869975112272339 2614566745304962668408509)
  ·
    refine ⟨980462529489361000653191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2614566745304962668408509 980462529489361000653191)
    ·
      refine ⟨1470693794234041500979787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980462529489361000653191 1470693794234041500979787)
      ·
        refine ⟨2206040691351062251469681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470693794234041500979787 2206040691351062251469681)
        ·
          refine ⟨1654530518513296688602261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2206040691351062251469681 1654530518513296688602261)
          ·
            refine ⟨77556118055310782278231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1654530518513296688602261 77556118055310782278231)
            ·
              refine ⟨116334177082966173417347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77556118055310782278231 116334177082966173417347)
              ·
                refine ⟨174501265624449260126021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116334177082966173417347 174501265624449260126021)
                ·
                  refine ⟨32718987304584236273629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174501265624449260126021 32718987304584236273629)
                  ·
                    rfl

theorem cell20_71685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_71685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71685 prefixEnd_71685 := by exact prefixLift 71685
  have htrace : WordTrace (prefixWord ++ tailWord_71685) baseStart_71685 baseEnd_71685 := by
    simpa [prefixWord, tailWord_71685, baseEnd_71685] using wordTrace_append hprefix tailTrace_71685
  have hstable : (prefixWord ++ tailWord_71685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71685).length < 2 ^ (prefixWord ++ tailWord_71685).sum := by decide
  have hdescent : baseEnd_71685 < baseStart_71685 := by decide
  rcases family_descends (prefixWord ++ tailWord_71685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71727 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_71727 : Nat := 118140960795 + 71727 * 2 ^ 59
def prefixEnd_71727 : Nat := 4983230072969 + 3 ^ 40 * 71727 * 2
def baseEnd_71727 : Nat := 32738157249018756873457

theorem tailTrace_71727 : CollatzResearch.WordTrace tailWord_71727 prefixEnd_71727 32738157249018756873457 := by
  unfold tailWord_71727
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616098611152803841437435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1744065740768535894291623 2616098611152803841437435)
  ·
    refine ⟨3924147916729205762156153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2616098611152803841437435 3924147916729205762156153)
    ·
      refine ⟨2943110937546904321617115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3924147916729205762156153 2943110937546904321617115)
      ·
        refine ⟨4414666406320356482425673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943110937546904321617115 4414666406320356482425673)
        ·
          refine ⟨3310999804740267361819255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4414666406320356482425673 3310999804740267361819255)
          ·
            refine ⟨4966499707110401042728883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310999804740267361819255 4966499707110401042728883)
            ·
              refine ⟨7449749560665601564093325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966499707110401042728883 7449749560665601564093325)
              ·
                refine ⟨2793656085249600586534997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7449749560665601564093325 2793656085249600586534997)
                ·
                  refine ⟨32738157249018756873457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2793656085249600586534997 32738157249018756873457)
                  ·
                    rfl

theorem cell20_71727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_71727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71727 prefixEnd_71727 := by exact prefixLift 71727
  have htrace : WordTrace (prefixWord ++ tailWord_71727) baseStart_71727 baseEnd_71727 := by
    simpa [prefixWord, tailWord_71727, baseEnd_71727] using wordTrace_append hprefix tailTrace_71727
  have hstable : (prefixWord ++ tailWord_71727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71727).length < 2 ^ (prefixWord ++ tailWord_71727).sum := by decide
  have hdescent : baseEnd_71727 < baseStart_71727 := by decide
  rcases family_descends (prefixWord ++ tailWord_71727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71736 : List Nat := [2, 1, 2, 1, 7, 1, 2, 2, 2]
def baseStart_71736 : Nat := 118140960795 + 71736 * 2 ^ 59
def prefixEnd_71736 : Nat := 4983230072969 + 3 ^ 40 * 71736 * 2
def baseEnd_71736 : Nat := 32742265094254725573421

theorem tailTrace_71736 : CollatzResearch.WordTrace tailWord_71736 prefixEnd_71736 32742265094254725573421 := by
  unfold tailWord_71736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308213434060099189257531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1744284578746798919010041 1308213434060099189257531)
  ·
    refine ⟨1962320151090148783886297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1308213434060099189257531 1962320151090148783886297)
    ·
      refine ⟨1471740113317611587914723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1962320151090148783886297 1471740113317611587914723)
      ·
        refine ⟨2207610169976417381872085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471740113317611587914723 2207610169976417381872085)
        ·
          refine ⟨51740863358822282387627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2207610169976417381872085 51740863358822282387627)
          ·
            refine ⟨77611295038233423581441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51740863358822282387627 77611295038233423581441)
            ·
              refine ⟨58208471278675067686081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77611295038233423581441 58208471278675067686081)
              ·
                refine ⟨43656353459006300764561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58208471278675067686081 43656353459006300764561)
                ·
                  refine ⟨32742265094254725573421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43656353459006300764561 32742265094254725573421)
                  ·
                    rfl

theorem cell20_71736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_71736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71736 prefixEnd_71736 := by exact prefixLift 71736
  have htrace : WordTrace (prefixWord ++ tailWord_71736) baseStart_71736 baseEnd_71736 := by
    simpa [prefixWord, tailWord_71736, baseEnd_71736] using wordTrace_append hprefix tailTrace_71736
  have hstable : (prefixWord ++ tailWord_71736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71736).length < 2 ^ (prefixWord ++ tailWord_71736).sum := by decide
  have hdescent : baseEnd_71736 < baseStart_71736 := by decide
  rcases family_descends (prefixWord ++ tailWord_71736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71768 : List Nat := [2, 1, 2, 2, 1, 5, 3, 4]
def baseStart_71768 : Nat := 118140960795 + 71768 * 2 ^ 59
def prefixEnd_71768 : Nat := 4983230072969 + 3 ^ 40 * 71768 * 2
def baseEnd_71768 : Nat := 10918956922068278835541

theorem tailTrace_71768 : CollatzResearch.WordTrace tailWord_71768 prefixEnd_71768 10918956922068278835541 := by
  unfold tailWord_71768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308797002002133921839979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1745062669336178562453305 1308797002002133921839979)
  ·
    refine ⟨1963195503003200882759969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1308797002002133921839979 1963195503003200882759969)
    ·
      refine ⟨1472396627252400662069977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1963195503003200882759969 1472396627252400662069977)
      ·
        refine ⟨1104297470439300496552483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1472396627252400662069977 1104297470439300496552483)
        ·
          refine ⟨1656446205658950744828725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104297470439300496552483 1656446205658950744828725)
          ·
            refine ⟨155291831780526632327693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1656446205658950744828725 155291831780526632327693)
            ·
              refine ⟨58234436917697487122885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155291831780526632327693 58234436917697487122885)
              ·
                refine ⟨10918956922068278835541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58234436917697487122885 10918956922068278835541)
                ·
                  rfl

theorem cell20_71768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_71768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71768 prefixEnd_71768 := by exact prefixLift 71768
  have htrace : WordTrace (prefixWord ++ tailWord_71768) baseStart_71768 baseEnd_71768 := by
    simpa [prefixWord, tailWord_71768, baseEnd_71768] using wordTrace_append hprefix tailTrace_71768
  have hstable : (prefixWord ++ tailWord_71768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71768).length < 2 ^ (prefixWord ++ tailWord_71768).sum := by decide
  have hdescent : baseEnd_71768 < baseStart_71768 := by decide
  rcases family_descends (prefixWord ++ tailWord_71768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71789 : List Nat := [1, 5, 1, 1, 2, 1, 9]
def baseStart_71789 : Nat := 118140960795 + 71789 * 2 ^ 59
def prefixEnd_71789 : Nat := 4983230072969 + 3 ^ 40 * 71789 * 2
def baseEnd_71789 : Nat := 3640717304269121867393

theorem tailTrace_71789 : CollatzResearch.WordTrace tailWord_71789 prefixEnd_71789 3640717304269121867393 := by
  unfold tailWord_71789
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618359936928188430194421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1745573291285458953462947 2618359936928188430194421)
  ·
    refine ⟨245471244087017665330727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2618359936928188430194421 245471244087017665330727)
    ·
      refine ⟨368206866130526497996091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245471244087017665330727 368206866130526497996091)
      ·
        refine ⟨552310299195789746994137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368206866130526497996091 552310299195789746994137)
        ·
          refine ⟨414232724396842310245603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552310299195789746994137 414232724396842310245603)
          ·
            refine ⟨621349086595263465368405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414232724396842310245603 621349086595263465368405)
            ·
              refine ⟨3640717304269121867393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 621349086595263465368405 3640717304269121867393)
              ·
                rfl

theorem cell20_71789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_71789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71789 prefixEnd_71789 := by exact prefixLift 71789
  have htrace : WordTrace (prefixWord ++ tailWord_71789) baseStart_71789 baseEnd_71789 := by
    simpa [prefixWord, tailWord_71789, baseEnd_71789] using wordTrace_append hprefix tailTrace_71789
  have hstable : (prefixWord ++ tailWord_71789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71789).length < 2 ^ (prefixWord ++ tailWord_71789).sum := by decide
  have hdescent : baseEnd_71789 < baseStart_71789 := by decide
  rcases family_descends (prefixWord ++ tailWord_71789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71792 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_71792 : Nat := 118140960795 + 71792 * 2 ^ 59
def prefixEnd_71792 : Nat := 4983230072969 + 3 ^ 40 * 71792 * 2
def baseEnd_71792 : Nat := 32767825020167419706525

theorem tailTrace_71792 : CollatzResearch.WordTrace tailWord_71792 prefixEnd_71792 32767825020167419706525 := by
  unfold tailWord_71792
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309234677958659971276815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1745646237278213295035753 1309234677958659971276815)
  ·
    refine ⟨1963852016937989956915223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1309234677958659971276815 1963852016937989956915223)
    ·
      refine ⟨2945778025406984935372835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963852016937989956915223 2945778025406984935372835)
      ·
        refine ⟨4418667038110477403059253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945778025406984935372835 4418667038110477403059253)
        ·
          refine ⟨414250034822857256536805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4418667038110477403059253 414250034822857256536805)
          ·
            refine ⟨77671881529285735600651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 414250034822857256536805 77671881529285735600651)
            ·
              refine ⟨116507822293928603400977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77671881529285735600651 116507822293928603400977)
              ·
                refine ⟨87380866720446452550733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116507822293928603400977 87380866720446452550733)
                ·
                  refine ⟨32767825020167419706525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87380866720446452550733 32767825020167419706525)
                  ·
                    rfl

theorem cell20_71792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_71792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71792 prefixEnd_71792 := by exact prefixLift 71792
  have htrace : WordTrace (prefixWord ++ tailWord_71792) baseStart_71792 baseEnd_71792 := by
    simpa [prefixWord, tailWord_71792, baseEnd_71792] using wordTrace_append hprefix tailTrace_71792
  have hstable : (prefixWord ++ tailWord_71792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71792).length < 2 ^ (prefixWord ++ tailWord_71792).sum := by decide
  have hdescent : baseEnd_71792 < baseStart_71792 := by decide
  rcases family_descends (prefixWord ++ tailWord_71792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71799 : List Nat := [1, 1, 3, 1, 1, 5, 2, 4, 2]
def baseStart_71799 : Nat := 118140960795 + 71799 * 2 ^ 59
def prefixEnd_71799 : Nat := 4983230072969 + 3 ^ 40 * 71799 * 2
def baseEnd_71799 : Nat := 32771020010906506473163

theorem tailTrace_71799 : CollatzResearch.WordTrace tailWord_71799 prefixEnd_71799 32771020010906506473163 := by
  unfold tailWord_71799
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618724666891960138058451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1745816444594640092038967 2618724666891960138058451)
  ·
    refine ⟨3928087000337940207087677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2618724666891960138058451 3928087000337940207087677)
    ·
      refine ⟨1473032625126727577657879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3928087000337940207087677 1473032625126727577657879)
      ·
        refine ⟨2209548937690091366486819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473032625126727577657879 2209548937690091366486819)
        ·
          refine ⟨3314323406535137049730229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209548937690091366486819 3314323406535137049730229)
          ·
            refine ⟨310717819362669098412209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3314323406535137049730229 310717819362669098412209)
            ·
              refine ⟨233038364522001823809157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310717819362669098412209 233038364522001823809157)
              ·
                refine ⟨43694693347875341964217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233038364522001823809157 43694693347875341964217)
                ·
                  refine ⟨32771020010906506473163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43694693347875341964217 32771020010906506473163)
                  ·
                    rfl

theorem cell20_71799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 2].length) (baseStart_71799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71799 prefixEnd_71799 := by exact prefixLift 71799
  have htrace : WordTrace (prefixWord ++ tailWord_71799) baseStart_71799 baseEnd_71799 := by
    simpa [prefixWord, tailWord_71799, baseEnd_71799] using wordTrace_append hprefix tailTrace_71799
  have hstable : (prefixWord ++ tailWord_71799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71799).length < 2 ^ (prefixWord ++ tailWord_71799).sum := by decide
  have hdescent : baseEnd_71799 < baseStart_71799 := by decide
  rcases family_descends (prefixWord ++ tailWord_71799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71809 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 3]
def baseStart_71809 : Nat := 118140960795 + 71809 * 2 ^ 59
def prefixEnd_71809 : Nat := 4983230072969 + 3 ^ 40 * 71809 * 2
def baseEnd_71809 : Nat := 32775584283390916139789

theorem tailTrace_71809 : CollatzResearch.WordTrace tailWord_71809 prefixEnd_71809 32775584283390916139789 := by
  unfold tailWord_71809
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619089396855731845922481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1746059597903821230614987 2619089396855731845922481)
  ·
    refine ⟨1964317047641798884441861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2619089396855731845922481 1964317047641798884441861)
    ·
      refine ⟨368309446432837290832849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1964317047641798884441861 368309446432837290832849)
      ·
        refine ⟨276232084824627968124637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368309446432837290832849 276232084824627968124637)
        ·
          refine ⟨103587031809235488046739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276232084824627968124637 103587031809235488046739)
          ·
            refine ⟨155380547713853232070109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103587031809235488046739 155380547713853232070109)
            ·
              refine ⟨58267705392694962026291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155380547713853232070109 58267705392694962026291)
              ·
                refine ⟨87401558089042443039437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58267705392694962026291 87401558089042443039437)
                ·
                  refine ⟨32775584283390916139789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87401558089042443039437 32775584283390916139789)
                  ·
                    rfl

theorem cell20_71809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_71809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71809 prefixEnd_71809 := by exact prefixLift 71809
  have htrace : WordTrace (prefixWord ++ tailWord_71809) baseStart_71809 baseEnd_71809 := by
    simpa [prefixWord, tailWord_71809, baseEnd_71809] using wordTrace_append hprefix tailTrace_71809
  have hstable : (prefixWord ++ tailWord_71809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71809).length < 2 ^ (prefixWord ++ tailWord_71809).sum := by decide
  have hdescent : baseEnd_71809 < baseStart_71809 := by decide
  rcases family_descends (prefixWord ++ tailWord_71809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71844 : List Nat := [2, 3, 1, 2, 4, 2, 6]
def baseStart_71844 : Nat := 118140960795 + 71844 * 2 ^ 59
def prefixEnd_71844 : Nat := 4983230072969 + 3 ^ 40 * 71844 * 2
def baseEnd_71844 : Nat := 3643506581898483330331

theorem tailTrace_71844 : CollatzResearch.WordTrace tailWord_71844 prefixEnd_71844 3643506581898483330331 := by
  unfold tailWord_71844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310182975864466411723293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1746910634485955215631057 1310182975864466411723293)
  ·
    refine ⟨491318615949174904396235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1310182975864466411723293 491318615949174904396235)
    ·
      refine ⟨736977923923762356594353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491318615949174904396235 736977923923762356594353)
      ·
        refine ⟨552733442942821767445765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 736977923923762356594353 552733442942821767445765)
        ·
          refine ⟨103637520551779081396081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 552733442942821767445765 103637520551779081396081)
          ·
            refine ⟨77728140413834311047061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103637520551779081396081 77728140413834311047061)
            ·
              refine ⟨3643506581898483330331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77728140413834311047061 3643506581898483330331)
              ·
                rfl

theorem cell20_71844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 6].length) (baseStart_71844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71844 prefixEnd_71844 := by exact prefixLift 71844
  have htrace : WordTrace (prefixWord ++ tailWord_71844) baseStart_71844 baseEnd_71844 := by
    simpa [prefixWord, tailWord_71844, baseEnd_71844] using wordTrace_append hprefix tailTrace_71844
  have hstable : (prefixWord ++ tailWord_71844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71844).length < 2 ^ (prefixWord ++ tailWord_71844).sum := by decide
  have hdescent : baseEnd_71844 < baseStart_71844 := by decide
  rcases family_descends (prefixWord ++ tailWord_71844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71850 : List Nat := [3, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_71850 : Nat := 118140960795 + 71850 * 2 ^ 59
def prefixEnd_71850 : Nat := 4983230072969 + 3 ^ 40 * 71850 * 2
def baseEnd_71850 : Nat := 32794297800576995772955

theorem tailTrace_71850 : CollatzResearch.WordTrace tailWord_71850 prefixEnd_71850 32794297800576995772955 := by
  unfold tailWord_71850
  simp only [CollatzResearch.WordTrace]
  refine ⟨655146197426798962041251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1747056526471463898776669 655146197426798962041251)
  ·
    refine ⟨982719296140198443061877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655146197426798962041251 982719296140198443061877)
    ·
      refine ⟨92129934013143604037051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 982719296140198443061877 92129934013143604037051)
      ·
        refine ⟨138194901019715406055577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92129934013143604037051 138194901019715406055577)
        ·
          refine ⟨103646175764786554541683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138194901019715406055577 103646175764786554541683)
          ·
            refine ⟨155469263647179831812525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103646175764786554541683 155469263647179831812525)
            ·
              refine ⟨58300973867692436929697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155469263647179831812525 58300973867692436929697)
              ·
                refine ⟨43725730400769327697273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58300973867692436929697 43725730400769327697273)
                ·
                  refine ⟨32794297800576995772955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43725730400769327697273 32794297800576995772955)
                  ·
                    rfl

theorem cell20_71850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_71850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71850 prefixEnd_71850 := by exact prefixLift 71850
  have htrace : WordTrace (prefixWord ++ tailWord_71850) baseStart_71850 baseEnd_71850 := by
    simpa [prefixWord, tailWord_71850, baseEnd_71850] using wordTrace_append hprefix tailTrace_71850
  have hstable : (prefixWord ++ tailWord_71850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71850).length < 2 ^ (prefixWord ++ tailWord_71850).sum := by decide
  have hdescent : baseEnd_71850 < baseStart_71850 := by decide
  rcases family_descends (prefixWord ++ tailWord_71850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71860 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 3]
def baseStart_71860 : Nat := 118140960795 + 71860 * 2 ^ 59
def prefixEnd_71860 : Nat := 4983230072969 + 3 ^ 40 * 71860 * 2
def baseEnd_71860 : Nat := 32798862073061405439581

theorem tailTrace_71860 : CollatzResearch.WordTrace tailWord_71860 prefixEnd_71860 32798862073061405439581 := by
  unfold tailWord_71860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310474759835483778014517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1747299679780645037352689 1310474759835483778014517)
  ·
    refine ⟨122857008734576604188861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1310474759835483778014517 122857008734576604188861)
    ·
      refine ⟨46071378275466226570823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122857008734576604188861 46071378275466226570823)
      ·
        refine ⟨69107067413199339856235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46071378275466226570823 69107067413199339856235)
        ·
          refine ⟨103660601119799009784353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69107067413199339856235 103660601119799009784353)
          ·
            refine ⟨77745450839849257338265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103660601119799009784353 77745450839849257338265)
            ·
              refine ⟨58309088129886943003699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77745450839849257338265 58309088129886943003699)
              ·
                refine ⟨87463632194830414505549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58309088129886943003699 87463632194830414505549)
                ·
                  refine ⟨32798862073061405439581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87463632194830414505549 32798862073061405439581)
                  ·
                    rfl

theorem cell20_71860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_71860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71860 prefixEnd_71860 := by exact prefixLift 71860
  have htrace : WordTrace (prefixWord ++ tailWord_71860) baseStart_71860 baseEnd_71860 := by
    simpa [prefixWord, tailWord_71860, baseEnd_71860] using wordTrace_append hprefix tailTrace_71860
  have hstable : (prefixWord ++ tailWord_71860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71860).length < 2 ^ (prefixWord ++ tailWord_71860).sum := by decide
  have hdescent : baseEnd_71860 < baseStart_71860 := by decide
  rcases family_descends (prefixWord ++ tailWord_71860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71861 : List Nat := [1, 3, 3, 4, 1, 1, 2, 5]
def baseStart_71861 : Nat := 118140960795 + 71861 * 2 ^ 59
def prefixEnd_71861 : Nat := 4983230072969 + 3 ^ 40 * 71861 * 2
def baseEnd_71861 : Nat := 10933106166769948802081

theorem tailTrace_71861 : CollatzResearch.WordTrace tailWord_71861 prefixEnd_71861 10933106166769948802081 := by
  unfold tailWord_71861
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620985992667344726815437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1747323995111563151210291 2620985992667344726815437)
  ·
    refine ⟨982869747250254272555789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2620985992667344726815437 982869747250254272555789)
    ·
      refine ⟨368576155218845352208421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 982869747250254272555789 368576155218845352208421)
      ·
        refine ⟨69108029103533503539079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 368576155218845352208421 69108029103533503539079)
        ·
          refine ⟨103662043655300255308619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69108029103533503539079 103662043655300255308619)
          ·
            refine ⟨155493065482950382962929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103662043655300255308619 155493065482950382962929)
            ·
              refine ⟨116619799112212787222197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155493065482950382962929 116619799112212787222197)
              ·
                refine ⟨10933106166769948802081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116619799112212787222197 10933106166769948802081)
                ·
                  rfl

theorem cell20_71861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_71861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71861 prefixEnd_71861 := by exact prefixLift 71861
  have htrace : WordTrace (prefixWord ++ tailWord_71861) baseStart_71861 baseEnd_71861 := by
    simpa [prefixWord, tailWord_71861, baseEnd_71861] using wordTrace_append hprefix tailTrace_71861
  have hstable : (prefixWord ++ tailWord_71861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71861).length < 2 ^ (prefixWord ++ tailWord_71861).sum := by decide
  have hdescent : baseEnd_71861 < baseStart_71861 := by decide
  rcases family_descends (prefixWord ++ tailWord_71861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71865 : List Nat := [1, 2, 1, 4, 1, 2, 4, 5]
def baseStart_71865 : Nat := 118140960795 + 71865 * 2 ^ 59
def prefixEnd_71865 : Nat := 4983230072969 + 3 ^ 40 * 71865 * 2
def baseEnd_71865 : Nat := 10933714736434536757631

theorem tailTrace_71865 : CollatzResearch.WordTrace tailWord_71865 prefixEnd_71865 10933714736434536757631 := by
  unfold tailWord_71865
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621131884652853409961049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1747421256435235606640699 2621131884652853409961049)
  ·
    refine ⟨1965848913489640057470787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2621131884652853409961049 1965848913489640057470787)
    ·
      refine ⟨2948773370234460086206181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965848913489640057470787 2948773370234460086206181)
      ·
        refine ⟨552895006918961266163659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2948773370234460086206181 552895006918961266163659)
        ·
          refine ⟨829342510378441899245489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552895006918961266163659 829342510378441899245489)
          ·
            refine ⟨622006882783831424434117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829342510378441899245489 622006882783831424434117)
            ·
              refine ⟨116626290521968392081397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 622006882783831424434117 116626290521968392081397)
              ·
                refine ⟨10933714736434536757631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116626290521968392081397 10933714736434536757631)
                ·
                  rfl

theorem cell20_71865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_71865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71865 prefixEnd_71865 := by exact prefixLift 71865
  have htrace : WordTrace (prefixWord ++ tailWord_71865) baseStart_71865 baseEnd_71865 := by
    simpa [prefixWord, tailWord_71865, baseEnd_71865] using wordTrace_append hprefix tailTrace_71865
  have hstable : (prefixWord ++ tailWord_71865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71865).length < 2 ^ (prefixWord ++ tailWord_71865).sum := by decide
  have hdescent : baseEnd_71865 < baseStart_71865 := by decide
  rcases family_descends (prefixWord ++ tailWord_71865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71868 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_71868 : Nat := 118140960795 + 71868 * 2 ^ 59
def prefixEnd_71868 : Nat := 4983230072969 + 3 ^ 40 * 71868 * 2
def baseEnd_71868 : Nat := 32802513491048933172881

theorem tailTrace_71868 : CollatzResearch.WordTrace tailWord_71868 prefixEnd_71868 32802513491048933172881 := by
  unfold tailWord_71868
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310620651820992461160129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1747494202427989948213505 1310620651820992461160129)
  ·
    refine ⟨982965488865744345870097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1310620651820992461160129 982965488865744345870097)
    ·
      refine ⟨737224116649308259402573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 982965488865744345870097 737224116649308259402573)
      ·
        refine ⟨276459043743490597275965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 737224116649308259402573 276459043743490597275965)
        ·
          refine ⟨103672141403808973978487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276459043743490597275965 103672141403808973978487)
          ·
            refine ⟨155508212105713460967731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103672141403808973978487 155508212105713460967731)
            ·
              refine ⟨233262318158570191451597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155508212105713460967731 233262318158570191451597)
              ·
                refine ⟨87473369309463821794349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233262318158570191451597 87473369309463821794349)
                ·
                  refine ⟨32802513491048933172881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87473369309463821794349 32802513491048933172881)
                  ·
                    rfl

theorem cell20_71868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_71868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71868 prefixEnd_71868 := by exact prefixLift 71868
  have htrace : WordTrace (prefixWord ++ tailWord_71868) baseStart_71868 baseEnd_71868 := by
    simpa [prefixWord, tailWord_71868, baseEnd_71868] using wordTrace_append hprefix tailTrace_71868
  have hstable : (prefixWord ++ tailWord_71868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71868).length < 2 ^ (prefixWord ++ tailWord_71868).sum := by decide
  have hdescent : baseEnd_71868 < baseStart_71868 := by decide
  rcases family_descends (prefixWord ++ tailWord_71868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71909 : List Nat := [1, 3, 1, 4, 2, 3, 2, 2, 2]
def baseStart_71909 : Nat := 118140960795 + 71909 * 2 ^ 59
def prefixEnd_71909 : Nat := 4983230072969 + 3 ^ 40 * 71909 * 2
def baseEnd_71909 : Nat := 32821227008235012806047

theorem tailTrace_71909 : CollatzResearch.WordTrace tailWord_71909 prefixEnd_71909 32821227008235012806047 := by
  unfold tailWord_71909
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622736696493448924562781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1748491130995632616375187 2622736696493448924562781)
  ·
    refine ⟨983526261185043346711043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2622736696493448924562781 983526261185043346711043)
    ·
      refine ⟨1475289391777565020066565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983526261185043346711043 1475289391777565020066565)
      ·
        refine ⟨276616760958293441262481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1475289391777565020066565 276616760958293441262481)
        ·
          refine ⟨207462570718720080946861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276616760958293441262481 207462570718720080946861)
          ·
            refine ⟨77798464019520030355073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207462570718720080946861 77798464019520030355073)
            ·
              refine ⟨58348848014640022766305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77798464019520030355073 58348848014640022766305)
              ·
                refine ⟨43761636010980017074729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58348848014640022766305 43761636010980017074729)
                ·
                  refine ⟨32821227008235012806047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43761636010980017074729 32821227008235012806047)
                  ·
                    rfl

theorem cell20_71909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_71909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71909 prefixEnd_71909 := by exact prefixLift 71909
  have htrace : WordTrace (prefixWord ++ tailWord_71909) baseStart_71909 baseEnd_71909 := by
    simpa [prefixWord, tailWord_71909, baseEnd_71909] using wordTrace_append hprefix tailTrace_71909
  have hstable : (prefixWord ++ tailWord_71909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71909).length < 2 ^ (prefixWord ++ tailWord_71909).sum := by decide
  have hdescent : baseEnd_71909 < baseStart_71909 := by decide
  rcases family_descends (prefixWord ++ tailWord_71909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71948 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_71948 : Nat := 118140960795 + 71948 * 2 ^ 59
def prefixEnd_71948 : Nat := 4983230072969 + 3 ^ 40 * 71948 * 2
def baseEnd_71948 : Nat := 32839027670924210505887

theorem tailTrace_71948 : CollatzResearch.WordTrace tailWord_71948 prefixEnd_71948 32839027670924210505887 := by
  unfold tailWord_71948
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312079571676079292616249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1749439428901439056821665 1312079571676079292616249)
  ·
    refine ⟨984059678757059469462187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1312079571676079292616249 984059678757059469462187)
    ·
      refine ⟨1476089518135589204193281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984059678757059469462187 1476089518135589204193281)
      ·
        refine ⟨1107067138601691903144961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1476089518135589204193281 1107067138601691903144961)
        ·
          refine ⟨830300353951268927358721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1107067138601691903144961 830300353951268927358721)
          ·
            refine ⟨622725265463451695519041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830300353951268927358721 622725265463451695519041)
            ·
              refine ⟨467043949097588771639281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622725265463451695519041 467043949097588771639281)
              ·
                refine ⟨350282961823191578729461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467043949097588771639281 350282961823191578729461)
                ·
                  refine ⟨32839027670924210505887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 350282961823191578729461 32839027670924210505887)
                  ·
                    rfl

theorem cell20_71948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_71948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71948 prefixEnd_71948 := by exact prefixLift 71948
  have htrace : WordTrace (prefixWord ++ tailWord_71948) baseStart_71948 baseEnd_71948 := by
    simpa [prefixWord, tailWord_71948, baseEnd_71948] using wordTrace_append hprefix tailTrace_71948
  have hstable : (prefixWord ++ tailWord_71948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71948).length < 2 ^ (prefixWord ++ tailWord_71948).sum := by decide
  have hdescent : baseEnd_71948 < baseStart_71948 := by decide
  rcases family_descends (prefixWord ++ tailWord_71948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71972 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_71972 : Nat := 118140960795 + 71972 * 2 ^ 59
def prefixEnd_71972 : Nat := 4983230072969 + 3 ^ 40 * 71972 * 2
def baseEnd_71972 : Nat := 32849981924886793705789

theorem tailTrace_71972 : CollatzResearch.WordTrace tailWord_71972 prefixEnd_71972 32849981924886793705789 := by
  unfold tailWord_71972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312517247632605342053085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1750022996843473789404113 1312517247632605342053085)
  ·
    refine ⟨492193967862227003269907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1312517247632605342053085 492193967862227003269907)
    ·
      refine ⟨738290951793340504904861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492193967862227003269907 738290951793340504904861)
      ·
        refine ⟨276859106922502689339323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 738290951793340504904861 276859106922502689339323)
        ·
          refine ⟨415288660383754034008985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276859106922502689339323 415288660383754034008985)
          ·
            refine ⟨311466495287815525506739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415288660383754034008985 311466495287815525506739)
            ·
              refine ⟨467199742931723288260109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311466495287815525506739 467199742931723288260109)
              ·
                refine ⟨175199903599396233097541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 467199742931723288260109 175199903599396233097541)
                ·
                  refine ⟨32849981924886793705789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175199903599396233097541 32849981924886793705789)
                  ·
                    rfl

theorem cell20_71972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_71972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_71972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_71972 prefixEnd_71972 := by exact prefixLift 71972
  have htrace : WordTrace (prefixWord ++ tailWord_71972) baseStart_71972 baseEnd_71972 := by
    simpa [prefixWord, tailWord_71972, baseEnd_71972] using wordTrace_append hprefix tailTrace_71972
  have hstable : (prefixWord ++ tailWord_71972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71972).length < 2 ^ (prefixWord ++ tailWord_71972).sum := by decide
  have hdescent : baseEnd_71972 < baseStart_71972 := by decide
  rcases family_descends (prefixWord ++ tailWord_71972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72017 : List Nat := [1, 2, 2, 1, 4, 4, 6]
def baseStart_72017 : Nat := 118140960795 + 72017 * 2 ^ 59
def prefixEnd_72017 : Nat := 4983230072969 + 3 ^ 40 * 72017 * 2
def baseEnd_72017 : Nat := 3652280127896293022845

theorem tailTrace_72017 : CollatzResearch.WordTrace tailWord_72017 prefixEnd_72017 3652280127896293022845 := by
  unfold tailWord_72017
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626675780102183369494305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1751117186734788912996203 2626675780102183369494305)
  ·
    refine ⟨1970006835076637527120729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2626675780102183369494305 1970006835076637527120729)
    ·
      refine ⟨1477505126307478145340547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1970006835076637527120729 1477505126307478145340547)
      ·
        refine ⟨2216257689461217218010821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477505126307478145340547 2216257689461217218010821)
        ·
          refine ⟨415548316773978228377029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2216257689461217218010821 415548316773978228377029)
          ·
            refine ⟨77915309395120917820693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 415548316773978228377029 77915309395120917820693)
            ·
              refine ⟨3652280127896293022845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77915309395120917820693 3652280127896293022845)
              ·
                rfl

theorem cell20_72017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 6].length) (baseStart_72017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72017 prefixEnd_72017 := by exact prefixLift 72017
  have htrace : WordTrace (prefixWord ++ tailWord_72017) baseStart_72017 baseEnd_72017 := by
    simpa [prefixWord, tailWord_72017, baseEnd_72017] using wordTrace_append hprefix tailTrace_72017
  have hstable : (prefixWord ++ tailWord_72017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72017).length < 2 ^ (prefixWord ++ tailWord_72017).sum := by decide
  have hdescent : baseEnd_72017 < baseStart_72017 := by decide
  rcases family_descends (prefixWord ++ tailWord_72017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72034 : List Nat := [3, 3, 2, 1, 1, 3, 2, 5]
def baseStart_72034 : Nat := 118140960795 + 72034 * 2 ^ 59
def prefixEnd_72034 : Nat := 4983230072969 + 3 ^ 40 * 72034 * 2
def baseEnd_72034 : Nat := 10959426804763377879623

theorem tailTrace_72034 : CollatzResearch.WordTrace tailWord_72034 prefixEnd_72034 10959426804763377879623 := by
  unfold tailWord_72034
  simp only [CollatzResearch.WordTrace]
  refine ⟨656823955260148818215789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1751530547360396848575437 656823955260148818215789)
  ·
    refine ⟨246308983222555806830921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 656823955260148818215789 246308983222555806830921)
    ·
      refine ⟨184731737416916855123191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246308983222555806830921 184731737416916855123191)
      ·
        refine ⟨277097606125375282684787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184731737416916855123191 277097606125375282684787)
        ·
          refine ⟨415646409188062924027181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277097606125375282684787 415646409188062924027181)
          ·
            refine ⟨155867403445523596510193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 415646409188062924027181 155867403445523596510193)
            ·
              refine ⟨116900552584142697382645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155867403445523596510193 116900552584142697382645)
              ·
                refine ⟨10959426804763377879623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116900552584142697382645 10959426804763377879623)
                ·
                  rfl

theorem cell20_72034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_72034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72034 prefixEnd_72034 := by exact prefixLift 72034
  have htrace : WordTrace (prefixWord ++ tailWord_72034) baseStart_72034 baseEnd_72034 := by
    simpa [prefixWord, tailWord_72034, baseEnd_72034] using wordTrace_append hprefix tailTrace_72034
  have hstable : (prefixWord ++ tailWord_72034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72034).length < 2 ^ (prefixWord ++ tailWord_72034).sum := by decide
  have hdescent : baseEnd_72034 < baseStart_72034 := by decide
  rcases family_descends (prefixWord ++ tailWord_72034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72076 : List Nat := [2, 2, 1, 2, 1, 12]
def baseStart_72076 : Nat := 118140960795 + 72076 * 2 ^ 59
def prefixEnd_72076 : Nat := 4983230072969 + 3 ^ 40 * 72076 * 2
def baseEnd_72076 : Nat := 1218424087360172379211

theorem tailTrace_72076 : CollatzResearch.WordTrace tailWord_72076 prefixEnd_72076 1218424087360172379211 := by
  unfold tailWord_72076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314413843444218222946041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1752551791258957630594721 1314413843444218222946041)
  ·
    refine ⟨985810382583163667209531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1314413843444218222946041 985810382583163667209531)
    ·
      refine ⟨1478715573874745500814297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985810382583163667209531 1478715573874745500814297)
      ·
        refine ⟨1109036680406059125610723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1478715573874745500814297 1109036680406059125610723)
        ·
          refine ⟨1663555020609088688416085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109036680406059125610723 1663555020609088688416085)
          ·
            refine ⟨1218424087360172379211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1663555020609088688416085 1218424087360172379211)
            ·
              rfl

theorem cell20_72076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 12].length) (baseStart_72076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72076 prefixEnd_72076 := by exact prefixLift 72076
  have htrace : WordTrace (prefixWord ++ tailWord_72076) baseStart_72076 baseEnd_72076 := by
    simpa [prefixWord, tailWord_72076, baseEnd_72076] using wordTrace_append hprefix tailTrace_72076
  have hstable : (prefixWord ++ tailWord_72076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72076).length < 2 ^ (prefixWord ++ tailWord_72076).sum := by decide
  have hdescent : baseEnd_72076 < baseStart_72076 := by decide
  rcases family_descends (prefixWord ++ tailWord_72076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72116 : List Nat := [2, 5, 2, 2, 1, 1, 2, 3, 2]
def baseStart_72116 : Nat := 118140960795 + 72116 * 2 ^ 59
def prefixEnd_72116 : Nat := 4983230072969 + 3 ^ 40 * 72116 * 2
def baseEnd_72116 : Nat := 32915707448662292905201

theorem tailTrace_72116 : CollatzResearch.WordTrace tailWord_72116 prefixEnd_72116 32915707448662292905201 := by
  unfold tailWord_72116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315143303371761638674101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1753524404495682184898801 1315143303371761638674101)
  ·
    refine ⟨123294684691102653625697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1315143303371761638674101 123294684691102653625697)
    ·
      refine ⟨92471013518326990219273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123294684691102653625697 92471013518326990219273)
      ·
        refine ⟨69353260138745242664455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92471013518326990219273 69353260138745242664455)
        ·
          refine ⟨104029890208117863996683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69353260138745242664455 104029890208117863996683)
          ·
            refine ⟨156044835312176795995025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104029890208117863996683 156044835312176795995025)
            ·
              refine ⟨117033626484132596996269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156044835312176795995025 117033626484132596996269)
              ·
                refine ⟨43887609931549723873601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117033626484132596996269 43887609931549723873601)
                ·
                  refine ⟨32915707448662292905201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43887609931549723873601 32915707448662292905201)
                  ·
                    rfl

theorem cell20_72116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_72116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72116 prefixEnd_72116 := by exact prefixLift 72116
  have htrace : WordTrace (prefixWord ++ tailWord_72116) baseStart_72116 baseEnd_72116 := by
    simpa [prefixWord, tailWord_72116, baseEnd_72116] using wordTrace_append hprefix tailTrace_72116
  have hstable : (prefixWord ++ tailWord_72116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72116).length < 2 ^ (prefixWord ++ tailWord_72116).sum := by decide
  have hdescent : baseEnd_72116 < baseStart_72116 := by decide
  rcases family_descends (prefixWord ++ tailWord_72116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72138 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_72138 : Nat := 118140960795 + 72138 * 2 ^ 59
def prefixEnd_72138 : Nat := 4983230072969 + 3 ^ 40 * 72138 * 2
def baseEnd_72138 : Nat := 32925748848127994171777

theorem tailTrace_72138 : CollatzResearch.WordTrace tailWord_72138 prefixEnd_72138 32925748848127994171777 := by
  unfold tailWord_72138
  simp only [CollatzResearch.WordTrace]
  refine ⟨657772253165955258662267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1754059341775880689766045 657772253165955258662267)
  ·
    refine ⟨986658379748932887993401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 657772253165955258662267 986658379748932887993401)
    ·
      refine ⟨739993784811699665995051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 986658379748932887993401 739993784811699665995051)
      ·
        refine ⟨1109990677217549498992577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739993784811699665995051 1109990677217549498992577)
        ·
          refine ⟨832493007913162124244433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109990677217549498992577 832493007913162124244433)
          ·
            refine ⟨624369755934871593183325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832493007913162124244433 624369755934871593183325)
            ·
              refine ⟨234138658475576847443747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 624369755934871593183325 234138658475576847443747)
              ·
                refine ⟨351207987713365271165621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234138658475576847443747 351207987713365271165621)
                ·
                  refine ⟨32925748848127994171777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351207987713365271165621 32925748848127994171777)
                  ·
                    rfl

theorem cell20_72138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_72138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72138 prefixEnd_72138 := by exact prefixLift 72138
  have htrace : WordTrace (prefixWord ++ tailWord_72138) baseStart_72138 baseEnd_72138 := by
    simpa [prefixWord, tailWord_72138, baseEnd_72138] using wordTrace_append hprefix tailTrace_72138
  have hstable : (prefixWord ++ tailWord_72138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72138).length < 2 ^ (prefixWord ++ tailWord_72138).sum := by decide
  have hdescent : baseEnd_72138 < baseStart_72138 := by decide
  rcases family_descends (prefixWord ++ tailWord_72138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72152 : List Nat := [2, 1, 2, 2, 2, 1, 1, 9]
def baseStart_72152 : Nat := 118140960795 + 72152 * 2 ^ 59
def prefixEnd_72152 : Nat := 4983230072969 + 3 ^ 40 * 72152 * 2
def baseEnd_72152 : Nat := 10977379609868722568351

theorem tailTrace_72152 : CollatzResearch.WordTrace tailWord_72152 prefixEnd_72152 10977379609868722568351 := by
  unfold tailWord_72152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315799817306550712829355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1754399756408734283772473 1315799817306550712829355)
  ·
    refine ⟨1973699725959826069244033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1315799817306550712829355 1973699725959826069244033)
    ·
      refine ⟨1480274794469869551933025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1973699725959826069244033 1480274794469869551933025)
      ·
        refine ⟨1110206095852402163949769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1480274794469869551933025 1110206095852402163949769)
        ·
          refine ⟨832654571889301622962327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110206095852402163949769 832654571889301622962327)
          ·
            refine ⟨1248981857833952434443491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832654571889301622962327 1248981857833952434443491)
            ·
              refine ⟨1873472786750928651665237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248981857833952434443491 1873472786750928651665237)
              ·
                refine ⟨10977379609868722568351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1873472786750928651665237 10977379609868722568351)
                ·
                  rfl

theorem cell20_72152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_72152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72152 prefixEnd_72152 := by exact prefixLift 72152
  have htrace : WordTrace (prefixWord ++ tailWord_72152) baseStart_72152 baseEnd_72152 := by
    simpa [prefixWord, tailWord_72152, baseEnd_72152] using wordTrace_append hprefix tailTrace_72152
  have hstable : (prefixWord ++ tailWord_72152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72152).length < 2 ^ (prefixWord ++ tailWord_72152).sum := by decide
  have hdescent : baseEnd_72152 < baseStart_72152 := by decide
  rcases family_descends (prefixWord ++ tailWord_72152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72165 : List Nat := [1, 3, 1, 5, 2, 2, 2, 4]
def baseStart_72165 : Nat := 118140960795 + 72165 * 2 ^ 59
def prefixEnd_72165 : Nat := 4983230072969 + 3 ^ 40 * 72165 * 2
def baseEnd_72165 : Nat := 10979357461278633423889

theorem tailTrace_72165 : CollatzResearch.WordTrace tailWord_72165 prefixEnd_72165 10979357461278633423889 := by
  unfold tailWord_72165
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632073783566004645881949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1754715855710669763921299 2632073783566004645881949)
  ·
    refine ⟨987027668837251742205731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2632073783566004645881949 987027668837251742205731)
    ·
      refine ⟨1480541503255877613308597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 987027668837251742205731 1480541503255877613308597)
      ·
        refine ⟨138800765930238526247681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1480541503255877613308597 138800765930238526247681)
        ·
          refine ⟨104100574447678894685761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138800765930238526247681 104100574447678894685761)
          ·
            refine ⟨78075430835759171014321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104100574447678894685761 78075430835759171014321)
            ·
              refine ⟨58556573126819378260741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78075430835759171014321 58556573126819378260741)
              ·
                refine ⟨10979357461278633423889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58556573126819378260741 10979357461278633423889)
                ·
                  rfl

theorem cell20_72165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_72165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72165 prefixEnd_72165 := by exact prefixLift 72165
  have htrace : WordTrace (prefixWord ++ tailWord_72165) baseStart_72165 baseEnd_72165 := by
    simpa [prefixWord, tailWord_72165, baseEnd_72165] using wordTrace_append hprefix tailTrace_72165
  have hstable : (prefixWord ++ tailWord_72165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72165).length < 2 ^ (prefixWord ++ tailWord_72165).sum := by decide
  have hdescent : baseEnd_72165 < baseStart_72165 := by decide
  rcases family_descends (prefixWord ++ tailWord_72165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72235 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_72235 : Nat := 118140960795 + 72235 * 2 ^ 59
def prefixEnd_72235 : Nat := 4983230072969 + 3 ^ 40 * 72235 * 2
def baseEnd_72235 : Nat := 32970022291226767938047

theorem tailTrace_72235 : CollatzResearch.WordTrace tailWord_72235 prefixEnd_72235 32970022291226767938047 := by
  unfold tailWord_72235
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634626893312406600930159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1756417928874937733953439 2634626893312406600930159)
  ·
    refine ⟨3951940339968609901395239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2634626893312406600930159 3951940339968609901395239)
    ·
      refine ⟨5927910509952914852092859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3951940339968609901395239 5927910509952914852092859)
      ·
        refine ⟨8891865764929372278139289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5927910509952914852092859 8891865764929372278139289)
        ·
          refine ⟨6668899323697029208604467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8891865764929372278139289 6668899323697029208604467)
          ·
            refine ⟨10003348985545543812906701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6668899323697029208604467 10003348985545543812906701)
            ·
              refine ⟨3751255869579578929840013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10003348985545543812906701 3751255869579578929840013)
              ·
                refine ⟨1406720951092342098690005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3751255869579578929840013 1406720951092342098690005)
                ·
                  refine ⟨32970022291226767938047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1406720951092342098690005 32970022291226767938047)
                  ·
                    rfl

theorem cell20_72235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_72235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72235 prefixEnd_72235 := by exact prefixLift 72235
  have htrace : WordTrace (prefixWord ++ tailWord_72235) baseStart_72235 baseEnd_72235 := by
    simpa [prefixWord, tailWord_72235, baseEnd_72235] using wordTrace_append hprefix tailTrace_72235
  have hstable : (prefixWord ++ tailWord_72235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72235).length < 2 ^ (prefixWord ++ tailWord_72235).sum := by decide
  have hdescent : baseEnd_72235 < baseStart_72235 := by decide
  rcases family_descends (prefixWord ++ tailWord_72235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72276 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_72276 : Nat := 118140960795 + 72276 * 2 ^ 59
def prefixEnd_72276 : Nat := 4983230072969 + 3 ^ 40 * 72276 * 2
def baseEnd_72276 : Nat := 32988735808412847571213

theorem tailTrace_72276 : CollatzResearch.WordTrace tailWord_72276 prefixEnd_72276 32988735808412847571213 := by
  unfold tailWord_72276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318061143081935301586341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1757414857442580402115121 1318061143081935301586341)
  ·
    refine ⟨247136464327862869047439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1318061143081935301586341 247136464327862869047439)
    ·
      refine ⟨370704696491794303571159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247136464327862869047439 370704696491794303571159)
      ·
        refine ⟨556057044737691455356739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370704696491794303571159 556057044737691455356739)
        ·
          refine ⟨834085567106537183035109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556057044737691455356739 834085567106537183035109)
          ·
            refine ⟨156391043832475721819083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 834085567106537183035109 156391043832475721819083)
            ·
              refine ⟨234586565748713582728625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156391043832475721819083 234586565748713582728625)
              ·
                refine ⟨175939924311535187046469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234586565748713582728625 175939924311535187046469)
                ·
                  refine ⟨32988735808412847571213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175939924311535187046469 32988735808412847571213)
                  ·
                    rfl

theorem cell20_72276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_72276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72276 prefixEnd_72276 := by exact prefixLift 72276
  have htrace : WordTrace (prefixWord ++ tailWord_72276) baseStart_72276 baseEnd_72276 := by
    simpa [prefixWord, tailWord_72276, baseEnd_72276] using wordTrace_append hprefix tailTrace_72276
  have hstable : (prefixWord ++ tailWord_72276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72276).length < 2 ^ (prefixWord ++ tailWord_72276).sum := by decide
  have hdescent : baseEnd_72276 < baseStart_72276 := by decide
  rcases family_descends (prefixWord ++ tailWord_72276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72324 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_72324 : Nat := 118140960795 + 72324 * 2 ^ 59
def prefixEnd_72324 : Nat := 4983230072969 + 3 ^ 40 * 72324 * 2
def baseEnd_72324 : Nat := 33010644316338013971017

theorem tailTrace_72324 : CollatzResearch.WordTrace tailWord_72324 prefixEnd_72324 33010644316338013971017 := by
  unfold tailWord_72324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318936494994987400460013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1758581993326649867280017 1318936494994987400460013)
  ·
    refine ⟨494601185623120275172505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1318936494994987400460013 494601185623120275172505)
    ·
      refine ⟨370950889217340206379379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 494601185623120275172505 370950889217340206379379)
      ·
        refine ⟨556426333826010309569069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370950889217340206379379 556426333826010309569069)
        ·
          refine ⟨208659875184753866088401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 556426333826010309569069 208659875184753866088401)
          ·
            refine ⟨156494906388565399566301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208659875184753866088401 156494906388565399566301)
            ·
              refine ⟨58685589895712024837363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156494906388565399566301 58685589895712024837363)
              ·
                refine ⟨88028384843568037256045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58685589895712024837363 88028384843568037256045)
                ·
                  refine ⟨33010644316338013971017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88028384843568037256045 33010644316338013971017)
                  ·
                    rfl

theorem cell20_72324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_72324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72324 prefixEnd_72324 := by exact prefixLift 72324
  have htrace : WordTrace (prefixWord ++ tailWord_72324) baseStart_72324 baseEnd_72324 := by
    simpa [prefixWord, tailWord_72324, baseEnd_72324] using wordTrace_append hprefix tailTrace_72324
  have hstable : (prefixWord ++ tailWord_72324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72324).length < 2 ^ (prefixWord ++ tailWord_72324).sum := by decide
  have hdescent : baseEnd_72324 < baseStart_72324 := by decide
  rcases family_descends (prefixWord ++ tailWord_72324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72338 : List Nat := [3, 2, 3, 1, 2, 1, 4, 4]
def baseStart_72338 : Nat := 118140960795 + 72338 * 2 ^ 59
def prefixEnd_72338 : Nat := 4983230072969 + 3 ^ 40 * 72338 * 2
def baseEnd_72338 : Nat := 11005678099272062501431

theorem tailTrace_72338 : CollatzResearch.WordTrace tailWord_72338 prefixEnd_72338 11005678099272062501431 := by
  unfold tailWord_72338
  simp only [CollatzResearch.WordTrace]
  refine ⟨659595902984813797982417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1758922407959503461286445 659595902984813797982417)
  ·
    refine ⟨494696927238610348486813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 659595902984813797982417 494696927238610348486813)
    ·
      refine ⟨185511347714478880682555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 494696927238610348486813 185511347714478880682555)
      ·
        refine ⟨278267021571718321023833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185511347714478880682555 278267021571718321023833)
        ·
          refine ⟨208700266178788740767875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278267021571718321023833 208700266178788740767875)
          ·
            refine ⟨313050399268183111151813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208700266178788740767875 313050399268183111151813)
            ·
              refine ⟨58696949862784333340965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 313050399268183111151813 58696949862784333340965)
              ·
                refine ⟨11005678099272062501431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58696949862784333340965 11005678099272062501431)
                ·
                  rfl

theorem cell20_72338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_72338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72338 prefixEnd_72338 := by exact prefixLift 72338
  have htrace : WordTrace (prefixWord ++ tailWord_72338) baseStart_72338 baseEnd_72338 := by
    simpa [prefixWord, tailWord_72338, baseEnd_72338] using wordTrace_append hprefix tailTrace_72338
  have hstable : (prefixWord ++ tailWord_72338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72338).length < 2 ^ (prefixWord ++ tailWord_72338).sum := by decide
  have hdescent : baseEnd_72338 < baseStart_72338 := by decide
  rcases family_descends (prefixWord ++ tailWord_72338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72348 : List Nat := [2, 2, 3, 2, 2, 3, 1, 3, 2]
def baseStart_72348 : Nat := 118140960795 + 72348 * 2 ^ 59
def prefixEnd_72348 : Nat := 4983230072969 + 3 ^ 40 * 72348 * 2
def baseEnd_72348 : Nat := 33021598570300597170919

theorem tailTrace_72348 : CollatzResearch.WordTrace tailWord_72348 prefixEnd_72348 33021598570300597170919 := by
  unfold tailWord_72348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319374170951513449896849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1759165561268684599862465 1319374170951513449896849)
  ·
    refine ⟨989530628213635087422637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1319374170951513449896849 989530628213635087422637)
    ·
      refine ⟨371073985580113157783489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 989530628213635087422637 371073985580113157783489)
      ·
        refine ⟨278305489185084868337617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371073985580113157783489 278305489185084868337617)
        ·
          refine ⟨208729116888813651253213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278305489185084868337617 208729116888813651253213)
          ·
            refine ⟨78273418833305119219955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208729116888813651253213 78273418833305119219955)
            ·
              refine ⟨117410128249957678829933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78273418833305119219955 117410128249957678829933)
              ·
                refine ⟨44028798093734129561225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117410128249957678829933 44028798093734129561225)
                ·
                  refine ⟨33021598570300597170919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44028798093734129561225 33021598570300597170919)
                  ·
                    rfl

theorem cell20_72348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_72348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72348 prefixEnd_72348 := by exact prefixLift 72348
  have htrace : WordTrace (prefixWord ++ tailWord_72348) baseStart_72348 baseEnd_72348 := by
    simpa [prefixWord, tailWord_72348, baseEnd_72348] using wordTrace_append hprefix tailTrace_72348
  have hstable : (prefixWord ++ tailWord_72348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72348).length < 2 ^ (prefixWord ++ tailWord_72348).sum := by decide
  have hdescent : baseEnd_72348 < baseStart_72348 := by decide
  rcases family_descends (prefixWord ++ tailWord_72348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72383 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 3]
def baseStart_72383 : Nat := 118140960795 + 72383 * 2 ^ 59
def prefixEnd_72383 : Nat := 4983230072969 + 3 ^ 40 * 72383 * 2
def baseEnd_72383 : Nat := 33037573523996031004109

theorem tailTrace_72383 : CollatzResearch.WordTrace tailWord_72383 prefixEnd_72383 33037573523996031004109 := by
  unfold tailWord_72383
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640024896776227877317803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1760016597850818584878535 2640024896776227877317803)
  ·
    refine ⟨3960037345164341815976705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640024896776227877317803 3960037345164341815976705)
    ·
      refine ⟨2970028008873256361982529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3960037345164341815976705 2970028008873256361982529)
      ·
        refine ⟨2227521006654942271486897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970028008873256361982529 2227521006654942271486897)
        ·
          refine ⟨1670640754991206703615173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2227521006654942271486897 1670640754991206703615173)
          ·
            refine ⟨313245141560851256927845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1670640754991206703615173 313245141560851256927845)
            ·
              refine ⟨58733464042659610673971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 313245141560851256927845 58733464042659610673971)
              ·
                refine ⟨88100196063989416010957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58733464042659610673971 88100196063989416010957)
                ·
                  refine ⟨33037573523996031004109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88100196063989416010957 33037573523996031004109)
                  ·
                    rfl

theorem cell20_72383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 3].length) (baseStart_72383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72383 prefixEnd_72383 := by exact prefixLift 72383
  have htrace : WordTrace (prefixWord ++ tailWord_72383) baseStart_72383 baseEnd_72383 := by
    simpa [prefixWord, tailWord_72383, baseEnd_72383] using wordTrace_append hprefix tailTrace_72383
  have hstable : (prefixWord ++ tailWord_72383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72383).length < 2 ^ (prefixWord ++ tailWord_72383).sum := by decide
  have hdescent : baseEnd_72383 < baseStart_72383 := by decide
  rcases family_descends (prefixWord ++ tailWord_72383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72421 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 3]
def baseStart_72421 : Nat := 118140960795 + 72421 * 2 ^ 59
def prefixEnd_72421 : Nat := 4983230072969 + 3 ^ 40 * 72421 * 2
def baseEnd_72421 : Nat := 33054917759436787737287

theorem tailTrace_72421 : CollatzResearch.WordTrace tailWord_72421 prefixEnd_72421 33054917759436787737287 := by
  unfold tailWord_72421
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641410870638560367201117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1760940580425706911467411 2641410870638560367201117)
  ·
    refine ⟨990529076489460137700419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2641410870638560367201117 990529076489460137700419)
    ·
      refine ⟨1485793614734190206550629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990529076489460137700419 1485793614734190206550629)
      ·
        refine ⟨278586302762660663728243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1485793614734190206550629 278586302762660663728243)
        ·
          refine ⟨417879454143990995592365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278586302762660663728243 417879454143990995592365)
          ·
            refine ⟨156704795303996623347137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417879454143990995592365 156704795303996623347137)
            ·
              refine ⟨117528596477997467510353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156704795303996623347137 117528596477997467510353)
              ·
                refine ⟨88146447358498100632765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117528596477997467510353 88146447358498100632765)
                ·
                  refine ⟨33054917759436787737287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88146447358498100632765 33054917759436787737287)
                  ·
                    rfl

theorem cell20_72421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_72421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72421 prefixEnd_72421 := by exact prefixLift 72421
  have htrace : WordTrace (prefixWord ++ tailWord_72421) baseStart_72421 baseEnd_72421 := by
    simpa [prefixWord, tailWord_72421, baseEnd_72421] using wordTrace_append hprefix tailTrace_72421
  have hstable : (prefixWord ++ tailWord_72421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72421).length < 2 ^ (prefixWord ++ tailWord_72421).sum := by decide
  have hdescent : baseEnd_72421 < baseStart_72421 := by decide
  rcases family_descends (prefixWord ++ tailWord_72421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72425 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_72425 : Nat := 118140960795 + 72425 * 2 ^ 59
def prefixEnd_72425 : Nat := 4983230072969 + 3 ^ 40 * 72425 * 2
def baseEnd_72425 : Nat := 33056743468430551603937

theorem tailTrace_72425 : CollatzResearch.WordTrace tailWord_72425 prefixEnd_72425 33056743468430551603937 := by
  unfold tailWord_72425
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641556762624069050346729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1761037841749379366897819 2641556762624069050346729)
  ·
    refine ⟨1981167571968051787760047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2641556762624069050346729 1981167571968051787760047)
    ·
      refine ⟨2971751357952077681640071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981167571968051787760047 2971751357952077681640071)
      ·
        refine ⟨4457627036928116522460107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971751357952077681640071 4457627036928116522460107)
        ·
          refine ⟨6686440555392174783690161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457627036928116522460107 6686440555392174783690161)
          ·
            refine ⟨5014830416544131087767621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6686440555392174783690161 5014830416544131087767621)
            ·
              refine ⟨940280703102024578956429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5014830416544131087767621 940280703102024578956429)
              ·
                refine ⟨352605263663259217108661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940280703102024578956429 352605263663259217108661)
                ·
                  refine ⟨33056743468430551603937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352605263663259217108661 33056743468430551603937)
                  ·
                    rfl

theorem cell20_72425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_72425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72425 prefixEnd_72425 := by exact prefixLift 72425
  have htrace : WordTrace (prefixWord ++ tailWord_72425) baseStart_72425 baseEnd_72425 := by
    simpa [prefixWord, tailWord_72425, baseEnd_72425] using wordTrace_append hprefix tailTrace_72425
  have hstable : (prefixWord ++ tailWord_72425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72425).length < 2 ^ (prefixWord ++ tailWord_72425).sum := by decide
  have hdescent : baseEnd_72425 < baseStart_72425 := by decide
  rcases family_descends (prefixWord ++ tailWord_72425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72442 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_72442 : Nat := 118140960795 + 72442 * 2 ^ 59
def prefixEnd_72442 : Nat := 4983230072969 + 3 ^ 40 * 72442 * 2
def baseEnd_72442 : Nat := 33064502731654048037201

theorem tailTrace_72442 : CollatzResearch.WordTrace tailWord_72442 prefixEnd_72442 33064502731654048037201 := by
  unfold tailWord_72442
  simp only [CollatzResearch.WordTrace]
  refine ⟨660544200890620238428895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1761451202374987302477053 660544200890620238428895)
  ·
    refine ⟨990816301335930357643343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 660544200890620238428895 990816301335930357643343)
    ·
      refine ⟨1486224452003895536465015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990816301335930357643343 1486224452003895536465015)
      ·
        refine ⟨2229336678005843304697523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486224452003895536465015 2229336678005843304697523)
        ·
          refine ⟨3344005017008764957046285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229336678005843304697523 3344005017008764957046285)
          ·
            refine ⟨1254001881378286858892357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3344005017008764957046285 1254001881378286858892357)
            ·
              refine ⟨235125352758428786042317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1254001881378286858892357 235125352758428786042317)
              ·
                refine ⟨88172007284410794765869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235125352758428786042317 88172007284410794765869)
                ·
                  refine ⟨33064502731654048037201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88172007284410794765869 33064502731654048037201)
                  ·
                    rfl

theorem cell20_72442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_72442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72442 prefixEnd_72442 := by exact prefixLift 72442
  have htrace : WordTrace (prefixWord ++ tailWord_72442) baseStart_72442 baseEnd_72442 := by
    simpa [prefixWord, tailWord_72442, baseEnd_72442] using wordTrace_append hprefix tailTrace_72442
  have hstable : (prefixWord ++ tailWord_72442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72442).length < 2 ^ (prefixWord ++ tailWord_72442).sum := by decide
  have hdescent : baseEnd_72442 < baseStart_72442 := by decide
  rcases family_descends (prefixWord ++ tailWord_72442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72463 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_72463 : Nat := 118140960795 + 72463 * 2 ^ 59
def prefixEnd_72463 : Nat := 4983230072969 + 3 ^ 40 * 72463 * 2
def baseEnd_72463 : Nat := 33074087703871308337115

theorem tailTrace_72463 : CollatzResearch.WordTrace tailWord_72463 prefixEnd_72463 33074087703871308337115 := by
  unfold tailWord_72463
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642942736486401540230043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1761961824324267693486695 2642942736486401540230043)
  ·
    refine ⟨3964414104729602310345065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2642942736486401540230043 3964414104729602310345065)
    ·
      refine ⟨2973310578547201732758799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3964414104729602310345065 2973310578547201732758799)
      ·
        refine ⟨4459965867820802599138199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973310578547201732758799 4459965867820802599138199)
        ·
          refine ⟨6689948801731203898707299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459965867820802599138199 6689948801731203898707299)
          ·
            refine ⟨10034923202596805848060949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689948801731203898707299 10034923202596805848060949)
            ·
              refine ⟨470387025121725274127857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10034923202596805848060949 470387025121725274127857)
              ·
                refine ⟨352790268841293955595893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470387025121725274127857 352790268841293955595893)
                ·
                  refine ⟨33074087703871308337115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352790268841293955595893 33074087703871308337115)
                  ·
                    rfl

theorem cell20_72463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_72463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72463 prefixEnd_72463 := by exact prefixLift 72463
  have htrace : WordTrace (prefixWord ++ tailWord_72463) baseStart_72463 baseEnd_72463 := by
    simpa [prefixWord, tailWord_72463, baseEnd_72463] using wordTrace_append hprefix tailTrace_72463
  have hstable : (prefixWord ++ tailWord_72463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72463).length < 2 ^ (prefixWord ++ tailWord_72463).sum := by decide
  have hdescent : baseEnd_72463 < baseStart_72463 := by decide
  rcases family_descends (prefixWord ++ tailWord_72463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72480 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_72480 : Nat := 118140960795 + 72480 * 2 ^ 59
def prefixEnd_72480 : Nat := 4983230072969 + 3 ^ 40 * 72480 * 2
def baseEnd_72480 : Nat := 33081846967094804770379

theorem tailTrace_72480 : CollatzResearch.WordTrace tailWord_72480 prefixEnd_72480 33081846967094804770379 := by
  unfold tailWord_72480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321781388712406721799447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1762375184949875629065929 1321781388712406721799447)
  ·
    refine ⟨1982672083068610082699171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1321781388712406721799447 1982672083068610082699171)
    ·
      refine ⟨2974008124602915124048757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982672083068610082699171 2974008124602915124048757)
      ·
        refine ⟨278813261681523292879571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2974008124602915124048757 278813261681523292879571)
        ·
          refine ⟨418219892522284939319357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278813261681523292879571 418219892522284939319357)
          ·
            refine ⟨156832459695856852244759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418219892522284939319357 156832459695856852244759)
            ·
              refine ⟨235248689543785278367139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156832459695856852244759 235248689543785278367139)
              ·
                refine ⟨352873034315677917550709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235248689543785278367139 352873034315677917550709)
                ·
                  refine ⟨33081846967094804770379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352873034315677917550709 33081846967094804770379)
                  ·
                    rfl

theorem cell20_72480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_72480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72480 prefixEnd_72480 := by exact prefixLift 72480
  have htrace : WordTrace (prefixWord ++ tailWord_72480) baseStart_72480 baseEnd_72480 := by
    simpa [prefixWord, tailWord_72480, baseEnd_72480] using wordTrace_append hprefix tailTrace_72480
  have hstable : (prefixWord ++ tailWord_72480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72480).length < 2 ^ (prefixWord ++ tailWord_72480).sum := by decide
  have hdescent : baseEnd_72480 < baseStart_72480 := by decide
  rcases family_descends (prefixWord ++ tailWord_72480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72497 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 3]
def baseStart_72497 : Nat := 118140960795 + 72497 * 2 ^ 59
def prefixEnd_72497 : Nat := 4983230072969 + 3 ^ 40 * 72497 * 2
def baseEnd_72497 : Nat := 33089606230318301203643

theorem tailTrace_72497 : CollatzResearch.WordTrace tailWord_72497 prefixEnd_72497 33089606230318301203643 := by
  unfold tailWord_72497
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644182818363225346967745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1762788545575483564645163 2644182818363225346967745)
  ·
    refine ⟨1983137113772419010225809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2644182818363225346967745 1983137113772419010225809)
    ·
      refine ⟨1487352835329314257669357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1983137113772419010225809 1487352835329314257669357)
      ·
        refine ⟨557757313248492846626009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1487352835329314257669357 557757313248492846626009)
        ·
          refine ⟨418317984936369634969507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557757313248492846626009 418317984936369634969507)
          ·
            refine ⟨627476977404554452454261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418317984936369634969507 627476977404554452454261)
            ·
              refine ⟨58825966631676979917587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 627476977404554452454261 58825966631676979917587)
              ·
                refine ⟨88238949947515469876381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58825966631676979917587 88238949947515469876381)
                ·
                  refine ⟨33089606230318301203643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88238949947515469876381 33089606230318301203643)
                  ·
                    rfl

theorem cell20_72497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_72497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72497 prefixEnd_72497 := by exact prefixLift 72497
  have htrace : WordTrace (prefixWord ++ tailWord_72497) baseStart_72497 baseEnd_72497 := by
    simpa [prefixWord, tailWord_72497, baseEnd_72497] using wordTrace_append hprefix tailTrace_72497
  have hstable : (prefixWord ++ tailWord_72497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72497).length < 2 ^ (prefixWord ++ tailWord_72497).sum := by decide
  have hdescent : baseEnd_72497 < baseStart_72497 := by decide
  rcases family_descends (prefixWord ++ tailWord_72497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72511 : List Nat := [1, 1, 2, 2, 5, 1, 4, 4]
def baseStart_72511 : Nat := 118140960795 + 72511 * 2 ^ 59
def prefixEnd_72511 : Nat := 4983230072969 + 3 ^ 40 * 72511 * 2
def baseEnd_72511 : Nat := 11031998737265491578973

theorem tailTrace_72511 : CollatzResearch.WordTrace tailWord_72511 prefixEnd_72511 11031998737265491578973 := by
  unfold tailWord_72511
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644693440312505737977387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1763128960208337158651591 2644693440312505737977387)
  ·
    refine ⟨3967040160468758606966081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2644693440312505737977387 3967040160468758606966081)
    ·
      refine ⟨2975280120351568955224561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3967040160468758606966081 2975280120351568955224561)
      ·
        refine ⟨2231460090263676716418421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2975280120351568955224561 2231460090263676716418421)
        ·
          refine ⟨209199383462219692164227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2231460090263676716418421 209199383462219692164227)
          ·
            refine ⟨313799075193329538246341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209199383462219692164227 313799075193329538246341)
            ·
              refine ⟨58837326598749288421189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 313799075193329538246341 58837326598749288421189)
              ·
                refine ⟨11031998737265491578973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58837326598749288421189 11031998737265491578973)
                ·
                  rfl

theorem cell20_72511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_72511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72511 prefixEnd_72511 := by exact prefixLift 72511
  have htrace : WordTrace (prefixWord ++ tailWord_72511) baseStart_72511 baseEnd_72511 := by
    simpa [prefixWord, tailWord_72511, baseEnd_72511] using wordTrace_append hprefix tailTrace_72511
  have hstable : (prefixWord ++ tailWord_72511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72511).length < 2 ^ (prefixWord ++ tailWord_72511).sum := by decide
  have hdescent : baseEnd_72511 < baseStart_72511 := by decide
  rcases family_descends (prefixWord ++ tailWord_72511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72521 : List Nat := [1, 2, 1, 1, 2, 7, 1, 3, 2]
def baseStart_72521 : Nat := 118140960795 + 72521 * 2 ^ 59
def prefixEnd_72521 : Nat := 4983230072969 + 3 ^ 40 * 72521 * 2
def baseEnd_72521 : Nat := 33100560484280884403545

theorem tailTrace_72521 : CollatzResearch.WordTrace tailWord_72521 prefixEnd_72521 33100560484280884403545 := by
  unfold tailWord_72521
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645058170276277445841417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1763372113517518297227611 2645058170276277445841417)
  ·
    refine ⟨1983793627707208084381063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2645058170276277445841417 1983793627707208084381063)
    ·
      refine ⟨2975690441560812126571595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983793627707208084381063 2975690441560812126571595)
      ·
        refine ⟨4463535662341218189857393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975690441560812126571595 4463535662341218189857393)
        ·
          refine ⟨3347651746755913642393045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4463535662341218189857393 3347651746755913642393045)
          ·
            refine ⟨78460587814591725993587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3347651746755913642393045 78460587814591725993587)
            ·
              refine ⟨117690881721887588990381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78460587814591725993587 117690881721887588990381)
              ·
                refine ⟨44134080645707845871393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117690881721887588990381 44134080645707845871393)
                ·
                  refine ⟨33100560484280884403545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44134080645707845871393 33100560484280884403545)
                  ·
                    rfl

theorem cell20_72521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_72521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72521 prefixEnd_72521 := by exact prefixLift 72521
  have htrace : WordTrace (prefixWord ++ tailWord_72521) baseStart_72521 baseEnd_72521 := by
    simpa [prefixWord, tailWord_72521, baseEnd_72521] using wordTrace_append hprefix tailTrace_72521
  have hstable : (prefixWord ++ tailWord_72521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72521).length < 2 ^ (prefixWord ++ tailWord_72521).sum := by decide
  have hdescent : baseEnd_72521 < baseStart_72521 := by decide
  rcases family_descends (prefixWord ++ tailWord_72521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72552 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_72552 : Nat := 118140960795 + 72552 * 2 ^ 59
def prefixEnd_72552 : Nat := 4983230072969 + 3 ^ 40 * 72552 * 2
def baseEnd_72552 : Nat := 33114709728982554370085

theorem tailTrace_72552 : CollatzResearch.WordTrace tailWord_72552 prefixEnd_72552 33114709728982554370085 := by
  unfold tailWord_72552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323094416581984870109955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1764125888775979826813273 1323094416581984870109955)
  ·
    refine ⟨1984641624872977305164933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323094416581984870109955 1984641624872977305164933)
    ·
      refine ⟨372120304663683244718425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1984641624872977305164933 372120304663683244718425)
      ·
        refine ⟨279090228497762433538819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372120304663683244718425 279090228497762433538819)
        ·
          refine ⟨418635342746643650308229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279090228497762433538819 418635342746643650308229)
          ·
            refine ⟨78494126764995684432793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 418635342746643650308229 78494126764995684432793)
            ·
              refine ⟨58870595073746763324595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78494126764995684432793 58870595073746763324595)
              ·
                refine ⟨88305892610620144986893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58870595073746763324595 88305892610620144986893)
                ·
                  refine ⟨33114709728982554370085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88305892610620144986893 33114709728982554370085)
                  ·
                    rfl

theorem cell20_72552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_72552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72552 prefixEnd_72552 := by exact prefixLift 72552
  have htrace : WordTrace (prefixWord ++ tailWord_72552) baseStart_72552 baseEnd_72552 := by
    simpa [prefixWord, tailWord_72552, baseEnd_72552] using wordTrace_append hprefix tailTrace_72552
  have hstable : (prefixWord ++ tailWord_72552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72552).length < 2 ^ (prefixWord ++ tailWord_72552).sum := by decide
  have hdescent : baseEnd_72552 < baseStart_72552 := by decide
  rcases family_descends (prefixWord ++ tailWord_72552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72556 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_72556 : Nat := 118140960795 + 72556 * 2 ^ 59
def prefixEnd_72556 : Nat := 4983230072969 + 3 ^ 40 * 72556 * 2
def baseEnd_72556 : Nat := 33116535437976318236735

theorem tailTrace_72556 : CollatzResearch.WordTrace tailWord_72556 prefixEnd_72556 33116535437976318236735 := by
  unfold tailWord_72556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323167362574739211682761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1764223150099652282243681 1323167362574739211682761)
  ·
    refine ⟨992375521931054408762071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1323167362574739211682761 992375521931054408762071)
    ·
      refine ⟨1488563282896581613143107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992375521931054408762071 1488563282896581613143107)
      ·
        refine ⟨2232844924344872419714661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488563282896581613143107 2232844924344872419714661)
        ·
          refine ⟨418658423314663578696499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2232844924344872419714661 418658423314663578696499)
          ·
            refine ⟨627987634971995368044749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418658423314663578696499 627987634971995368044749)
            ·
              refine ⟨235495363114498263016781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 627987634971995368044749 235495363114498263016781)
              ·
                refine ⟨88310761167936848631293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235495363114498263016781 88310761167936848631293)
                ·
                  refine ⟨33116535437976318236735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88310761167936848631293 33116535437976318236735)
                  ·
                    rfl

theorem cell20_72556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_72556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72556 prefixEnd_72556 := by exact prefixLift 72556
  have htrace : WordTrace (prefixWord ++ tailWord_72556) baseStart_72556 baseEnd_72556 := by
    simpa [prefixWord, tailWord_72556, baseEnd_72556] using wordTrace_append hprefix tailTrace_72556
  have hstable : (prefixWord ++ tailWord_72556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72556).length < 2 ^ (prefixWord ++ tailWord_72556).sum := by decide
  have hdescent : baseEnd_72556 < baseStart_72556 := by decide
  rcases family_descends (prefixWord ++ tailWord_72556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72580 : List Nat := [2, 3, 2, 1, 1, 1, 1, 7, 2]
def baseStart_72580 : Nat := 118140960795 + 72580 * 2 ^ 59
def prefixEnd_72580 : Nat := 4983230072969 + 3 ^ 40 * 72580 * 2
def baseEnd_72580 : Nat := 33127489691938901436637

theorem tailTrace_72580 : CollatzResearch.WordTrace tailWord_72580 prefixEnd_72580 33127489691938901436637 := by
  unfold tailWord_72580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323605038531265261119597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1764806718041687014826129 1323605038531265261119597)
  ·
    refine ⟨496351889449224472919849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1323605038531265261119597 496351889449224472919849)
    ·
      refine ⟨372263917086918354689887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 496351889449224472919849 372263917086918354689887)
      ·
        refine ⟨558395875630377532034831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372263917086918354689887 558395875630377532034831)
        ·
          refine ⟨837593813445566298052247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558395875630377532034831 837593813445566298052247)
          ·
            refine ⟨1256390720168349447078371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837593813445566298052247 1256390720168349447078371)
            ·
              refine ⟨1884586080252524170617557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256390720168349447078371 1884586080252524170617557)
              ·
                refine ⟨44169986255918535248849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1884586080252524170617557 44169986255918535248849)
                ·
                  refine ⟨33127489691938901436637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44169986255918535248849 33127489691938901436637)
                  ·
                    rfl

theorem cell20_72580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_72580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72580 prefixEnd_72580 := by exact prefixLift 72580
  have htrace : WordTrace (prefixWord ++ tailWord_72580) baseStart_72580 baseEnd_72580 := by
    simpa [prefixWord, tailWord_72580, baseEnd_72580] using wordTrace_append hprefix tailTrace_72580
  have hstable : (prefixWord ++ tailWord_72580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72580).length < 2 ^ (prefixWord ++ tailWord_72580).sum := by decide
  have hdescent : baseEnd_72580 < baseStart_72580 := by decide
  rcases family_descends (prefixWord ++ tailWord_72580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72597 : List Nat := [1, 3, 2, 1, 1, 4, 4, 2, 2]
def baseStart_72597 : Nat := 118140960795 + 72597 * 2 ^ 59
def prefixEnd_72597 : Nat := 4983230072969 + 3 ^ 40 * 72597 * 2
def baseEnd_72597 : Nat := 33135248955162397869901

theorem tailTrace_72597 : CollatzResearch.WordTrace tailWord_72597 prefixEnd_72597 33135248955162397869901 := by
  unfold tailWord_72597
  simp only [CollatzResearch.WordTrace]
  refine ⟨2647830118000942425608045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1765220078667294950405363 2647830118000942425608045)
  ·
    refine ⟨992936294250353409603017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2647830118000942425608045 992936294250353409603017)
    ·
      refine ⟨744702220687765057202263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 992936294250353409603017 744702220687765057202263)
      ·
        refine ⟨1117053331031647585803395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744702220687765057202263 1117053331031647585803395)
        ·
          refine ⟨1675579996547471378705093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117053331031647585803395 1675579996547471378705093)
          ·
            refine ⟨314171249352650883507205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1675579996547471378705093 314171249352650883507205)
            ·
              refine ⟨58907109253622040657601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314171249352650883507205 58907109253622040657601)
              ·
                refine ⟨44180331940216530493201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58907109253622040657601 44180331940216530493201)
                ·
                  refine ⟨33135248955162397869901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44180331940216530493201 33135248955162397869901)
                  ·
                    rfl

theorem cell20_72597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_72597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72597 prefixEnd_72597 := by exact prefixLift 72597
  have htrace : WordTrace (prefixWord ++ tailWord_72597) baseStart_72597 baseEnd_72597 := by
    simpa [prefixWord, tailWord_72597, baseEnd_72597] using wordTrace_append hprefix tailTrace_72597
  have hstable : (prefixWord ++ tailWord_72597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72597).length < 2 ^ (prefixWord ++ tailWord_72597).sum := by decide
  have hdescent : baseEnd_72597 < baseStart_72597 := by decide
  rcases family_descends (prefixWord ++ tailWord_72597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72604 : List Nat := [2, 2, 3, 3, 2, 2, 1, 5]
def baseStart_72604 : Nat := 118140960795 + 72604 * 2 ^ 59
def prefixEnd_72604 : Nat := 4983230072969 + 3 ^ 40 * 72604 * 2
def baseEnd_72604 : Nat := 11046147981967161545513

theorem tailTrace_72604 : CollatzResearch.WordTrace tailWord_72604 prefixEnd_72604 11046147981967161545513 := by
  unfold tailWord_72604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324042714487791310556433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1765390285983721747408577 1324042714487791310556433)
  ·
    refine ⟨993032035865843482917325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1324042714487791310556433 993032035865843482917325)
    ·
      refine ⟨372387013449691306093997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 993032035865843482917325 372387013449691306093997)
      ·
        refine ⟨139645130043634239785249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372387013449691306093997 139645130043634239785249)
        ·
          refine ⟨104733847532725679838937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139645130043634239785249 104733847532725679838937)
          ·
            refine ⟨78550385649544259879203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104733847532725679838937 78550385649544259879203)
            ·
              refine ⟨117825578474316389818805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78550385649544259879203 117825578474316389818805)
              ·
                refine ⟨11046147981967161545513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117825578474316389818805 11046147981967161545513)
                ·
                  rfl

theorem cell20_72604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_72604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72604 prefixEnd_72604 := by exact prefixLift 72604
  have htrace : WordTrace (prefixWord ++ tailWord_72604) baseStart_72604 baseEnd_72604 := by
    simpa [prefixWord, tailWord_72604, baseEnd_72604] using wordTrace_append hprefix tailTrace_72604
  have hstable : (prefixWord ++ tailWord_72604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72604).length < 2 ^ (prefixWord ++ tailWord_72604).sum := by decide
  have hdescent : baseEnd_72604 < baseStart_72604 := by decide
  rcases family_descends (prefixWord ++ tailWord_72604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72608 : List Nat := [2, 1, 1, 4, 1, 1, 5, 5]
def baseStart_72608 : Nat := 118140960795 + 72608 * 2 ^ 59
def prefixEnd_72608 : Nat := 4983230072969 + 3 ^ 40 * 72608 * 2
def baseEnd_72608 : Nat := 11046756551631749501063

theorem tailTrace_72608 : CollatzResearch.WordTrace tailWord_72608 prefixEnd_72608 11046756551631749501063 := by
  unfold tailWord_72608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324115660480545652129239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1765487547307394202838985 1324115660480545652129239)
  ·
    refine ⟨1986173490720818478193859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1324115660480545652129239 1986173490720818478193859)
    ·
      refine ⟨2979260236081227717290789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1986173490720818478193859 2979260236081227717290789)
      ·
        refine ⟨558611294265230196992023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2979260236081227717290789 558611294265230196992023)
        ·
          refine ⟨837916941397845295488035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558611294265230196992023 837916941397845295488035)
          ·
            refine ⟨1256875412096767943232053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837916941397845295488035 1256875412096767943232053)
            ·
              refine ⟨117832069884071994678005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1256875412096767943232053 117832069884071994678005)
              ·
                refine ⟨11046756551631749501063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117832069884071994678005 11046756551631749501063)
                ·
                  rfl

theorem cell20_72608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_72608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72608 prefixEnd_72608 := by exact prefixLift 72608
  have htrace : WordTrace (prefixWord ++ tailWord_72608) baseStart_72608 baseEnd_72608 := by
    simpa [prefixWord, tailWord_72608, baseEnd_72608] using wordTrace_append hprefix tailTrace_72608
  have hstable : (prefixWord ++ tailWord_72608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72608).length < 2 ^ (prefixWord ++ tailWord_72608).sum := by decide
  have hdescent : baseEnd_72608 < baseStart_72608 := by decide
  rcases family_descends (prefixWord ++ tailWord_72608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72621 : List Nat := [1, 5, 2, 3, 1, 1, 3, 4]
def baseStart_72621 : Nat := 118140960795 + 72621 * 2 ^ 59
def prefixEnd_72621 : Nat := 4983230072969 + 3 ^ 40 * 72621 * 2
def baseEnd_72621 : Nat := 11048734403041660356601

theorem tailTrace_72621 : CollatzResearch.WordTrace tailWord_72621 prefixEnd_72621 11048734403041660356601 := by
  unfold tailWord_72621
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648705469913994524481717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1765803646609329682987811 2648705469913994524481717)
  ·
    refine ⟨248316137804436986670161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2648705469913994524481717 248316137804436986670161)
    ·
      refine ⟨186237103353327740002621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248316137804436986670161 186237103353327740002621)
      ·
        refine ⟨69838913757497902500983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186237103353327740002621 69838913757497902500983)
        ·
          refine ⟨104758370636246853751475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69838913757497902500983 104758370636246853751475)
          ·
            refine ⟨157137555954370280627213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104758370636246853751475 157137555954370280627213)
            ·
              refine ⟨58926583482888855235205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157137555954370280627213 58926583482888855235205)
              ·
                refine ⟨11048734403041660356601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58926583482888855235205 11048734403041660356601)
                ·
                  rfl

theorem cell20_72621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_72621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72621 prefixEnd_72621 := by exact prefixLift 72621
  have htrace : WordTrace (prefixWord ++ tailWord_72621) baseStart_72621 baseEnd_72621 := by
    simpa [prefixWord, tailWord_72621, baseEnd_72621] using wordTrace_append hprefix tailTrace_72621
  have hstable : (prefixWord ++ tailWord_72621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72621).length < 2 ^ (prefixWord ++ tailWord_72621).sum := by decide
  have hdescent : baseEnd_72621 < baseStart_72621 := by decide
  rcases family_descends (prefixWord ++ tailWord_72621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72698 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_72698 : Nat := 118140960795 + 72698 * 2 ^ 59
def prefixEnd_72698 : Nat := 4983230072969 + 3 ^ 40 * 72698 * 2
def baseEnd_72698 : Nat := 33181348107254935502821

theorem tailTrace_72698 : CollatzResearch.WordTrace tailWord_72698 prefixEnd_72698 33181348107254935502821 := by
  unfold tailWord_72698
  simp only [CollatzResearch.WordTrace]
  refine ⟨662878472658759168758687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1767675927090024450023165 662878472658759168758687)
  ·
    refine ⟨994317708988138753138031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662878472658759168758687 994317708988138753138031)
    ·
      refine ⟨1491476563482208129707047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994317708988138753138031 1491476563482208129707047)
      ·
        refine ⟨2237214845223312194560571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491476563482208129707047 2237214845223312194560571)
        ·
          refine ⟨3355822267834968291840857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237214845223312194560571 3355822267834968291840857)
          ·
            refine ⟨2516866700876226218880643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3355822267834968291840857 2516866700876226218880643)
            ·
              refine ⟨3775300051314339328320965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516866700876226218880643 3775300051314339328320965)
              ·
                refine ⟨707868759621438624060181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3775300051314339328320965 707868759621438624060181)
                ·
                  refine ⟨33181348107254935502821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 707868759621438624060181 33181348107254935502821)
                  ·
                    rfl

theorem cell20_72698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_72698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72698 prefixEnd_72698 := by exact prefixLift 72698
  have htrace : WordTrace (prefixWord ++ tailWord_72698) baseStart_72698 baseEnd_72698 := by
    simpa [prefixWord, tailWord_72698, baseEnd_72698] using wordTrace_append hprefix tailTrace_72698
  have hstable : (prefixWord ++ tailWord_72698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72698).length < 2 ^ (prefixWord ++ tailWord_72698).sum := by decide
  have hdescent : baseEnd_72698 < baseStart_72698 := by decide
  rcases family_descends (prefixWord ++ tailWord_72698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72711 : List Nat := [1, 1, 4, 3, 1, 1, 5, 2, 2]
def baseStart_72711 : Nat := 118140960795 + 72711 * 2 ^ 59
def prefixEnd_72711 : Nat := 4983230072969 + 3 ^ 40 * 72711 * 2
def baseEnd_72711 : Nat := 33187281661484668069435

theorem tailTrace_72711 : CollatzResearch.WordTrace tailWord_72711 prefixEnd_72711 33187281661484668069435 := by
  unfold tailWord_72711
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651988039587939895257987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1767992026391959930171991 2651988039587939895257987)
  ·
    refine ⟨3977982059381909842886981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2651988039587939895257987 3977982059381909842886981)
    ·
      refine ⟨745871636134108095541309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3977982059381909842886981 745871636134108095541309)
      ·
        refine ⟨279701863550290535827991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 745871636134108095541309 279701863550290535827991)
        ·
          refine ⟨419552795325435803741987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279701863550290535827991 419552795325435803741987)
          ·
            refine ⟨629329192988153705612981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419552795325435803741987 629329192988153705612981)
            ·
              refine ⟨58999611842639409901217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 629329192988153705612981 58999611842639409901217)
              ·
                refine ⟨44249708881979557425913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58999611842639409901217 44249708881979557425913)
                ·
                  refine ⟨33187281661484668069435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44249708881979557425913 33187281661484668069435)
                  ·
                    rfl

theorem cell20_72711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 2].length) (baseStart_72711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72711 prefixEnd_72711 := by exact prefixLift 72711
  have htrace : WordTrace (prefixWord ++ tailWord_72711) baseStart_72711 baseEnd_72711 := by
    simpa [prefixWord, tailWord_72711, baseEnd_72711] using wordTrace_append hprefix tailTrace_72711
  have hstable : (prefixWord ++ tailWord_72711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72711).length < 2 ^ (prefixWord ++ tailWord_72711).sum := by decide
  have hdescent : baseEnd_72711 < baseStart_72711 := by decide
  rcases family_descends (prefixWord ++ tailWord_72711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72715 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_72715 : Nat := 118140960795 + 72715 * 2 ^ 59
def prefixEnd_72715 : Nat := 4983230072969 + 3 ^ 40 * 72715 * 2
def baseEnd_72715 : Nat := 33189107370478431936085

theorem tailTrace_72715 : CollatzResearch.WordTrace tailWord_72715 prefixEnd_72715 33189107370478431936085 := by
  unfold tailWord_72715
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652133931573448578403599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1768089287715632385602399 2652133931573448578403599)
  ·
    refine ⟨3978200897360172867605399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2652133931573448578403599 3978200897360172867605399)
    ·
      refine ⟨5967301346040259301408099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3978200897360172867605399 5967301346040259301408099)
      ·
        refine ⟨8950952019060388952112149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5967301346040259301408099 8950952019060388952112149)
        ·
          refine ⟨419575875893455732130257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8950952019060388952112149 419575875893455732130257)
          ·
            refine ⟨314681906920091799097693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419575875893455732130257 314681906920091799097693)
            ·
              refine ⟨118005715095034424661635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314681906920091799097693 118005715095034424661635)
              ·
                refine ⟨177008572642551636992453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118005715095034424661635 177008572642551636992453)
                ·
                  refine ⟨33189107370478431936085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177008572642551636992453 33189107370478431936085)
                  ·
                    rfl

theorem cell20_72715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_72715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72715 prefixEnd_72715 := by exact prefixLift 72715
  have htrace : WordTrace (prefixWord ++ tailWord_72715) baseStart_72715 baseEnd_72715 := by
    simpa [prefixWord, tailWord_72715, baseEnd_72715] using wordTrace_append hprefix tailTrace_72715
  have hstable : (prefixWord ++ tailWord_72715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72715).length < 2 ^ (prefixWord ++ tailWord_72715).sum := by decide
  have hdescent : baseEnd_72715 < baseStart_72715 := by decide
  rcases family_descends (prefixWord ++ tailWord_72715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72725 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 3]
def baseStart_72725 : Nat := 118140960795 + 72725 * 2 ^ 59
def prefixEnd_72725 : Nat := 4983230072969 + 3 ^ 40 * 72725 * 2
def baseEnd_72725 : Nat := 33193671642962841602711

theorem tailTrace_72725 : CollatzResearch.WordTrace tailWord_72725 prefixEnd_72725 33193671642962841602711 := by
  unfold tailWord_72725
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652498661537220286267629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1768332441024813524178419 2652498661537220286267629)
  ·
    refine ⟨994686998076457607350361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2652498661537220286267629 994686998076457607350361)
    ·
      refine ⟨746015248557343205512771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 994686998076457607350361 746015248557343205512771)
      ·
        refine ⟨1119022872836014808269157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746015248557343205512771 1119022872836014808269157)
        ·
          refine ⟨209816788656752776550467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1119022872836014808269157 209816788656752776550467)
          ·
            refine ⟨314725182985129164825701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209816788656752776550467 314725182985129164825701)
            ·
              refine ⟨59010971809711718404819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314725182985129164825701 59010971809711718404819)
              ·
                refine ⟨88516457714567577607229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59010971809711718404819 88516457714567577607229)
                ·
                  refine ⟨33193671642962841602711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88516457714567577607229 33193671642962841602711)
                  ·
                    rfl

theorem cell20_72725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_72725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72725 prefixEnd_72725 := by exact prefixLift 72725
  have htrace : WordTrace (prefixWord ++ tailWord_72725) baseStart_72725 baseEnd_72725 := by
    simpa [prefixWord, tailWord_72725, baseEnd_72725] using wordTrace_append hprefix tailTrace_72725
  have hstable : (prefixWord ++ tailWord_72725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72725).length < 2 ^ (prefixWord ++ tailWord_72725).sum := by decide
  have hdescent : baseEnd_72725 < baseStart_72725 := by decide
  rcases family_descends (prefixWord ++ tailWord_72725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72766 : List Nat := [4, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_72766 : Nat := 118140960795 + 72766 * 2 ^ 59
def prefixEnd_72766 : Nat := 4983230072969 + 3 ^ 40 * 72766 * 2
def baseEnd_72766 : Nat := 33212385160148921235877

theorem tailTrace_72766 : CollatzResearch.WordTrace tailWord_72766 prefixEnd_72766 33212385160148921235877 := by
  unfold tailWord_72766
  simp only [CollatzResearch.WordTrace]
  refine ⟨331749256798585536063769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1769329369592456192340101 331749256798585536063769)
  ·
    refine ⟨248811942598939152047827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 331749256798585536063769 248811942598939152047827)
    ·
      refine ⟨373217913898408728071741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248811942598939152047827 373217913898408728071741)
      ·
        refine ⟨139956717711903273026903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373217913898408728071741 139956717711903273026903)
        ·
          refine ⟨209935076567854909540355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139956717711903273026903 209935076567854909540355)
          ·
            refine ⟨314902614851782364310533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209935076567854909540355 314902614851782364310533)
            ·
              refine ⟨59044240284709193308225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314902614851782364310533 59044240284709193308225)
              ·
                refine ⟨44283180213531894981169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59044240284709193308225 44283180213531894981169)
                ·
                  refine ⟨33212385160148921235877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44283180213531894981169 33212385160148921235877)
                  ·
                    rfl

theorem cell20_72766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_72766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72766 prefixEnd_72766 := by exact prefixLift 72766
  have htrace : WordTrace (prefixWord ++ tailWord_72766) baseStart_72766 baseEnd_72766 := by
    simpa [prefixWord, tailWord_72766, baseEnd_72766] using wordTrace_append hprefix tailTrace_72766
  have hstable : (prefixWord ++ tailWord_72766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72766).length < 2 ^ (prefixWord ++ tailWord_72766).sum := by decide
  have hdescent : baseEnd_72766 < baseStart_72766 := by decide
  rcases family_descends (prefixWord ++ tailWord_72766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72805 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_72805 : Nat := 118140960795 + 72805 * 2 ^ 59
def prefixEnd_72805 : Nat := 4983230072969 + 3 ^ 40 * 72805 * 2
def baseEnd_72805 : Nat := 33230185822838118935717

theorem tailTrace_72805 : CollatzResearch.WordTrace tailWord_72805 prefixEnd_72805 33230185822838118935717 := by
  unfold tailWord_72805
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655416501247393949179869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1770277667498262632786579 2655416501247393949179869)
  ·
    refine ⟨995781187967772730942451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2655416501247393949179869 995781187967772730942451)
    ·
      refine ⟨1493671781951659096413677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995781187967772730942451 1493671781951659096413677)
      ·
        refine ⟨560126918231872161155129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1493671781951659096413677 560126918231872161155129)
        ·
          refine ⟨420095188673904120866347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560126918231872161155129 420095188673904120866347)
          ·
            refine ⟨630142783010856181299521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420095188673904120866347 630142783010856181299521)
            ·
              refine ⟨472607087258142135974641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630142783010856181299521 472607087258142135974641)
              ·
                refine ⟨354455315443606601980981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472607087258142135974641 354455315443606601980981)
                ·
                  refine ⟨33230185822838118935717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354455315443606601980981 33230185822838118935717)
                  ·
                    rfl

theorem cell20_72805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_72805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72805 prefixEnd_72805 := by exact prefixLift 72805
  have htrace : WordTrace (prefixWord ++ tailWord_72805) baseStart_72805 baseEnd_72805 := by
    simpa [prefixWord, tailWord_72805, baseEnd_72805] using wordTrace_append hprefix tailTrace_72805
  have hstable : (prefixWord ++ tailWord_72805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72805).length < 2 ^ (prefixWord ++ tailWord_72805).sum := by decide
  have hdescent : baseEnd_72805 < baseStart_72805 := by decide
  rcases family_descends (prefixWord ++ tailWord_72805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72812 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_72812 : Nat := 118140960795 + 72812 * 2 ^ 59
def prefixEnd_72812 : Nat := 4983230072969 + 3 ^ 40 * 72812 * 2
def baseEnd_72812 : Nat := 33233380813577205702355

theorem tailTrace_72812 : CollatzResearch.WordTrace tailWord_72812 prefixEnd_72812 33233380813577205702355 := by
  unfold tailWord_72812
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327835906111017072342345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1770447874814689429789793 1327835906111017072342345)
  ·
    refine ⟨995876929583262804256759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1327835906111017072342345 995876929583262804256759)
    ·
      refine ⟨1493815394374894206385139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 995876929583262804256759 1493815394374894206385139)
      ·
        refine ⟨2240723091562341309577709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1493815394374894206385139 2240723091562341309577709)
        ·
          refine ⟨840271159335877991091641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2240723091562341309577709 840271159335877991091641)
          ·
            refine ⟨630203369501908493318731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840271159335877991091641 630203369501908493318731)
            ·
              refine ⟨945305054252862739978097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630203369501908493318731 945305054252862739978097)
              ·
                refine ⟨708978790689647054983573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945305054252862739978097 708978790689647054983573)
                ·
                  refine ⟨33233380813577205702355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 708978790689647054983573 33233380813577205702355)
                  ·
                    rfl

theorem cell20_72812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_72812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72812 prefixEnd_72812 := by exact prefixLift 72812
  have htrace : WordTrace (prefixWord ++ tailWord_72812) baseStart_72812 baseEnd_72812 := by
    simpa [prefixWord, tailWord_72812, baseEnd_72812] using wordTrace_append hprefix tailTrace_72812
  have hstable : (prefixWord ++ tailWord_72812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72812).length < 2 ^ (prefixWord ++ tailWord_72812).sum := by decide
  have hdescent : baseEnd_72812 < baseStart_72812 := by decide
  rcases family_descends (prefixWord ++ tailWord_72812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72822 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_72822 : Nat := 118140960795 + 72822 * 2 ^ 59
def prefixEnd_72822 : Nat := 4983230072969 + 3 ^ 40 * 72822 * 2
def baseEnd_72822 : Nat := 33237945086061615368981

theorem tailTrace_72822 : CollatzResearch.WordTrace tailWord_72822 prefixEnd_72822 33237945086061615368981 := by
  unfold tailWord_72822
  simp only [CollatzResearch.WordTrace]
  refine ⟨166002283886612865784295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1770691028123870568365813 166002283886612865784295)
  ·
    refine ⟨249003425829919298676443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166002283886612865784295 249003425829919298676443)
    ·
      refine ⟨373505138744878948014665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249003425829919298676443 373505138744878948014665)
      ·
        refine ⟨280128854058659211010999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373505138744878948014665 280128854058659211010999)
        ·
          refine ⟨420193281087988816516499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280128854058659211010999 420193281087988816516499)
          ·
            refine ⟨630289921631983224774749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420193281087988816516499 630289921631983224774749)
            ·
              refine ⟨236358720611993709290531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 630289921631983224774749 236358720611993709290531)
              ·
                refine ⟨354538080917990563935797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236358720611993709290531 354538080917990563935797)
                ·
                  refine ⟨33237945086061615368981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354538080917990563935797 33237945086061615368981)
                  ·
                    rfl

theorem cell20_72822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_72822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72822 prefixEnd_72822 := by exact prefixLift 72822
  have htrace : WordTrace (prefixWord ++ tailWord_72822) baseStart_72822 baseEnd_72822 := by
    simpa [prefixWord, tailWord_72822, baseEnd_72822] using wordTrace_append hprefix tailTrace_72822
  have hstable : (prefixWord ++ tailWord_72822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72822).length < 2 ^ (prefixWord ++ tailWord_72822).sum := by decide
  have hdescent : baseEnd_72822 < baseStart_72822 := by decide
  rcases family_descends (prefixWord ++ tailWord_72822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72829 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_72829 : Nat := 118140960795 + 72829 * 2 ^ 59
def prefixEnd_72829 : Nat := 4983230072969 + 3 ^ 40 * 72829 * 2
def baseEnd_72829 : Nat := 33241140076800702135619

theorem tailTrace_72829 : CollatzResearch.WordTrace tailWord_72829 prefixEnd_72829 33241140076800702135619 := by
  unfold tailWord_72829
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656291853160446048053541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1770861235440297365369027 2656291853160446048053541)
  ·
    refine ⟨498054722467583634010039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2656291853160446048053541 498054722467583634010039)
    ·
      refine ⟨747082083701375451015059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 498054722467583634010039 747082083701375451015059)
      ·
        refine ⟨1120623125552063176522589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747082083701375451015059 1120623125552063176522589)
        ·
          refine ⟨420233672082023691195971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1120623125552063176522589 420233672082023691195971)
          ·
            refine ⟨630350508123035536793957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420233672082023691195971 630350508123035536793957)
            ·
              refine ⟨118190720273069163148867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 630350508123035536793957 118190720273069163148867)
              ·
                refine ⟨177286080409603744723301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118190720273069163148867 177286080409603744723301)
                ·
                  refine ⟨33241140076800702135619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177286080409603744723301 33241140076800702135619)
                  ·
                    rfl

theorem cell20_72829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_72829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72829 prefixEnd_72829 := by exact prefixLift 72829
  have htrace : WordTrace (prefixWord ++ tailWord_72829) baseStart_72829 baseEnd_72829 := by
    simpa [prefixWord, tailWord_72829, baseEnd_72829] using wordTrace_append hprefix tailTrace_72829
  have hstable : (prefixWord ++ tailWord_72829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72829).length < 2 ^ (prefixWord ++ tailWord_72829).sum := by decide
  have hdescent : baseEnd_72829 < baseStart_72829 := by decide
  rcases family_descends (prefixWord ++ tailWord_72829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72843 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 3]
def baseStart_72843 : Nat := 118140960795 + 72843 * 2 ^ 59
def prefixEnd_72843 : Nat := 4983230072969 + 3 ^ 40 * 72843 * 2
def baseEnd_72843 : Nat := 33247530058278875668895

theorem tailTrace_72843 : CollatzResearch.WordTrace tailWord_72843 prefixEnd_72843 33247530058278875668895 := by
  unfold tailWord_72843
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656802475109726439063183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1771201650073150959375455 2656802475109726439063183)
  ·
    refine ⟨3985203712664589658594775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2656802475109726439063183 3985203712664589658594775)
    ·
      refine ⟨5977805568996884487892163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3985203712664589658594775 5977805568996884487892163)
      ·
        refine ⟨8966708353495326731838245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5977805568996884487892163 8966708353495326731838245)
        ·
          refine ⟨1681257816280373762219671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8966708353495326731838245 1681257816280373762219671)
          ·
            refine ⟨2521886724420560643329507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681257816280373762219671 2521886724420560643329507)
            ·
              refine ⟨3782830086630840964994261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521886724420560643329507 3782830086630840964994261)
              ·
                refine ⟨88660080155410335117053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3782830086630840964994261 88660080155410335117053)
                ·
                  refine ⟨33247530058278875668895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88660080155410335117053 33247530058278875668895)
                  ·
                    rfl

theorem cell20_72843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_72843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72843 prefixEnd_72843 := by exact prefixLift 72843
  have htrace : WordTrace (prefixWord ++ tailWord_72843) baseStart_72843 baseEnd_72843 := by
    simpa [prefixWord, tailWord_72843, baseEnd_72843] using wordTrace_append hprefix tailTrace_72843
  have hstable : (prefixWord ++ tailWord_72843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72843).length < 2 ^ (prefixWord ++ tailWord_72843).sum := by decide
  have hdescent : baseEnd_72843 < baseStart_72843 := by decide
  rcases family_descends (prefixWord ++ tailWord_72843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72888 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_72888 : Nat := 118140960795 + 72888 * 2 ^ 59
def prefixEnd_72888 : Nat := 4983230072969 + 3 ^ 40 * 72888 * 2
def baseEnd_72888 : Nat := 33268069284458719168711

theorem tailTrace_72888 : CollatzResearch.WordTrace tailWord_72888 prefixEnd_72888 33268069284458719168711 := by
  unfold tailWord_72888
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329221879973349562225659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1772295839964466082967545 1329221879973349562225659)
  ·
    refine ⟨1993832819960024343338489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1329221879973349562225659 1993832819960024343338489)
    ·
      refine ⟨1495374614970018257503867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1993832819960024343338489 1495374614970018257503867)
      ·
        refine ⟨2243061922455027386255801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1495374614970018257503867 2243061922455027386255801)
        ·
          refine ⟨1682296441841270539691851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2243061922455027386255801 1682296441841270539691851)
          ·
            refine ⟨2523444662761905809537777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682296441841270539691851 2523444662761905809537777)
            ·
              refine ⟨1892583497071429357153333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523444662761905809537777 1892583497071429357153333)
              ·
                refine ⟨177429702850446502233125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1892583497071429357153333 177429702850446502233125)
                ·
                  refine ⟨33268069284458719168711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177429702850446502233125 33268069284458719168711)
                  ·
                    rfl

theorem cell20_72888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_72888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72888 prefixEnd_72888 := by exact prefixLift 72888
  have htrace : WordTrace (prefixWord ++ tailWord_72888) baseStart_72888 baseEnd_72888 := by
    simpa [prefixWord, tailWord_72888, baseEnd_72888] using wordTrace_append hprefix tailTrace_72888
  have hstable : (prefixWord ++ tailWord_72888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72888).length < 2 ^ (prefixWord ++ tailWord_72888).sum := by decide
  have hdescent : baseEnd_72888 < baseStart_72888 := by decide
  rcases family_descends (prefixWord ++ tailWord_72888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72894 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_72894 : Nat := 118140960795 + 72894 * 2 ^ 59
def prefixEnd_72894 : Nat := 4983230072969 + 3 ^ 40 * 72894 * 2
def baseEnd_72894 : Nat := 33270807847949364968687

theorem tailTrace_72894 : CollatzResearch.WordTrace tailWord_72894 prefixEnd_72894 33270807847949364968687 := by
  unfold tailWord_72894
  simp only [CollatzResearch.WordTrace]
  refine ⟨332332824740620268646217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1772441731949974766113157 332332824740620268646217)
  ·
    refine ⟨249249618555465201484663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 332332824740620268646217 249249618555465201484663)
    ·
      refine ⟨373874427833197802226995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249249618555465201484663 373874427833197802226995)
      ·
        refine ⟨560811641749796703340493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373874427833197802226995 560811641749796703340493)
        ·
          refine ⟨210304365656173763752685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 560811641749796703340493 210304365656173763752685)
          ·
            refine ⟨78864137121065161407257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210304365656173763752685 78864137121065161407257)
            ·
              refine ⟨59148102840798871055443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78864137121065161407257 59148102840798871055443)
              ·
                refine ⟨88722154261198306583165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59148102840798871055443 88722154261198306583165)
                ·
                  refine ⟨33270807847949364968687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88722154261198306583165 33270807847949364968687)
                  ·
                    rfl

theorem cell20_72894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_72894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72894 prefixEnd_72894 := by exact prefixLift 72894
  have htrace : WordTrace (prefixWord ++ tailWord_72894) baseStart_72894 baseEnd_72894 := by
    simpa [prefixWord, tailWord_72894, baseEnd_72894] using wordTrace_append hprefix tailTrace_72894
  have hstable : (prefixWord ++ tailWord_72894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72894).length < 2 ^ (prefixWord ++ tailWord_72894).sum := by decide
  have hdescent : baseEnd_72894 < baseStart_72894 := by decide
  rcases family_descends (prefixWord ++ tailWord_72894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72895 : List Nat := [1, 1, 2, 2, 2, 2, 3, 7]
def baseStart_72895 : Nat := 118140960795 + 72895 * 2 ^ 59
def prefixEnd_72895 : Nat := 4983230072969 + 3 ^ 40 * 72895 * 2
def baseEnd_72895 : Nat := 11090421425065935311783

theorem tailTrace_72895 : CollatzResearch.WordTrace tailWord_72895 prefixEnd_72895 11090421425065935311783 := by
  unfold tailWord_72895
  simp only [CollatzResearch.WordTrace]
  refine ⟨2658699070921339319956139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1772466047280892879970759 2658699070921339319956139)
  ·
    refine ⟨3988048606382008979934209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2658699070921339319956139 3988048606382008979934209)
    ·
      refine ⟨2991036454786506734950657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3988048606382008979934209 2991036454786506734950657)
      ·
        refine ⟨2243277341089880051212993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2991036454786506734950657 2243277341089880051212993)
        ·
          refine ⟨1682458005817410038409745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2243277341089880051212993 1682458005817410038409745)
          ·
            refine ⟨1261843504363057528807309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1682458005817410038409745 1261843504363057528807309)
            ·
              refine ⟨473191314136146573302741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1261843504363057528807309 473191314136146573302741)
              ·
                refine ⟨11090421425065935311783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 473191314136146573302741 11090421425065935311783)
                ·
                  rfl

theorem cell20_72895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_72895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72895 prefixEnd_72895 := by exact prefixLift 72895
  have htrace : WordTrace (prefixWord ++ tailWord_72895) baseStart_72895 baseEnd_72895 := by
    simpa [prefixWord, tailWord_72895, baseEnd_72895] using wordTrace_append hprefix tailTrace_72895
  have hstable : (prefixWord ++ tailWord_72895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72895).length < 2 ^ (prefixWord ++ tailWord_72895).sum := by decide
  have hdescent : baseEnd_72895 < baseStart_72895 := by decide
  rcases family_descends (prefixWord ++ tailWord_72895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72933 : List Nat := [1, 3, 1, 4, 11]
def baseStart_72933 : Nat := 118140960795 + 72933 * 2 ^ 59
def prefixEnd_72933 : Nat := 4983230072969 + 3 ^ 40 * 72933 * 2
def baseEnd_72933 : Nat := 410970475439982255167

theorem tailTrace_72933 : CollatzResearch.WordTrace tailWord_72933 prefixEnd_72933 410970475439982255167 := by
  unfold tailWord_72933
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660085044783671809839453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1773390029855781206559635 2660085044783671809839453)
  ·
    refine ⟨997531891793876928689795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2660085044783671809839453 997531891793876928689795)
    ·
      refine ⟨1496297837690815393034693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997531891793876928689795 1496297837690815393034693)
      ·
        refine ⟨280555844567027886194005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1496297837690815393034693 280555844567027886194005)
        ·
          refine ⟨410970475439982255167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 280555844567027886194005 410970475439982255167)
          ·
            rfl

theorem cell20_72933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 11].length) (baseStart_72933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72933 prefixEnd_72933 := by exact prefixLift 72933
  have htrace : WordTrace (prefixWord ++ tailWord_72933) baseStart_72933 baseEnd_72933 := by
    simpa [prefixWord, tailWord_72933, baseEnd_72933] using wordTrace_append hprefix tailTrace_72933
  have hstable : (prefixWord ++ tailWord_72933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72933).length < 2 ^ (prefixWord ++ tailWord_72933).sum := by decide
  have hdescent : baseEnd_72933 < baseStart_72933 := by decide
  rcases family_descends (prefixWord ++ tailWord_72933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72935 : List Nat := [1, 1, 5, 3, 3, 1, 2, 2, 2]
def baseStart_72935 : Nat := 118140960795 + 72935 * 2 ^ 59
def prefixEnd_72935 : Nat := 4983230072969 + 3 ^ 40 * 72935 * 2
def baseEnd_72935 : Nat := 33289521365135444601853

theorem tailTrace_72935 : CollatzResearch.WordTrace tailWord_72935 prefixEnd_72935 33289521365135444601853 := by
  unfold tailWord_72935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660157990776426151412259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1773438660517617434274839 2660157990776426151412259)
  ·
    refine ⟨3990236986164639227118389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2660157990776426151412259 3990236986164639227118389)
    ·
      refine ⟨374084717452934927542349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3990236986164639227118389 374084717452934927542349)
      ·
        refine ⟨140281769044850597828381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 374084717452934927542349 140281769044850597828381)
        ·
          refine ⟨52605663391818974185643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140281769044850597828381 52605663391818974185643)
          ·
            refine ⟨78908495087728461278465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52605663391818974185643 78908495087728461278465)
            ·
              refine ⟨59181371315796345958849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78908495087728461278465 59181371315796345958849)
              ·
                refine ⟨44386028486847259469137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59181371315796345958849 44386028486847259469137)
                ·
                  refine ⟨33289521365135444601853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44386028486847259469137 33289521365135444601853)
                  ·
                    rfl

theorem cell20_72935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 2].length) (baseStart_72935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72935 prefixEnd_72935 := by exact prefixLift 72935
  have htrace : WordTrace (prefixWord ++ tailWord_72935) baseStart_72935 baseEnd_72935 := by
    simpa [prefixWord, tailWord_72935, baseEnd_72935] using wordTrace_append hprefix tailTrace_72935
  have hstable : (prefixWord ++ tailWord_72935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72935).length < 2 ^ (prefixWord ++ tailWord_72935).sum := by decide
  have hdescent : baseEnd_72935 < baseStart_72935 := by decide
  rcases family_descends (prefixWord ++ tailWord_72935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72936 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_72936 : Nat := 118140960795 + 72936 * 2 ^ 59
def prefixEnd_72936 : Nat := 4983230072969 + 3 ^ 40 * 72936 * 2
def baseEnd_72936 : Nat := 33289977792383885568515

theorem tailTrace_72936 : CollatzResearch.WordTrace tailWord_72936 prefixEnd_72936 33289977792383885568515 := by
  unfold tailWord_72936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330097231886401661099331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1773462975848535548132441 1330097231886401661099331)
  ·
    refine ⟨1995145847829602491648997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1330097231886401661099331 1995145847829602491648997)
    ·
      refine ⟨374089846468050467184187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1995145847829602491648997 374089846468050467184187)
      ·
        refine ⟨561134769702075700776281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374089846468050467184187 561134769702075700776281)
        ·
          refine ⟨420851077276556775582211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561134769702075700776281 420851077276556775582211)
          ·
            refine ⟨631276615914835163373317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420851077276556775582211 631276615914835163373317)
            ·
              refine ⟨118364365484031593132497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 631276615914835163373317 118364365484031593132497)
              ·
                refine ⟨88773274113023694849373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118364365484031593132497 88773274113023694849373)
                ·
                  refine ⟨33289977792383885568515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88773274113023694849373 33289977792383885568515)
                  ·
                    rfl

theorem cell20_72936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_72936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72936 prefixEnd_72936 := by exact prefixLift 72936
  have htrace : WordTrace (prefixWord ++ tailWord_72936) baseStart_72936 baseEnd_72936 := by
    simpa [prefixWord, tailWord_72936, baseEnd_72936] using wordTrace_append hprefix tailTrace_72936
  have hstable : (prefixWord ++ tailWord_72936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72936).length < 2 ^ (prefixWord ++ tailWord_72936).sum := by decide
  have hdescent : baseEnd_72936 < baseStart_72936 := by decide
  rcases family_descends (prefixWord ++ tailWord_72936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72939 : List Nat := [1, 1, 1, 1, 2, 8, 2, 2, 2]
def baseStart_72939 : Nat := 118140960795 + 72939 * 2 ^ 59
def prefixEnd_72939 : Nat := 4983230072969 + 3 ^ 40 * 72939 * 2
def baseEnd_72939 : Nat := 33291347074129208468503

theorem tailTrace_72939 : CollatzResearch.WordTrace tailWord_72939 prefixEnd_72939 33291347074129208468503 := by
  unfold tailWord_72939
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660303882761934834557871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1773535921841289889705247 2660303882761934834557871)
  ·
    refine ⟨3990455824142902251836807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2660303882761934834557871 3990455824142902251836807)
    ·
      refine ⟨5985683736214353377755211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990455824142902251836807 5985683736214353377755211)
      ·
        refine ⟨8978525604321530066632817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985683736214353377755211 8978525604321530066632817)
        ·
          refine ⟨6733894203241147549974613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8978525604321530066632817 6733894203241147549974613)
          ·
            refine ⟨78912822694232197851265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 6733894203241147549974613 78912822694232197851265)
            ·
              refine ⟨59184617020674148388449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78912822694232197851265 59184617020674148388449)
              ·
                refine ⟨44388462765505611291337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59184617020674148388449 44388462765505611291337)
                ·
                  refine ⟨33291347074129208468503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44388462765505611291337 33291347074129208468503)
                  ·
                    rfl

theorem cell20_72939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 2].length) (baseStart_72939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72939 prefixEnd_72939 := by exact prefixLift 72939
  have htrace : WordTrace (prefixWord ++ tailWord_72939) baseStart_72939 baseEnd_72939 := by
    simpa [prefixWord, tailWord_72939, baseEnd_72939] using wordTrace_append hprefix tailTrace_72939
  have hstable : (prefixWord ++ tailWord_72939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72939).length < 2 ^ (prefixWord ++ tailWord_72939).sum := by decide
  have hdescent : baseEnd_72939 < baseStart_72939 := by decide
  rcases family_descends (prefixWord ++ tailWord_72939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72946 : List Nat := [3, 2, 1, 3, 4, 1, 1, 5]
def baseStart_72946 : Nat := 118140960795 + 72946 * 2 ^ 59
def prefixEnd_72946 : Nat := 4983230072969 + 3 ^ 40 * 72946 * 2
def baseEnd_72946 : Nat := 11098180688289431745047

theorem tailTrace_72946 : CollatzResearch.WordTrace tailWord_72946 prefixEnd_72946 11098180688289431745047 := by
  unfold tailWord_72946
  simp only [CollatzResearch.WordTrace]
  refine ⟨665139798434143757515673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1773706129157716686708461 665139798434143757515673)
  ·
    refine ⟨498854848825607818136755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 665139798434143757515673 498854848825607818136755)
    ·
      refine ⟨748282273238411727205133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 498854848825607818136755 748282273238411727205133)
      ·
        refine ⟨280605852464404397701925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 748282273238411727205133 280605852464404397701925)
        ·
          refine ⟨52613597337075824569111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280605852464404397701925 52613597337075824569111)
          ·
            refine ⟨78920396005613736853667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52613597337075824569111 78920396005613736853667)
            ·
              refine ⟨118380594008420605280501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78920396005613736853667 118380594008420605280501)
              ·
                refine ⟨11098180688289431745047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118380594008420605280501 11098180688289431745047)
                ·
                  rfl

theorem cell20_72946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_72946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72946 prefixEnd_72946 := by exact prefixLift 72946
  have htrace : WordTrace (prefixWord ++ tailWord_72946) baseStart_72946 baseEnd_72946 := by
    simpa [prefixWord, tailWord_72946, baseEnd_72946] using wordTrace_append hprefix tailTrace_72946
  have hstable : (prefixWord ++ tailWord_72946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72946).length < 2 ^ (prefixWord ++ tailWord_72946).sum := by decide
  have hdescent : baseEnd_72946 < baseStart_72946 := by decide
  rcases family_descends (prefixWord ++ tailWord_72946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72991 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 3]
def baseStart_72991 : Nat := 118140960795 + 72991 * 2 ^ 59
def prefixEnd_72991 : Nat := 4983230072969 + 3 ^ 40 * 72991 * 2
def baseEnd_72991 : Nat := 33315081291048138734957

theorem tailTrace_72991 : CollatzResearch.WordTrace tailWord_72991 prefixEnd_72991 33315081291048138734957 := by
  unfold tailWord_72991
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662200478573547715450827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1774800319049031810300551 2662200478573547715450827)
  ·
    refine ⟨3993300717860321573176241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662200478573547715450827 3993300717860321573176241)
    ·
      refine ⟨2994975538395241179882181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3993300717860321573176241 2994975538395241179882181)
      ·
        refine ⟨561557913449107721227909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2994975538395241179882181 561557913449107721227909)
        ·
          refine ⟨105292108771707697730233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 561557913449107721227909 105292108771707697730233)
          ·
            refine ⟨78969081578780773297675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105292108771707697730233 78969081578780773297675)
            ·
              refine ⟨118453622368171159946513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78969081578780773297675 118453622368171159946513)
              ·
                refine ⟨88840216776128369959885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118453622368171159946513 88840216776128369959885)
                ·
                  refine ⟨33315081291048138734957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88840216776128369959885 33315081291048138734957)
                  ·
                    rfl

theorem cell20_72991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_72991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72991 prefixEnd_72991 := by exact prefixLift 72991
  have htrace : WordTrace (prefixWord ++ tailWord_72991) baseStart_72991 baseEnd_72991 := by
    simpa [prefixWord, tailWord_72991, baseEnd_72991] using wordTrace_append hprefix tailTrace_72991
  have hstable : (prefixWord ++ tailWord_72991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72991).length < 2 ^ (prefixWord ++ tailWord_72991).sum := by decide
  have hdescent : baseEnd_72991 < baseStart_72991 := by decide
  rcases family_descends (prefixWord ++ tailWord_72991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72995 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_72995 : Nat := 118140960795 + 72995 * 2 ^ 59
def prefixEnd_72995 : Nat := 4983230072969 + 3 ^ 40 * 72995 * 2
def baseEnd_72995 : Nat := 33316907000041902601607

theorem tailTrace_72995 : CollatzResearch.WordTrace tailWord_72995 prefixEnd_72995 33316907000041902601607 := by
  unfold tailWord_72995
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662346370559056398596439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1774897580372704265730959 2662346370559056398596439)
  ·
    refine ⟨3993519555838584597894659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662346370559056398596439 3993519555838584597894659)
    ·
      refine ⟨5990279333757876896841989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993519555838584597894659 5990279333757876896841989)
      ·
        refine ⟨1123177375079601918157873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5990279333757876896841989 1123177375079601918157873)
        ·
          refine ⟨842383031309701438618405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123177375079601918157873 842383031309701438618405)
          ·
            refine ⟨157946818370569019740951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 842383031309701438618405 157946818370569019740951)
            ·
              refine ⟨236920227555853529611427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157946818370569019740951 236920227555853529611427)
              ·
                refine ⟨355380341333780294417141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236920227555853529611427 355380341333780294417141)
                ·
                  refine ⟨33316907000041902601607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 355380341333780294417141 33316907000041902601607)
                  ·
                    rfl

theorem cell20_72995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_72995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_72995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_72995 prefixEnd_72995 := by exact prefixLift 72995
  have htrace : WordTrace (prefixWord ++ tailWord_72995) baseStart_72995 baseEnd_72995 := by
    simpa [prefixWord, tailWord_72995, baseEnd_72995] using wordTrace_append hprefix tailTrace_72995
  have hstable : (prefixWord ++ tailWord_72995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72995).length < 2 ^ (prefixWord ++ tailWord_72995).sum := by decide
  have hdescent : baseEnd_72995 < baseStart_72995 := by decide
  rcases family_descends (prefixWord ++ tailWord_72995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73036 : List Nat := [2, 2, 1, 3, 2, 2, 3, 3, 2]
def baseStart_73036 : Nat := 118140960795 + 73036 * 2 ^ 59
def prefixEnd_73036 : Nat := 4983230072969 + 3 ^ 40 * 73036 * 2
def baseEnd_73036 : Nat := 33335620517227982234773

theorem tailTrace_73036 : CollatzResearch.WordTrace tailWord_73036 prefixEnd_73036 33335620517227982234773 := by
  unfold tailWord_73036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1331920881705260200419481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1775894508940346933892641 1331920881705260200419481)
  ·
    refine ⟨998940661278945150314611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1331920881705260200419481 998940661278945150314611)
    ·
      refine ⟨1498410991918417725471917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998940661278945150314611 1498410991918417725471917)
      ·
        refine ⟨561904121969406647051969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1498410991918417725471917 561904121969406647051969)
        ·
          refine ⟨421428091477054985288977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561904121969406647051969 421428091477054985288977)
          ·
            refine ⟨316071068607791238966733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421428091477054985288977 316071068607791238966733)
            ·
              refine ⟨118526650727921714612525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316071068607791238966733 118526650727921714612525)
              ·
                refine ⟨44447494022970642979697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118526650727921714612525 44447494022970642979697)
                ·
                  refine ⟨33335620517227982234773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44447494022970642979697 33335620517227982234773)
                  ·
                    rfl

theorem cell20_73036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_73036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73036 prefixEnd_73036 := by exact prefixLift 73036
  have htrace : WordTrace (prefixWord ++ tailWord_73036) baseStart_73036 baseEnd_73036 := by
    simpa [prefixWord, tailWord_73036, baseEnd_73036] using wordTrace_append hprefix tailTrace_73036
  have hstable : (prefixWord ++ tailWord_73036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73036).length < 2 ^ (prefixWord ++ tailWord_73036).sum := by decide
  have hdescent : baseEnd_73036 < baseStart_73036 := by decide
  rcases family_descends (prefixWord ++ tailWord_73036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73047 : List Nat := [1, 1, 3, 2, 3, 2, 8]
def baseStart_73047 : Nat := 118140960795 + 73047 * 2 ^ 59
def prefixEnd_73047 : Nat := 4983230072969 + 3 ^ 40 * 73047 * 2
def baseEnd_73047 : Nat := 3704515690773425874229

theorem tailTrace_73047 : CollatzResearch.WordTrace tailWord_73047 prefixEnd_73047 3704515690773425874229 := by
  unfold tailWord_73047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664242966370669279489395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1776161977580446186326263 2664242966370669279489395)
  ·
    refine ⟨3996364449556003919234093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2664242966370669279489395 3996364449556003919234093)
    ·
      refine ⟨1498636668583501469712785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3996364449556003919234093 1498636668583501469712785)
      ·
        refine ⟨1123977501437626102284589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1498636668583501469712785 1123977501437626102284589)
        ·
          refine ⟨421491563039109788356721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1123977501437626102284589 421491563039109788356721)
          ·
            refine ⟨316118672279332341267541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421491563039109788356721 316118672279332341267541)
            ·
              refine ⟨3704515690773425874229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 316118672279332341267541 3704515690773425874229)
              ·
                rfl

theorem cell20_73047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_73047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73047 prefixEnd_73047 := by exact prefixLift 73047
  have htrace : WordTrace (prefixWord ++ tailWord_73047) baseStart_73047 baseEnd_73047 := by
    simpa [prefixWord, tailWord_73047, baseEnd_73047] using wordTrace_append hprefix tailTrace_73047
  have hstable : (prefixWord ++ tailWord_73047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73047).length < 2 ^ (prefixWord ++ tailWord_73047).sum := by decide
  have hdescent : baseEnd_73047 < baseStart_73047 := by decide
  rcases family_descends (prefixWord ++ tailWord_73047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73057 : List Nat := [1, 2, 3, 1, 1, 1, 1, 8, 2]
def baseStart_73057 : Nat := 118140960795 + 73057 * 2 ^ 59
def prefixEnd_73057 : Nat := 4983230072969 + 3 ^ 40 * 73057 * 2
def baseEnd_73057 : Nat := 33345205489445242534687

theorem tailTrace_73057 : CollatzResearch.WordTrace tailWord_73057 prefixEnd_73057 33345205489445242534687 := by
  unfold tailWord_73057
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664607696334440987353425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1776405130889627324902283 2664607696334440987353425)
  ·
    refine ⟨1998455772250830740515069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2664607696334440987353425 1998455772250830740515069)
    ·
      refine ⟨749420914594061527693151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1998455772250830740515069 749420914594061527693151)
      ·
        refine ⟨1124131371891092291539727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749420914594061527693151 1124131371891092291539727)
        ·
          refine ⟨1686197057836638437309591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124131371891092291539727 1686197057836638437309591)
          ·
            refine ⟨2529295586754957655964387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686197057836638437309591 2529295586754957655964387)
            ·
              refine ⟨3793943380132436483946581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529295586754957655964387 3793943380132436483946581)
              ·
                refine ⟨44460273985926990046249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3793943380132436483946581 44460273985926990046249)
                ·
                  refine ⟨33345205489445242534687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44460273985926990046249 33345205489445242534687)
                  ·
                    rfl

theorem cell20_73057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_73057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73057 prefixEnd_73057 := by exact prefixLift 73057
  have htrace : WordTrace (prefixWord ++ tailWord_73057) baseStart_73057 baseEnd_73057 := by
    simpa [prefixWord, tailWord_73057, baseEnd_73057] using wordTrace_append hprefix tailTrace_73057
  have hstable : (prefixWord ++ tailWord_73057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73057).length < 2 ^ (prefixWord ++ tailWord_73057).sum := by decide
  have hdescent : baseEnd_73057 < baseStart_73057 := by decide
  rcases family_descends (prefixWord ++ tailWord_73057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73071 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 3]
def baseStart_73071 : Nat := 118140960795 + 73071 * 2 ^ 59
def prefixEnd_73071 : Nat := 4983230072969 + 3 ^ 40 * 73071 * 2
def baseEnd_73071 : Nat := 33351595470923416067963

theorem tailTrace_73071 : CollatzResearch.WordTrace tailWord_73071 prefixEnd_73071 33351595470923416067963 := by
  unfold tailWord_73071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665118318283721378363067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1776745545522480918908711 2665118318283721378363067)
  ·
    refine ⟨3997677477425582067544601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2665118318283721378363067 3997677477425582067544601)
    ·
      refine ⟨2998258108069186550658451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3997677477425582067544601 2998258108069186550658451)
      ·
        refine ⟨4497387162103779825987677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2998258108069186550658451 4497387162103779825987677)
        ·
          refine ⟨1686520185788917434745379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4497387162103779825987677 1686520185788917434745379)
          ·
            refine ⟨2529780278683376152118069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686520185788917434745379 2529780278683376152118069)
            ·
              refine ⟨237166901126566514261069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2529780278683376152118069 237166901126566514261069)
              ·
                refine ⟨88937587922462442847901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237166901126566514261069 88937587922462442847901)
                ·
                  refine ⟨33351595470923416067963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88937587922462442847901 33351595470923416067963)
                  ·
                    rfl

theorem cell20_73071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_73071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73071 prefixEnd_73071 := by exact prefixLift 73071
  have htrace : WordTrace (prefixWord ++ tailWord_73071) baseStart_73071 baseEnd_73071 := by
    simpa [prefixWord, tailWord_73071, baseEnd_73071] using wordTrace_append hprefix tailTrace_73071
  have hstable : (prefixWord ++ tailWord_73071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73071).length < 2 ^ (prefixWord ++ tailWord_73071).sum := by decide
  have hdescent : baseEnd_73071 < baseStart_73071 := by decide
  rcases family_descends (prefixWord ++ tailWord_73071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73085 : List Nat := [1, 4, 1, 1, 2, 2, 1, 8]
def baseStart_73085 : Nat := 118140960795 + 73085 * 2 ^ 59
def prefixEnd_73085 : Nat := 4983230072969 + 3 ^ 40 * 73085 * 2
def baseEnd_73085 : Nat := 11119328484133863200413

theorem tailTrace_73085 : CollatzResearch.WordTrace tailWord_73085 prefixEnd_73085 11119328484133863200413 := by
  unfold tailWord_73085
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665628940233001769372709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1777085960155334512915139 2665628940233001769372709)
  ·
    refine ⟨499805426293687831757383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2665628940233001769372709 499805426293687831757383)
    ·
      refine ⟨749708139440531747636075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499805426293687831757383 749708139440531747636075)
      ·
        refine ⟨1124562209160797621454113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749708139440531747636075 1124562209160797621454113)
        ·
          refine ⟨843421656870598216090585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124562209160797621454113 843421656870598216090585)
          ·
            refine ⟨632566242652948662067939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843421656870598216090585 632566242652948662067939)
            ·
              refine ⟨948849363979422993101909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632566242652948662067939 948849363979422993101909)
              ·
                refine ⟨11119328484133863200413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 948849363979422993101909 11119328484133863200413)
                ·
                  rfl

theorem cell20_73085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_73085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73085 prefixEnd_73085 := by exact prefixLift 73085
  have htrace : WordTrace (prefixWord ++ tailWord_73085) baseStart_73085 baseEnd_73085 := by
    simpa [prefixWord, tailWord_73085, baseEnd_73085] using wordTrace_append hprefix tailTrace_73085
  have hstable : (prefixWord ++ tailWord_73085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73085).length < 2 ^ (prefixWord ++ tailWord_73085).sum := by decide
  have hdescent : baseEnd_73085 < baseStart_73085 := by decide
  rcases family_descends (prefixWord ++ tailWord_73085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73102 : List Nat := [4, 1, 1, 4, 2, 8]
def baseStart_73102 : Nat := 118140960795 + 73102 * 2 ^ 59
def prefixEnd_73102 : Nat := 4983230072969 + 3 ^ 40 * 73102 * 2
def baseEnd_73102 : Nat := 1235768322800929112389

theorem tailTrace_73102 : CollatzResearch.WordTrace tailWord_73102 prefixEnd_73102 1235768322800929112389 := by
  unfold tailWord_73102
  simp only [CollatzResearch.WordTrace]
  refine ⟨333281122646426709092695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1777499320780942448494373 333281122646426709092695)
  ·
    refine ⟨499921683969640063639043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 333281122646426709092695 499921683969640063639043)
    ·
      refine ⟨749882525954460095458565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499921683969640063639043 749882525954460095458565)
      ·
        refine ⟨140602973616461267898481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 749882525954460095458565 140602973616461267898481)
        ·
          refine ⟨105452230212345950923861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140602973616461267898481 105452230212345950923861)
          ·
            refine ⟨1235768322800929112389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 105452230212345950923861 1235768322800929112389)
            ·
              rfl

theorem cell20_73102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 8].length) (baseStart_73102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73102 prefixEnd_73102 := by exact prefixLift 73102
  have htrace : WordTrace (prefixWord ++ tailWord_73102) baseStart_73102 baseEnd_73102 := by
    simpa [prefixWord, tailWord_73102, baseEnd_73102] using wordTrace_append hprefix tailTrace_73102
  have hstable : (prefixWord ++ tailWord_73102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73102).length < 2 ^ (prefixWord ++ tailWord_73102).sum := by decide
  have hdescent : baseEnd_73102 < baseStart_73102 := by decide
  rcases family_descends (prefixWord ++ tailWord_73102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73108 : List Nat := [2, 4, 2, 1, 2, 3, 2, 2, 2]
def baseStart_73108 : Nat := 118140960795 + 73108 * 2 ^ 59
def prefixEnd_73108 : Nat := 4983230072969 + 3 ^ 40 * 73108 * 2
def baseEnd_73108 : Nat := 33368483279115731834479

theorem tailTrace_73108 : CollatzResearch.WordTrace tailWord_73108 prefixEnd_73108 33368483279115731834479 := by
  unfold tailWord_73108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333233909574838348729989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1777645212766451131639985 1333233909574838348729989)
  ·
    refine ⟨249981358045282190386873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1333233909574838348729989 249981358045282190386873)
    ·
      refine ⟨187486018533961642790155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249981358045282190386873 187486018533961642790155)
      ·
        refine ⟨281229027800942464185233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187486018533961642790155 281229027800942464185233)
        ·
          refine ⟨210921770850706848138925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281229027800942464185233 210921770850706848138925)
          ·
            refine ⟨79095664069015068052097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210921770850706848138925 79095664069015068052097)
            ·
              refine ⟨59321748051761301039073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79095664069015068052097 59321748051761301039073)
              ·
                refine ⟨44491311038820975779305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59321748051761301039073 44491311038820975779305)
                ·
                  refine ⟨33368483279115731834479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44491311038820975779305 33368483279115731834479)
                  ·
                    rfl

theorem cell20_73108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_73108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73108 prefixEnd_73108 := by exact prefixLift 73108
  have htrace : WordTrace (prefixWord ++ tailWord_73108) baseStart_73108 baseEnd_73108 := by
    simpa [prefixWord, tailWord_73108, baseEnd_73108] using wordTrace_append hprefix tailTrace_73108
  have hstable : (prefixWord ++ tailWord_73108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73108).length < 2 ^ (prefixWord ++ tailWord_73108).sum := by decide
  have hdescent : baseEnd_73108 < baseStart_73108 := by decide
  rcases family_descends (prefixWord ++ tailWord_73108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73109 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 3]
def baseStart_73109 : Nat := 118140960795 + 73109 * 2 ^ 59
def prefixEnd_73109 : Nat := 4983230072969 + 3 ^ 40 * 73109 * 2
def baseEnd_73109 : Nat := 33368939706364172801141

theorem tailTrace_73109 : CollatzResearch.WordTrace tailWord_73109 prefixEnd_73109 33368939706364172801141 := by
  unfold tailWord_73109
  simp only [CollatzResearch.WordTrace]
  refine ⟨2666504292146053868246381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1777669528097369245497587 2666504292146053868246381)
  ·
    refine ⟨999939109554770200592393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2666504292146053868246381 999939109554770200592393)
    ·
      refine ⟨749954332166077650444295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 999939109554770200592393 749954332166077650444295)
      ·
        refine ⟨1124931498249116475666443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749954332166077650444295 1124931498249116475666443)
        ·
          refine ⟨1687397247373674713499665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124931498249116475666443 1687397247373674713499665)
          ·
            refine ⟨1265547935530256035124749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687397247373674713499665 1265547935530256035124749)
            ·
              refine ⟨474580475823846013171781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1265547935530256035124749 474580475823846013171781)
              ·
                refine ⟨88983839216971127469709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 474580475823846013171781 88983839216971127469709)
                ·
                  refine ⟨33368939706364172801141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88983839216971127469709 33368939706364172801141)
                  ·
                    rfl

theorem cell20_73109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_73109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73109 prefixEnd_73109 := by exact prefixLift 73109
  have htrace : WordTrace (prefixWord ++ tailWord_73109) baseStart_73109 baseEnd_73109 := by
    simpa [prefixWord, tailWord_73109, baseEnd_73109] using wordTrace_append hprefix tailTrace_73109
  have hstable : (prefixWord ++ tailWord_73109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73109).length < 2 ^ (prefixWord ++ tailWord_73109).sum := by decide
  have hdescent : baseEnd_73109 < baseStart_73109 := by decide
  rcases family_descends (prefixWord ++ tailWord_73109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73133 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_73133 : Nat := 118140960795 + 73133 * 2 ^ 59
def prefixEnd_73133 : Nat := 4983230072969 + 3 ^ 40 * 73133 * 2
def baseEnd_73133 : Nat := 33379893960326756001043

theorem tailTrace_73133 : CollatzResearch.WordTrace tailWord_73133 prefixEnd_73133 33379893960326756001043 := by
  unfold tailWord_73133
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667379644059105967120053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1778253096039403978080035 2667379644059105967120053)
  ·
    refine ⟨250066841630541184417505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2667379644059105967120053 250066841630541184417505)
    ·
      refine ⟨187550131222905888313129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250066841630541184417505 187550131222905888313129)
      ·
        refine ⟨140662598417179416234847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187550131222905888313129 140662598417179416234847)
        ·
          refine ⟨210993897625769124352271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140662598417179416234847 210993897625769124352271)
          ·
            refine ⟨316490846438653686528407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210993897625769124352271 316490846438653686528407)
            ·
              refine ⟨474736269657980529792611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316490846438653686528407 474736269657980529792611)
              ·
                refine ⟨712104404486970794688917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474736269657980529792611 712104404486970794688917)
                ·
                  refine ⟨33379893960326756001043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 712104404486970794688917 33379893960326756001043)
                  ·
                    rfl

theorem cell20_73133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_73133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73133 prefixEnd_73133 := by exact prefixLift 73133
  have htrace : WordTrace (prefixWord ++ tailWord_73133) baseStart_73133 baseEnd_73133 := by
    simpa [prefixWord, tailWord_73133, baseEnd_73133] using wordTrace_append hprefix tailTrace_73133
  have hstable : (prefixWord ++ tailWord_73133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73133).length < 2 ^ (prefixWord ++ tailWord_73133).sum := by decide
  have hdescent : baseEnd_73133 < baseStart_73133 := by decide
  rcases family_descends (prefixWord ++ tailWord_73133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73164 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_73164 : Nat := 118140960795 + 73164 * 2 ^ 59
def prefixEnd_73164 : Nat := 4983230072969 + 3 ^ 40 * 73164 * 2
def baseEnd_73164 : Nat := 33394043205028425967583

theorem tailTrace_73164 : CollatzResearch.WordTrace tailWord_73164 prefixEnd_73164 33394043205028425967583 := by
  unfold tailWord_73164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334255153473399130749273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1779006871297865507665697 1334255153473399130749273)
  ·
    refine ⟨1000691365105049348061955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1334255153473399130749273 1000691365105049348061955)
    ·
      refine ⟨1501037047657574022092933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000691365105049348061955 1501037047657574022092933)
      ·
        refine ⟨281444446435795129142425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1501037047657574022092933 281444446435795129142425)
        ·
          refine ⟨211083334826846346856819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281444446435795129142425 211083334826846346856819)
          ·
            refine ⟨316625002240269520285229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211083334826846346856819 316625002240269520285229)
            ·
              refine ⟨118734375840101070106961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316625002240269520285229 118734375840101070106961)
              ·
                refine ⟨89050781880075802580221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118734375840101070106961 89050781880075802580221)
                ·
                  refine ⟨33394043205028425967583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89050781880075802580221 33394043205028425967583)
                  ·
                    rfl

theorem cell20_73164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_73164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73164 prefixEnd_73164 := by exact prefixLift 73164
  have htrace : WordTrace (prefixWord ++ tailWord_73164) baseStart_73164 baseEnd_73164 := by
    simpa [prefixWord, tailWord_73164, baseEnd_73164] using wordTrace_append hprefix tailTrace_73164
  have hstable : (prefixWord ++ tailWord_73164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73164).length < 2 ^ (prefixWord ++ tailWord_73164).sum := by decide
  have hdescent : baseEnd_73164 < baseStart_73164 := by decide
  rcases family_descends (prefixWord ++ tailWord_73164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
