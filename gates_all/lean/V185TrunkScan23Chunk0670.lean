import V185TrunkScan23Chunk0669

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3961634 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_3961634 : Nat := 118140960795 + 3961634 * 2 ^ 59
def prefixEnd_3961634 : Nat := 4983230072969 + 3 ^ 40 * 3961634 * 2
def baseEnd_3961634 : Nat := 2034222419194058322455783

theorem tailTrace_3961634 : CollatzResearch.WordTrace tailWord_3961634 prefixEnd_3961634 2034222419194058322455783 := by
  unfold tailWord_3961634
  simp only [CollatzResearch.WordTrace]
  refine ⟨36123165632421021516492989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96328441686456057377314637 36123165632421021516492989)
  ·
    refine ⟨13546187112157883068684871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36123165632421021516492989 13546187112157883068684871)
    ·
      refine ⟨20319280668236824603027307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13546187112157883068684871 20319280668236824603027307)
      ·
        refine ⟨30478921002355236904540961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20319280668236824603027307 30478921002355236904540961)
        ·
          refine ⟨22859190751766427678405721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30478921002355236904540961 22859190751766427678405721)
          ·
            refine ⟨17144393063824820758804291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22859190751766427678405721 17144393063824820758804291)
            ·
              refine ⟨25716589595737231138206437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144393063824820758804291 25716589595737231138206437)
              ·
                refine ⟨4821860549200730838413707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25716589595737231138206437 4821860549200730838413707)
                ·
                  refine ⟨7232790823801096257620561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821860549200730838413707 7232790823801096257620561)
                  ·
                    refine ⟨5424593117850822193215421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7232790823801096257620561 5424593117850822193215421)
                    ·
                      refine ⟨2034222419194058322455783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424593117850822193215421 2034222419194058322455783)
                      ·
                        rfl

theorem cell23_3961634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_3961634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961634 prefixEnd_3961634 := by exact prefixLift 3961634
  have htrace : WordTrace (prefixWord ++ tailWord_3961634) baseStart_3961634 baseEnd_3961634 := by
    simpa [prefixWord, tailWord_3961634, baseEnd_3961634] using wordTrace_append hprefix tailTrace_3961634
  have hstable : (prefixWord ++ tailWord_3961634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961634).length < 2 ^ (prefixWord ++ tailWord_3961634).sum := by decide
  have hdescent : baseEnd_3961634 < baseStart_3961634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961642 : List Nat := [3, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3961642 : Nat := 118140960795 + 3961642 * 2 ^ 59
def prefixEnd_3961642 : Nat := 4983230072969 + 3 ^ 40 * 3961642 * 2
def baseEnd_3961642 : Nat := 2034226527039294291155747

theorem tailTrace_3961642 : CollatzResearch.WordTrace tailWord_3961642 prefixEnd_3961642 2034226527039294291155747 := by
  unfold tailWord_3961642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36123238578413775858065795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96328636209103402288175453 36123238578413775858065795)
  ·
    refine ⟨54184857867620663787098693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36123238578413775858065795 54184857867620663787098693)
    ·
      refine ⟨10159660850178874460081005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54184857867620663787098693 10159660850178874460081005)
      ·
        refine ⟨3809872818817077922530377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10159660850178874460081005 3809872818817077922530377)
        ·
          refine ⟨2857404614112808441897783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3809872818817077922530377 2857404614112808441897783)
          ·
            refine ⟨4286106921169212662846675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857404614112808441897783 4286106921169212662846675)
            ·
              refine ⟨6429160381753818994270013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286106921169212662846675 6429160381753818994270013)
              ·
                refine ⟨2410935143157682122851255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6429160381753818994270013 2410935143157682122851255)
                ·
                  refine ⟨3616402714736523184276883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410935143157682122851255 3616402714736523184276883)
                  ·
                    refine ⟨5424604072104784776415325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3616402714736523184276883 5424604072104784776415325)
                    ·
                      refine ⟨2034226527039294291155747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424604072104784776415325 2034226527039294291155747)
                      ·
                        rfl

theorem cell23_3961642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3961642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961642 prefixEnd_3961642 := by exact prefixLift 3961642
  have htrace : WordTrace (prefixWord ++ tailWord_3961642) baseStart_3961642 baseEnd_3961642 := by
    simpa [prefixWord, tailWord_3961642, baseEnd_3961642] using wordTrace_append hprefix tailTrace_3961642
  have hstable : (prefixWord ++ tailWord_3961642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961642).length < 2 ^ (prefixWord ++ tailWord_3961642).sum := by decide
  have hdescent : baseEnd_3961642 < baseStart_3961642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961654 : List Nat := [5, 1, 2, 2, 2, 2, 9]
def baseStart_3961654 : Nat := 118140960795 + 3961654 * 2 ^ 59
def prefixEnd_3961654 : Nat := 4983230072969 + 3 ^ 40 * 3961654 * 2
def baseEnd_3961654 : Nat := 25113983812433928940811

theorem tailTrace_3961654 : CollatzResearch.WordTrace tailWord_3961654 prefixEnd_3961654 25113983812433928940811 := by
  unfold tailWord_3961654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030836999350726842606251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96328927993074419654466677 9030836999350726842606251)
  ·
    refine ⟨13546255499026090263909377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030836999350726842606251 13546255499026090263909377)
    ·
      refine ⟨10159691624269567697932033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13546255499026090263909377 10159691624269567697932033)
      ·
        refine ⟨7619768718202175773449025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10159691624269567697932033 7619768718202175773449025)
        ·
          refine ⟨5714826538651631830086769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7619768718202175773449025 5714826538651631830086769)
          ·
            refine ⟨4286119903988723872565077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5714826538651631830086769 4286119903988723872565077)
            ·
              refine ⟨25113983812433928940811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4286119903988723872565077 25113983812433928940811)
              ·
                rfl

theorem cell23_3961654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 9].length) (baseStart_3961654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961654 prefixEnd_3961654 := by exact prefixLift 3961654
  have htrace : WordTrace (prefixWord ++ tailWord_3961654) baseStart_3961654 baseEnd_3961654 := by
    simpa [prefixWord, tailWord_3961654, baseEnd_3961654] using wordTrace_append hprefix tailTrace_3961654
  have hstable : (prefixWord ++ tailWord_3961654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961654).length < 2 ^ (prefixWord ++ tailWord_3961654).sum := by decide
  have hdescent : baseEnd_3961654 < baseStart_3961654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961660 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3961660 : Nat := 118140960795 + 3961660 * 2 ^ 59
def prefixEnd_3961660 : Nat := 4983230072969 + 3 ^ 40 * 3961660 * 2
def baseEnd_3961660 : Nat := 2034235769691075220730663

theorem tailTrace_3961660 : CollatzResearch.WordTrace tailWord_3961660 prefixEnd_3961660 2034235769691075220730663 := by
  unfold tailWord_3961660
  simp only [CollatzResearch.WordTrace]
  refine ⟨72246805413794946253209217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96329073885059928337612289 72246805413794946253209217)
  ·
    refine ⟨54185104060346209689906913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72246805413794946253209217 54185104060346209689906913)
    ·
      refine ⟨40638828045259657267430185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54185104060346209689906913 40638828045259657267430185)
      ·
        refine ⟨30479121033944742950572639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40638828045259657267430185 30479121033944742950572639)
        ·
          refine ⟨45718681550917114425858959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30479121033944742950572639 45718681550917114425858959)
          ·
            refine ⟨68578022326375671638788439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45718681550917114425858959 68578022326375671638788439)
            ·
              refine ⟨102867033489563507458182659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68578022326375671638788439 102867033489563507458182659)
              ·
                refine ⟨154300550234345261187273989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102867033489563507458182659 154300550234345261187273989)
                ·
                  refine ⟨28931353168939736472613873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154300550234345261187273989 28931353168939736472613873)
                  ·
                    refine ⟨21698514876704802354460405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28931353168939736472613873 21698514876704802354460405)
                    ·
                      refine ⟨2034235769691075220730663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21698514876704802354460405 2034235769691075220730663)
                      ·
                        rfl

theorem cell23_3961660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3961660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961660 prefixEnd_3961660 := by exact prefixLift 3961660
  have htrace : WordTrace (prefixWord ++ tailWord_3961660) baseStart_3961660 baseEnd_3961660 := by
    simpa [prefixWord, tailWord_3961660, baseEnd_3961660] using wordTrace_append hprefix tailTrace_3961660
  have hstable : (prefixWord ++ tailWord_3961660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961660).length < 2 ^ (prefixWord ++ tailWord_3961660).sum := by decide
  have hdescent : baseEnd_3961660 < baseStart_3961660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961665 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3961665 : Nat := 118140960795 + 3961665 * 2 ^ 59
def prefixEnd_3961665 : Nat := 4983230072969 + 3 ^ 40 * 3961665 * 2
def baseEnd_3961665 : Nat := 2034238337094347701168141

theorem tailTrace_3961665 : CollatzResearch.WordTrace tailWord_3961665 prefixEnd_3961665 2034238337094347701168141 := by
  unfold tailWord_3961665
  simp only [CollatzResearch.WordTrace]
  refine ⟨144493793192571778360350449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96329195461714518906900299 144493793192571778360350449)
  ·
    refine ⟨108370344894428833770262837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144493793192571778360350449 108370344894428833770262837)
    ·
      refine ⟨10159719833852703165962141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108370344894428833770262837 10159719833852703165962141)
      ·
        refine ⟨3809894937694763687235803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10159719833852703165962141 3809894937694763687235803)
        ·
          refine ⟨5714842406542145530853705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809894937694763687235803 5714842406542145530853705)
          ·
            refine ⟨4286131804906609148140279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5714842406542145530853705 4286131804906609148140279)
            ·
              refine ⟨6429197707359913722210419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286131804906609148140279 6429197707359913722210419)
              ·
                refine ⟨9643796561039870583315629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6429197707359913722210419 9643796561039870583315629)
                ·
                  refine ⟨3616423710389951468743361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9643796561039870583315629 3616423710389951468743361)
                  ·
                    refine ⟨2712317782792463601557521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3616423710389951468743361 2712317782792463601557521)
                    ·
                      refine ⟨2034238337094347701168141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712317782792463601557521 2034238337094347701168141)
                      ·
                        rfl

theorem cell23_3961665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3961665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961665 prefixEnd_3961665 := by exact prefixLift 3961665
  have htrace : WordTrace (prefixWord ++ tailWord_3961665) baseStart_3961665 baseEnd_3961665 := by
    simpa [prefixWord, tailWord_3961665, baseEnd_3961665] using wordTrace_append hprefix tailTrace_3961665
  have hstable : (prefixWord ++ tailWord_3961665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961665).length < 2 ^ (prefixWord ++ tailWord_3961665).sum := by decide
  have hdescent : baseEnd_3961665 < baseStart_3961665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961680 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 2, 6]
def baseStart_3961680 : Nat := 118140960795 + 3961680 * 2 ^ 59
def prefixEnd_3961680 : Nat := 4983230072969 + 3 ^ 40 * 3961680 * 2
def baseEnd_3961680 : Nat := 678082013101388380826857

theorem tailTrace_3961680 : CollatzResearch.WordTrace tailWord_3961680 prefixEnd_3961680 678082013101388380826857 := by
  unfold tailWord_3961680
  simp only [CollatzResearch.WordTrace]
  refine ⟨72247170143758717961073247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96329560191678290614764329 72247170143758717961073247)
  ·
    refine ⟨108370755215638076941609871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72247170143758717961073247 108370755215638076941609871)
    ·
      refine ⟨162556132823457115412414807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108370755215638076941609871 162556132823457115412414807)
      ·
        refine ⟨243834199235185673118622211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162556132823457115412414807 243834199235185673118622211)
        ·
          refine ⟨365751298852778509677933317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243834199235185673118622211 365751298852778509677933317)
          ·
            refine ⟨68578368534895970564612497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365751298852778509677933317 68578368534895970564612497)
            ·
              refine ⟨51433776401171977923459373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68578368534895970564612497 51433776401171977923459373)
              ·
                refine ⟨19287666150439491721297265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51433776401171977923459373 19287666150439491721297265)
                ·
                  refine ⟨14465749612829618790972949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19287666150439491721297265 14465749612829618790972949)
                  ·
                    refine ⟨678082013101388380826857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14465749612829618790972949 678082013101388380826857)
                    ·
                      rfl

theorem cell23_3961680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_3961680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961680 prefixEnd_3961680 := by exact prefixLift 3961680
  have htrace : WordTrace (prefixWord ++ tailWord_3961680) baseStart_3961680 baseEnd_3961680 := by
    simpa [prefixWord, tailWord_3961680, baseEnd_3961680] using wordTrace_append hprefix tailTrace_3961680
  have hstable : (prefixWord ++ tailWord_3961680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961680).length < 2 ^ (prefixWord ++ tailWord_3961680).sum := by decide
  have hdescent : baseEnd_3961680 < baseStart_3961680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961681 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_3961681 : Nat := 118140960795 + 3961681 * 2 ^ 59
def prefixEnd_3961681 : Nat := 4983230072969 + 3 ^ 40 * 3961681 * 2
def baseEnd_3961681 : Nat := 2034246552784819638568067

theorem tailTrace_3961681 : CollatzResearch.WordTrace tailWord_3961681 prefixEnd_3961681 2034246552784819638568067 := by
  unfold tailWord_3961681
  simp only [CollatzResearch.WordTrace]
  refine ⟨144494376760513813092932897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96329584507009208728621931 144494376760513813092932897)
  ·
    refine ⟨108370782570385359819699673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144494376760513813092932897 108370782570385359819699673)
    ·
      refine ⟨81278086927789019864774755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108370782570385359819699673 81278086927789019864774755)
      ·
        refine ⟨121917130391683529797162133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81278086927789019864774755 121917130391683529797162133)
        ·
          refine ⟨5714865487110165459241975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121917130391683529797162133 5714865487110165459241975)
          ·
            refine ⟨8572298230665248188862963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714865487110165459241975 8572298230665248188862963)
            ·
              refine ⟨12858447345997872283294445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572298230665248188862963 12858447345997872283294445)
              ·
                refine ⟨4821917754749202106235417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12858447345997872283294445 4821917754749202106235417)
                ·
                  refine ⟨3616438316061901579676563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4821917754749202106235417 3616438316061901579676563)
                  ·
                    refine ⟨5424657474092852369514845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3616438316061901579676563 5424657474092852369514845)
                    ·
                      refine ⟨2034246552784819638568067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424657474092852369514845 2034246552784819638568067)
                      ·
                        rfl

theorem cell23_3961681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_3961681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961681 prefixEnd_3961681 := by exact prefixLift 3961681
  have htrace : WordTrace (prefixWord ++ tailWord_3961681) baseStart_3961681 baseEnd_3961681 := by
    simpa [prefixWord, tailWord_3961681, baseEnd_3961681] using wordTrace_append hprefix tailTrace_3961681
  have hstable : (prefixWord ++ tailWord_3961681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961681).length < 2 ^ (prefixWord ++ tailWord_3961681).sum := by decide
  have hdescent : baseEnd_3961681 < baseStart_3961681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961704 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3961704 : Nat := 118140960795 + 3961704 * 2 ^ 59
def prefixEnd_3961704 : Nat := 4983230072969 + 3 ^ 40 * 3961704 * 2
def baseEnd_3961704 : Nat := 2034258362839873048580461

theorem tailTrace_3961704 : CollatzResearch.WordTrace tailWord_3961704 prefixEnd_3961704 2034258362839873048580461 := by
  unfold tailWord_3961704
  simp only [CollatzResearch.WordTrace]
  refine ⟨72247607819715244010510083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96330143759620325347346777 72247607819715244010510083)
  ·
    refine ⟨108371411729572866015765125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72247607819715244010510083 108371411729572866015765125)
    ·
      refine ⟨20319639699294912377955961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108371411729572866015765125 20319639699294912377955961)
      ·
        refine ⟨15239729774471184283466971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20319639699294912377955961 15239729774471184283466971)
        ·
          refine ⟨22859594661706776425200457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15239729774471184283466971 22859594661706776425200457)
          ·
            refine ⟨17144695996280082318900343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22859594661706776425200457 17144695996280082318900343)
            ·
              refine ⟨25717043994420123478350515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144695996280082318900343 25717043994420123478350515)
              ·
                refine ⟨38575565991630185217525773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25717043994420123478350515 38575565991630185217525773)
                ·
                  refine ⟨14465837246861319456572165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38575565991630185217525773 14465837246861319456572165)
                  ·
                    refine ⟨2712344483786497398107281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14465837246861319456572165 2712344483786497398107281)
                    ·
                      refine ⟨2034258362839873048580461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712344483786497398107281 2034258362839873048580461)
                      ·
                        rfl

theorem cell23_3961704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3961704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961704 prefixEnd_3961704 := by exact prefixLift 3961704
  have htrace : WordTrace (prefixWord ++ tailWord_3961704) baseStart_3961704 baseEnd_3961704 := by
    simpa [prefixWord, tailWord_3961704, baseEnd_3961704] using wordTrace_append hprefix tailTrace_3961704
  have hstable : (prefixWord ++ tailWord_3961704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961704).length < 2 ^ (prefixWord ++ tailWord_3961704).sum := by decide
  have hdescent : baseEnd_3961704 < baseStart_3961704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961721 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 2, 2, 2]
def baseStart_3961721 : Nat := 118140960795 + 3961721 * 2 ^ 59
def prefixEnd_3961721 : Nat := 4983230072969 + 3 ^ 40 * 3961721 * 2
def baseEnd_3961721 : Nat := 2034267092010999482067883

theorem tailTrace_3961721 : CollatzResearch.WordTrace tailWord_3961721 prefixEnd_3961721 2034267092010999482067883 := by
  unfold tailWord_3961721
  simp only [CollatzResearch.WordTrace]
  refine ⟨144495835680368899924389017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96330557120245933282926011 144495835680368899924389017)
  ·
    refine ⟨108371876760276674943291763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144495835680368899924389017 108371876760276674943291763)
    ·
      refine ⟨162557815140415012414937645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108371876760276674943291763 162557815140415012414937645)
      ·
        refine ⟨60959180677655629655601617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162557815140415012414937645 60959180677655629655601617)
        ·
          refine ⟨45719385508241722241701213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60959180677655629655601617 45719385508241722241701213)
          ·
            refine ⟨17144769565590645840637955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45719385508241722241701213 17144769565590645840637955)
            ·
              refine ⟨25717154348385968760956933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144769565590645840637955 25717154348385968760956933)
              ·
                refine ⟨4821966440322369142679425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25717154348385968760956933 4821966440322369142679425)
                ·
                  refine ⟨3616474830241776857009569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4821966440322369142679425 3616474830241776857009569)
                  ·
                    refine ⟨2712356122681332642757177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3616474830241776857009569 2712356122681332642757177)
                    ·
                      refine ⟨2034267092010999482067883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712356122681332642757177 2034267092010999482067883)
                      ·
                        rfl

theorem cell23_3961721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_3961721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961721 prefixEnd_3961721 := by exact prefixLift 3961721
  have htrace : WordTrace (prefixWord ++ tailWord_3961721) baseStart_3961721 baseEnd_3961721 := by
    simpa [prefixWord, tailWord_3961721, baseEnd_3961721] using wordTrace_append hprefix tailTrace_3961721
  have hstable : (prefixWord ++ tailWord_3961721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961721).length < 2 ^ (prefixWord ++ tailWord_3961721).sum := by decide
  have hdescent : baseEnd_3961721 < baseStart_3961721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961737 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 3]
def baseStart_3961737 : Nat := 118140960795 + 3961737 * 2 ^ 59
def prefixEnd_3961737 : Nat := 4983230072969 + 3 ^ 40 * 3961737 * 2
def baseEnd_3961737 : Nat := 2034275307701471419467809

theorem tailTrace_3961737 : CollatzResearch.WordTrace tailWord_3961737 prefixEnd_3961737 2034275307701471419467809 := by
  unfold tailWord_3961737
  simp only [CollatzResearch.WordTrace]
  refine ⟨144496419248310934656971465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96330946165540623104647643 144496419248310934656971465)
  ·
    refine ⟨108372314436233200992728599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144496419248310934656971465 108372314436233200992728599)
    ·
      refine ⟨162558471654349801489092899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108372314436233200992728599 162558471654349801489092899)
      ·
        refine ⟨243837707481524702233639349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162558471654349801489092899 243837707481524702233639349)
        ·
          refine ⟨22859785076392940834403689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243837707481524702233639349 22859785076392940834403689)
          ·
            refine ⟨17144838807294705625802767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22859785076392940834403689 17144838807294705625802767)
            ·
              refine ⟨25717258210942058438704151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144838807294705625802767 25717258210942058438704151)
              ·
                refine ⟨38575887316413087658056227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25717258210942058438704151 38575887316413087658056227)
                ·
                  refine ⟨57863830974619631487084341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38575887316413087658056227 57863830974619631487084341)
                  ·
                    refine ⟨5424734153870590451914157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57863830974619631487084341 5424734153870590451914157)
                    ·
                      refine ⟨2034275307701471419467809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424734153870590451914157 2034275307701471419467809)
                      ·
                        rfl

theorem cell23_3961737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_3961737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961737 prefixEnd_3961737 := by exact prefixLift 3961737
  have htrace : WordTrace (prefixWord ++ tailWord_3961737) baseStart_3961737 baseEnd_3961737 := by
    simpa [prefixWord, tailWord_3961737, baseEnd_3961737] using wordTrace_append hprefix tailTrace_3961737
  have hstable : (prefixWord ++ tailWord_3961737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961737).length < 2 ^ (prefixWord ++ tailWord_3961737).sum := by decide
  have hdescent : baseEnd_3961737 < baseStart_3961737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961738 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_3961738 : Nat := 118140960795 + 3961738 * 2 ^ 59
def prefixEnd_3961738 : Nat := 4983230072969 + 3 ^ 40 * 3961738 * 2
def baseEnd_3961738 : Nat := 2034275821182125915555305

theorem tailTrace_3961738 : CollatzResearch.WordTrace tailWord_3961738 prefixEnd_3961738 2034275821182125915555305 := by
  unfold tailWord_3961738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36124113930326827956939467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96330970480871541218505245 36124113930326827956939467)
  ·
    refine ⟨54186170895490241935409201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36124113930326827956939467 54186170895490241935409201)
    ·
      refine ⟨40639628171617681451556901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54186170895490241935409201 40639628171617681451556901)
      ·
        refine ⟨7619930282178315272166919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40639628171617681451556901 7619930282178315272166919)
        ·
          refine ⟨11429895423267472908250379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7619930282178315272166919 11429895423267472908250379)
          ·
            refine ⟨17144843134901209362375569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11429895423267472908250379 17144843134901209362375569)
            ·
              refine ⟨12858632351175907021781677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17144843134901209362375569 12858632351175907021781677)
              ·
                refine ⟨4821987131690965133168129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12858632351175907021781677 4821987131690965133168129)
                ·
                  refine ⟨3616490348768223849876097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4821987131690965133168129 3616490348768223849876097)
                  ·
                    refine ⟨2712367761576167887407073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3616490348768223849876097 2712367761576167887407073)
                    ·
                      refine ⟨2034275821182125915555305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712367761576167887407073 2034275821182125915555305)
                      ·
                        rfl

theorem cell23_3961738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_3961738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961738 prefixEnd_3961738 := by exact prefixLift 3961738
  have htrace : WordTrace (prefixWord ++ tailWord_3961738) baseStart_3961738 baseEnd_3961738 := by
    simpa [prefixWord, tailWord_3961738, baseEnd_3961738] using wordTrace_append hprefix tailTrace_3961738
  have hstable : (prefixWord ++ tailWord_3961738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961738).length < 2 ^ (prefixWord ++ tailWord_3961738).sum := by decide
  have hdescent : baseEnd_3961738 < baseStart_3961738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961757 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3961757 : Nat := 118140960795 + 3961757 * 2 ^ 59
def prefixEnd_3961757 : Nat := 4983230072969 + 3 ^ 40 * 3961757 * 2
def baseEnd_3961757 : Nat := 678095192438187113739239

theorem tailTrace_3961757 : CollatzResearch.WordTrace tailWord_3961757 prefixEnd_3961757 678095192438187113739239 := by
  unfold tailWord_3961757
  simp only [CollatzResearch.WordTrace]
  refine ⟨144497148708238478072699525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96331432472158985381799683 144497148708238478072699525)
  ·
    refine ⟨27093215382794714638631161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144497148708238478072699525 27093215382794714638631161)
    ·
      refine ⟨20319911537096035978973371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27093215382794714638631161 20319911537096035978973371)
      ·
        refine ⟨30479867305644053968460057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20319911537096035978973371 30479867305644053968460057)
        ·
          refine ⟨22859900479233040476345043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30479867305644053968460057 22859900479233040476345043)
          ·
            refine ⟨34289850718849560714517565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22859900479233040476345043 34289850718849560714517565)
            ·
              refine ⟨12858694019568585267944087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34289850718849560714517565 12858694019568585267944087)
              ·
                refine ⟨19288041029352877901916131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12858694019568585267944087 19288041029352877901916131)
                ·
                  refine ⟨28932061544029316852874197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19288041029352877901916131 28932061544029316852874197)
                  ·
                    refine ⟨678095192438187113739239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28932061544029316852874197 678095192438187113739239)
                    ·
                      rfl

theorem cell23_3961757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3961757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961757 prefixEnd_3961757 := by exact prefixLift 3961757
  have htrace : WordTrace (prefixWord ++ tailWord_3961757) baseStart_3961757 baseEnd_3961757 := by
    simpa [prefixWord, tailWord_3961757, baseEnd_3961757] using wordTrace_append hprefix tailTrace_3961757
  have hstable : (prefixWord ++ tailWord_3961757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961757).length < 2 ^ (prefixWord ++ tailWord_3961757).sum := by decide
  have hdescent : baseEnd_3961757 < baseStart_3961757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961761 : List Nat := [1, 2, 3, 4, 1, 2, 2, 3, 5]
def baseStart_3961761 : Nat := 118140960795 + 3961761 * 2 ^ 59
def prefixEnd_3961761 : Nat := 4983230072969 + 3 ^ 40 * 3961761 * 2
def baseEnd_3961761 : Nat := 226031959026353258396411

theorem tailTrace_3961761 : CollatzResearch.WordTrace tailWord_3961761 prefixEnd_3961761 226031959026353258396411 := by
  unfold tailWord_3961761
  simp only [CollatzResearch.WordTrace]
  refine ⟨144497294600223986755845137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96331529733482657837230091 144497294600223986755845137)
  ·
    refine ⟨108372970950167990066883853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144497294600223986755845137 108372970950167990066883853)
    ·
      refine ⟨40639864106312996275081445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108372970950167990066883853 40639864106312996275081445)
      ·
        refine ⟨7619974519933686801577771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40639864106312996275081445 7619974519933686801577771)
        ·
          refine ⟨11429961779900530202366657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7619974519933686801577771 11429961779900530202366657)
          ·
            refine ⟨8572471334925397651774993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11429961779900530202366657 8572471334925397651774993)
            ·
              refine ⟨6429353501194048238831245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8572471334925397651774993 6429353501194048238831245)
              ·
                refine ⟨2411007562947768089561717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6429353501194048238831245 2411007562947768089561717)
                ·
                  refine ⟨226031959026353258396411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2411007562947768089561717 226031959026353258396411)
                  ·
                    rfl

theorem cell23_3961761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 5].length) (baseStart_3961761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961761 prefixEnd_3961761 := by exact prefixLift 3961761
  have htrace : WordTrace (prefixWord ++ tailWord_3961761) baseStart_3961761 baseEnd_3961761 := by
    simpa [prefixWord, tailWord_3961761, baseEnd_3961761] using wordTrace_append hprefix tailTrace_3961761
  have hstable : (prefixWord ++ tailWord_3961761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961761).length < 2 ^ (prefixWord ++ tailWord_3961761).sum := by decide
  have hdescent : baseEnd_3961761 < baseStart_3961761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961804 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_3961804 : Nat := 118140960795 + 3961804 * 2 ^ 59
def prefixEnd_3961804 : Nat := 4983230072969 + 3 ^ 40 * 3961804 * 2
def baseEnd_3961804 : Nat := 678103236968440885776667

theorem tailTrace_3961804 : CollatzResearch.WordTrace tailWord_3961804 prefixEnd_3961804 678103236968440885776667 := by
  unfold tailWord_3961804
  simp only [CollatzResearch.WordTrace]
  refine ⟨72249431469534102549830233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96332575292712136733106977 72249431469534102549830233)
  ·
    refine ⟨54187073602150576912372675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72249431469534102549830233 54187073602150576912372675)
    ·
      refine ⟨81280610403225865368559013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54187073602150576912372675 81280610403225865368559013)
      ·
        refine ⟨15240114450604849756604815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81280610403225865368559013 15240114450604849756604815)
        ·
          refine ⟨22860171675907274634907223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15240114450604849756604815 22860171675907274634907223)
          ·
            refine ⟨34290257513860911952360835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22860171675907274634907223 34290257513860911952360835)
            ·
              refine ⟨51435386270791367928541253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34290257513860911952360835 51435386270791367928541253)
              ·
                refine ⟨9644134925773381486601485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51435386270791367928541253 9644134925773381486601485)
                ·
                  refine ⟨3616550597165018057475557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9644134925773381486601485 3616550597165018057475557)
                  ·
                    refine ⟨678103236968440885776667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3616550597165018057475557 678103236968440885776667)
                    ·
                      rfl

theorem cell23_3961804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_3961804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961804 prefixEnd_3961804 := by exact prefixLift 3961804
  have htrace : WordTrace (prefixWord ++ tailWord_3961804) baseStart_3961804 baseEnd_3961804 := by
    simpa [prefixWord, tailWord_3961804, baseEnd_3961804] using wordTrace_append hprefix tailTrace_3961804
  have hstable : (prefixWord ++ tailWord_3961804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961804).length < 2 ^ (prefixWord ++ tailWord_3961804).sum := by decide
  have hdescent : baseEnd_3961804 < baseStart_3961804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961817 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 8]
def baseStart_3961817 : Nat := 118140960795 + 3961817 * 2 ^ 59
def prefixEnd_3961817 : Nat := 4983230072969 + 3 ^ 40 * 3961817 * 2
def baseEnd_3961817 : Nat := 226035154017092345163049

theorem tailTrace_3961817 : CollatzResearch.WordTrace tailWord_3961817 prefixEnd_3961817 226035154017092345163049 := by
  unfold tailWord_3961817
  simp only [CollatzResearch.WordTrace]
  refine ⟨144499337088021108319883705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96332891392014072213255803 144499337088021108319883705)
  ·
    refine ⟨108374502816015831239912779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144499337088021108319883705 108374502816015831239912779)
    ·
      refine ⟨162561754224023746859869169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108374502816015831239912779 162561754224023746859869169)
      ·
        refine ⟨121921315668017810144901877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162561754224023746859869169 121921315668017810144901877)
        ·
          refine ⟨11430123343876669701084551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121921315668017810144901877 11430123343876669701084551)
          ·
            refine ⟨17145185015815004551626827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430123343876669701084551 17145185015815004551626827)
            ·
              refine ⟨25717777523722506827440241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17145185015815004551626827 25717777523722506827440241)
              ·
                refine ⟨19288333142791880120580181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25717777523722506827440241 19288333142791880120580181)
                ·
                  refine ⟨226035154017092345163049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19288333142791880120580181 226035154017092345163049)
                  ·
                    rfl

theorem cell23_3961817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_3961817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961817 prefixEnd_3961817 := by exact prefixLift 3961817
  have htrace : WordTrace (prefixWord ++ tailWord_3961817) baseStart_3961817 baseEnd_3961817 := by
    simpa [prefixWord, tailWord_3961817, baseEnd_3961817] using wordTrace_append hprefix tailTrace_3961817
  have hstable : (prefixWord ++ tailWord_3961817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961817).length < 2 ^ (prefixWord ++ tailWord_3961817).sum := by decide
  have hdescent : baseEnd_3961817 < baseStart_3961817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961831 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3961831 : Nat := 118140960795 + 3961831 * 2 ^ 59
def prefixEnd_3961831 : Nat := 4983230072969 + 3 ^ 40 * 3961831 * 2
def baseEnd_3961831 : Nat := 2034323574882994051692377

theorem tailTrace_3961831 : CollatzResearch.WordTrace tailWord_3961831 prefixEnd_3961831 2034323574882994051692377 := by
  unfold tailWord_3961831
  simp only [CollatzResearch.WordTrace]
  refine ⟨144499847709970388710893347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96333231806646925807262231 144499847709970388710893347)
  ·
    refine ⟨216749771564955583066340021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144499847709970388710893347 216749771564955583066340021)
    ·
      refine ⟨20320291084214585912469377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216749771564955583066340021 20320291084214585912469377)
      ·
        refine ⟨15240218313160939434352033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20320291084214585912469377 15240218313160939434352033)
        ·
          refine ⟨11430163734870704575764025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15240218313160939434352033 11430163734870704575764025)
          ·
            refine ⟨8572622801153028431823019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11430163734870704575764025 8572622801153028431823019)
            ·
              refine ⟨12858934201729542647734529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572622801153028431823019 12858934201729542647734529)
              ·
                refine ⟨9644200651297156985800897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12858934201729542647734529 9644200651297156985800897)
                ·
                  refine ⟨7233150488472867739350673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644200651297156985800897 7233150488472867739350673)
                  ·
                    refine ⟨5424862866354650804513005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7233150488472867739350673 5424862866354650804513005)
                    ·
                      refine ⟨2034323574882994051692377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424862866354650804513005 2034323574882994051692377)
                      ·
                        rfl

theorem cell23_3961831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3961831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961831 prefixEnd_3961831 := by exact prefixLift 3961831
  have htrace : WordTrace (prefixWord ++ tailWord_3961831) baseStart_3961831 baseEnd_3961831 := by
    simpa [prefixWord, tailWord_3961831, baseEnd_3961831] using wordTrace_append hprefix tailTrace_3961831
  have hstable : (prefixWord ++ tailWord_3961831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961831).length < 2 ^ (prefixWord ++ tailWord_3961831).sum := by decide
  have hdescent : baseEnd_3961831 < baseStart_3961831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961838 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3961838 : Nat := 118140960795 + 3961838 * 2 ^ 59
def prefixEnd_3961838 : Nat := 4983230072969 + 3 ^ 40 * 3961838 * 2
def baseEnd_3961838 : Nat := 678109056415858508101615

theorem tailTrace_3961838 : CollatzResearch.WordTrace tailWord_3961838 prefixEnd_3961838 678109056415858508101615 := by
  unfold tailWord_3961838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062512877618128613299771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96333402013963352604265445 18062512877618128613299771)
  ·
    refine ⟨27093769316427192919949657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18062512877618128613299771 27093769316427192919949657)
    ·
      refine ⟨20320326987320394689962243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27093769316427192919949657 20320326987320394689962243)
      ·
        refine ⟨30480490480980592034943365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20320326987320394689962243 30480490480980592034943365)
        ·
          refine ⟨5715091965183861006551881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30480490480980592034943365 5715091965183861006551881)
          ·
            refine ⟨4286318973887895754913911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5715091965183861006551881 4286318973887895754913911)
            ·
              refine ⟨6429478460831843632370867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286318973887895754913911 6429478460831843632370867)
              ·
                refine ⟨9644217691247765448556301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6429478460831843632370867 9644217691247765448556301)
                ·
                  refine ⟨3616581634217912043208613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9644217691247765448556301 3616581634217912043208613)
                  ·
                    refine ⟨678109056415858508101615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3616581634217912043208613 678109056415858508101615)
                    ·
                      rfl

theorem cell23_3961838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3961838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961838 prefixEnd_3961838 := by exact prefixLift 3961838
  have htrace : WordTrace (prefixWord ++ tailWord_3961838) baseStart_3961838 baseEnd_3961838 := by
    simpa [prefixWord, tailWord_3961838, baseEnd_3961838] using wordTrace_append hprefix tailTrace_3961838
  have hstable : (prefixWord ++ tailWord_3961838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961838).length < 2 ^ (prefixWord ++ tailWord_3961838).sum := by decide
  have hdescent : baseEnd_3961838 < baseStart_3961838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961864 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 3, 5]
def baseStart_3961864 : Nat := 118140960795 + 3961864 * 2 ^ 59
def prefixEnd_3961864 : Nat := 4983230072969 + 3 ^ 40 * 3961864 * 2
def baseEnd_3961864 : Nat := 678113506581530807526575

theorem tailTrace_3961864 : CollatzResearch.WordTrace tailWord_3961864 prefixEnd_3961864 678113506581530807526575 := by
  unfold tailWord_3961864
  simp only [CollatzResearch.WordTrace]
  refine ⟨72250525659425417673422323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96334034212567223564563097 72250525659425417673422323)
  ·
    refine ⟨108375788489138126510133485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72250525659425417673422323 108375788489138126510133485)
    ·
      refine ⟨40640920683426797441300057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108375788489138126510133485 40640920683426797441300057)
      ·
        refine ⟨30480690512570098080975043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40640920683426797441300057 30480690512570098080975043)
        ·
          refine ⟨45721035768855147121462565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30480690512570098080975043 45721035768855147121462565)
          ·
            refine ⟨8572694206660340085274231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45721035768855147121462565 8572694206660340085274231)
            ·
              refine ⟨12859041309990510127911347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572694206660340085274231 12859041309990510127911347)
              ·
                refine ⟨19288561964985765191867021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12859041309990510127911347 19288561964985765191867021)
                ·
                  refine ⟨7233210736869661946950133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19288561964985765191867021 7233210736869661946950133)
                  ·
                    refine ⟨678113506581530807526575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7233210736869661946950133 678113506581530807526575)
                    ·
                      rfl

theorem cell23_3961864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_3961864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961864 prefixEnd_3961864 := by exact prefixLift 3961864
  have htrace : WordTrace (prefixWord ++ tailWord_3961864) baseStart_3961864 baseEnd_3961864 := by
    simpa [prefixWord, tailWord_3961864, baseEnd_3961864] using wordTrace_append hprefix tailTrace_3961864
  have hstable : (prefixWord ++ tailWord_3961864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961864).length < 2 ^ (prefixWord ++ tailWord_3961864).sum := by decide
  have hdescent : baseEnd_3961864 < baseStart_3961864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961904 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3]
def baseStart_3961904 : Nat := 118140960795 + 3961904 * 2 ^ 59
def prefixEnd_3961904 : Nat := 4983230072969 + 3 ^ 40 * 3961904 * 2
def baseEnd_3961904 : Nat := 2034361058970772266079541

theorem tailTrace_3961904 : CollatzResearch.WordTrace tailWord_3961904 prefixEnd_3961904 2034361058970772266079541 := by
  unfold tailWord_3961904
  simp only [CollatzResearch.WordTrace]
  refine ⟨72251255119352961089150383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96335006825803948118867177 72251255119352961089150383)
  ·
    refine ⟨108376882679029441633725575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72251255119352961089150383 108376882679029441633725575)
    ·
      refine ⟨162565324018544162450588363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108376882679029441633725575 162565324018544162450588363)
      ·
        refine ⟨243847986027816243675882545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162565324018544162450588363 243847986027816243675882545)
        ·
          refine ⟨182885989520862182756911909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243847986027816243675882545 182885989520862182756911909)
          ·
            refine ⟨34291123035161659266920983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182885989520862182756911909 34291123035161659266920983)
            ·
              refine ⟨51436684552742488900381475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34291123035161659266920983 51436684552742488900381475)
              ·
                refine ⟨77155026829113733350572213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51436684552742488900381475 77155026829113733350572213)
                ·
                  refine ⟨7233283765229412501616145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77155026829113733350572213 7233283765229412501616145)
                  ·
                    refine ⟨5424962823922059376212109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7233283765229412501616145 5424962823922059376212109)
                    ·
                      refine ⟨2034361058970772266079541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5424962823922059376212109 2034361058970772266079541)
                      ·
                        rfl

theorem cell23_3961904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_3961904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961904 prefixEnd_3961904 := by exact prefixLift 3961904
  have htrace : WordTrace (prefixWord ++ tailWord_3961904) baseStart_3961904 baseEnd_3961904 := by
    simpa [prefixWord, tailWord_3961904, baseEnd_3961904] using wordTrace_append hprefix tailTrace_3961904
  have hstable : (prefixWord ++ tailWord_3961904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961904).length < 2 ^ (prefixWord ++ tailWord_3961904).sum := by decide
  have hdescent : baseEnd_3961904 < baseStart_3961904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961914 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_3961914 : Nat := 118140960795 + 3961914 * 2 ^ 59
def prefixEnd_3961914 : Nat := 4983230072969 + 3 ^ 40 * 3961914 * 2
def baseEnd_3961914 : Nat := 2034366193777317226954495

theorem tailTrace_3961914 : CollatzResearch.WordTrace tailWord_3961914 prefixEnd_3961914 2034366193777317226954495 := by
  unfold tailWord_3961914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36125718742167423471541199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96335249979113129257443197 36125718742167423471541199)
  ·
    refine ⟨54188578113251135207311799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36125718742167423471541199 54188578113251135207311799)
    ·
      refine ⟨81282867169876702810967699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54188578113251135207311799 81282867169876702810967699)
      ·
        refine ⟨121924300754815054216451549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81282867169876702810967699 121924300754815054216451549)
        ·
          refine ⟨45721612783055645331169331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121924300754815054216451549 45721612783055645331169331)
          ·
            refine ⟨68582419174583467996753997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45721612783055645331169331 68582419174583467996753997)
            ·
              refine ⟨25718407190468800498782749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68582419174583467996753997 25718407190468800498782749)
              ·
                refine ⟨9644402696425800187043531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25718407190468800498782749 9644402696425800187043531)
                ·
                  refine ⟨14466604044638700280565297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644402696425800187043531 14466604044638700280565297)
                  ·
                    refine ⟨10849953033479025210423973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14466604044638700280565297 10849953033479025210423973)
                    ·
                      refine ⟨2034366193777317226954495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10849953033479025210423973 2034366193777317226954495)
                      ·
                        rfl

theorem cell23_3961914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_3961914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961914 prefixEnd_3961914 := by exact prefixLift 3961914
  have htrace : WordTrace (prefixWord ++ tailWord_3961914) baseStart_3961914 baseEnd_3961914 := by
    simpa [prefixWord, tailWord_3961914, baseEnd_3961914] using wordTrace_append hprefix tailTrace_3961914
  have hstable : (prefixWord ++ tailWord_3961914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961914).length < 2 ^ (prefixWord ++ tailWord_3961914).sum := by decide
  have hdescent : baseEnd_3961914 < baseStart_3961914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961938 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_3961938 : Nat := 118140960795 + 3961938 * 2 ^ 59
def prefixEnd_3961938 : Nat := 4983230072969 + 3 ^ 40 * 3961938 * 2
def baseEnd_3961938 : Nat := 2034378517313025133054385

theorem tailTrace_3961938 : CollatzResearch.WordTrace tailWord_3961938 prefixEnd_3961938 2034378517313025133054385 := by
  unfold tailWord_3961938
  simp only [CollatzResearch.WordTrace]
  refine ⟨36125937580145686496259617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96335833547055163990025645 36125937580145686496259617)
  ·
    refine ⟨27094453185109264872194713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36125937580145686496259617 27094453185109264872194713)
    ·
      refine ⟨20320839888831948654146035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27094453185109264872194713 20320839888831948654146035)
      ·
        refine ⟨30481259833247922981219053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20320839888831948654146035 30481259833247922981219053)
        ·
          refine ⟨11430472437467971117957145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30481259833247922981219053 11430472437467971117957145)
          ·
            refine ⟨8572854328100978338467859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11430472437467971117957145 8572854328100978338467859)
            ·
              refine ⟨12859281492151467507701789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572854328100978338467859 12859281492151467507701789)
              ·
                refine ⟨4822230559556800315388171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12859281492151467507701789 4822230559556800315388171)
                ·
                  refine ⟨7233345839335200473082257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822230559556800315388171 7233345839335200473082257)
                  ·
                    refine ⟨5425009379501400354811693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7233345839335200473082257 5425009379501400354811693)
                    ·
                      refine ⟨2034378517313025133054385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425009379501400354811693 2034378517313025133054385)
                      ·
                        rfl

theorem cell23_3961938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_3961938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961938 prefixEnd_3961938 := by exact prefixLift 3961938
  have htrace : WordTrace (prefixWord ++ tailWord_3961938) baseStart_3961938 baseEnd_3961938 := by
    simpa [prefixWord, tailWord_3961938, baseEnd_3961938] using wordTrace_append hprefix tailTrace_3961938
  have hstable : (prefixWord ++ tailWord_3961938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961938).length < 2 ^ (prefixWord ++ tailWord_3961938).sum := by decide
  have hdescent : baseEnd_3961938 < baseStart_3961938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961951 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 3]
def baseStart_3961951 : Nat := 118140960795 + 3961951 * 2 ^ 59
def prefixEnd_3961951 : Nat := 4983230072969 + 3 ^ 40 * 3961951 * 2
def baseEnd_3961951 : Nat := 2034385192561533582191825

theorem tailTrace_3961951 : CollatzResearch.WordTrace tailWord_3961951 prefixEnd_3961951 2034385192561533582191825 := by
  unfold tailWord_3961951
  simp only [CollatzResearch.WordTrace]
  refine ⟨144504224469535649205261707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96336149646357099470174471 144504224469535649205261707)
  ·
    refine ⟨216756336704303473807892561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144504224469535649205261707 216756336704303473807892561)
    ·
      refine ⟨162567252528227605355919421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216756336704303473807892561 162567252528227605355919421)
      ·
        refine ⟨60962719698085352008469783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162567252528227605355919421 60962719698085352008469783)
        ·
          refine ⟨91444079547128028012704675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60962719698085352008469783 91444079547128028012704675)
          ·
            refine ⟨137166119320692042019057013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91444079547128028012704675 137166119320692042019057013)
            ·
              refine ⟨12859323686314878939286595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137166119320692042019057013 12859323686314878939286595)
              ·
                refine ⟨19288985529472318408929893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12859323686314878939286595 19288985529472318408929893)
                ·
                  refine ⟨3616684786776059701674355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19288985529472318408929893 3616684786776059701674355)
                  ·
                    refine ⟨5425027180164089552511533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3616684786776059701674355 5425027180164089552511533)
                    ·
                      refine ⟨2034385192561533582191825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425027180164089552511533 2034385192561533582191825)
                      ·
                        rfl

theorem cell23_3961951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_3961951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961951 prefixEnd_3961951 := by exact prefixLift 3961951
  have htrace : WordTrace (prefixWord ++ tailWord_3961951) baseStart_3961951 baseEnd_3961951 := by
    simpa [prefixWord, tailWord_3961951, baseEnd_3961951] using wordTrace_append hprefix tailTrace_3961951
  have hstable : (prefixWord ++ tailWord_3961951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961951).length < 2 ^ (prefixWord ++ tailWord_3961951).sum := by decide
  have hdescent : baseEnd_3961951 < baseStart_3961951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961991 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_3961991 : Nat := 118140960795 + 3961991 * 2 ^ 59
def prefixEnd_3961991 : Nat := 4983230072969 + 3 ^ 40 * 3961991 * 2
def baseEnd_3961991 : Nat := 2034405731787713425691641

theorem tailTrace_3961991 : CollatzResearch.WordTrace tailWord_3961991 prefixEnd_3961991 2034405731787713425691641 := by
  unfold tailWord_3961991
  simp only [CollatzResearch.WordTrace]
  refine ⟨144505683389390736036717827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96337122259593824024478551 144505683389390736036717827)
  ·
    refine ⟨216758525084086104055076741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144505683389390736036717827 216758525084086104055076741)
    ·
      refine ⟨40642223453266144510326889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216758525084086104055076741 40642223453266144510326889)
      ·
        refine ⟨30481667589949608382745167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40642223453266144510326889 30481667589949608382745167)
        ·
          refine ⟨45722501384924412574117751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30481667589949608382745167 45722501384924412574117751)
          ·
            refine ⟨68583752077386618861176627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45722501384924412574117751 68583752077386618861176627)
            ·
              refine ⟨102875628116079928291764941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68583752077386618861176627 102875628116079928291764941)
              ·
                refine ⟨38578360543529973109411853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102875628116079928291764941 38578360543529973109411853)
                ·
                  refine ⟨14466885203823739916029445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38578360543529973109411853 14466885203823739916029445)
                  ·
                    refine ⟨2712540975716951234255521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14466885203823739916029445 2712540975716951234255521)
                    ·
                      refine ⟨2034405731787713425691641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712540975716951234255521 2034405731787713425691641)
                      ·
                        rfl

theorem cell23_3961991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_3961991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3961991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3961991 prefixEnd_3961991 := by exact prefixLift 3961991
  have htrace : WordTrace (prefixWord ++ tailWord_3961991) baseStart_3961991 baseEnd_3961991 := by
    simpa [prefixWord, tailWord_3961991, baseEnd_3961991] using wordTrace_append hprefix tailTrace_3961991
  have hstable : (prefixWord ++ tailWord_3961991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961991).length < 2 ^ (prefixWord ++ tailWord_3961991).sum := by decide
  have hdescent : baseEnd_3961991 < baseStart_3961991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962029 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_3962029 : Nat := 118140960795 + 3962029 * 2 ^ 59
def prefixEnd_3962029 : Nat := 4983230072969 + 3 ^ 40 * 3962029 * 2
def baseEnd_3962029 : Nat := 2034425244052584277016467

theorem tailTrace_3962029 : CollatzResearch.WordTrace tailWord_3962029 prefixEnd_3962029 2034425244052584277016467 := by
  unfold tailWord_3962029
  simp only [CollatzResearch.WordTrace]
  refine ⟨144507069363253068526601141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96338046242168712351067427 144507069363253068526601141)
  ·
    refine ⟨13547537752804975174368857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144507069363253068526601141 13547537752804975174368857)
    ·
      refine ⟨10160653314603731380776643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13547537752804975174368857 10160653314603731380776643)
      ·
        refine ⟨15240979971905597071164965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10160653314603731380776643 15240979971905597071164965)
        ·
          refine ⟨2857683744732299450843431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15240979971905597071164965 2857683744732299450843431)
          ·
            refine ⟨4286525617098449176265147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857683744732299450843431 4286525617098449176265147)
            ·
              refine ⟨6429788425647673764397721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286525617098449176265147 6429788425647673764397721)
              ·
                refine ⟨4822341319235755323298291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6429788425647673764397721 4822341319235755323298291)
                ·
                  refine ⟨7233511978853632984947437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822341319235755323298291 7233511978853632984947437)
                  ·
                    refine ⟨2712566992070112369355289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7233511978853632984947437 2712566992070112369355289)
                    ·
                      refine ⟨2034425244052584277016467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712566992070112369355289 2034425244052584277016467)
                      ·
                        rfl

theorem cell23_3962029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_3962029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962029 prefixEnd_3962029 := by exact prefixLift 3962029
  have htrace : WordTrace (prefixWord ++ tailWord_3962029) baseStart_3962029 baseEnd_3962029 := by
    simpa [prefixWord, tailWord_3962029, baseEnd_3962029] using wordTrace_append hprefix tailTrace_3962029
  have hstable : (prefixWord ++ tailWord_3962029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962029).length < 2 ^ (prefixWord ++ tailWord_3962029).sum := by decide
  have hdescent : baseEnd_3962029 < baseStart_3962029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962074 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_3962074 : Nat := 118140960795 + 3962074 * 2 ^ 59
def prefixEnd_3962074 : Nat := 4983230072969 + 3 ^ 40 * 3962074 * 2
def baseEnd_3962074 : Nat := 678149450227345533651253

theorem tailTrace_3962074 : CollatzResearch.WordTrace tailWord_3962074 prefixEnd_3962074 678149450227345533651253 := by
  unfold tailWord_3962074
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127177662022510302997319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96339140432060027474659517 36127177662022510302997319)
  ·
    refine ⟨54190766493033765454495979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36127177662022510302997319 54190766493033765454495979)
    ·
      refine ⟨81286149739550648181743969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54190766493033765454495979 81286149739550648181743969)
      ·
        refine ⟨60964612304662986136307977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81286149739550648181743969 60964612304662986136307977)
        ·
          refine ⟨45723459228497239602230983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60964612304662986136307977 45723459228497239602230983)
          ·
            refine ⟨68585188842745859403346475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45723459228497239602230983 68585188842745859403346475)
            ·
              refine ⟨102877783264118789105019713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68585188842745859403346475 102877783264118789105019713)
              ·
                refine ⟨77158337448089091828764785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102877783264118789105019713 77158337448089091828764785)
                ·
                  refine ⟨57868753086066818871573589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77158337448089091828764785 57868753086066818871573589)
                  ·
                    refine ⟨678149450227345533651253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57868753086066818871573589 678149450227345533651253)
                    ·
                      rfl

theorem cell23_3962074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_3962074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962074 prefixEnd_3962074 := by exact prefixLift 3962074
  have htrace : WordTrace (prefixWord ++ tailWord_3962074) baseStart_3962074 baseEnd_3962074 := by
    simpa [prefixWord, tailWord_3962074, baseEnd_3962074] using wordTrace_append hprefix tailTrace_3962074
  have hstable : (prefixWord ++ tailWord_3962074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962074).length < 2 ^ (prefixWord ++ tailWord_3962074).sum := by decide
  have hdescent : baseEnd_3962074 < baseStart_3962074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962091 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 5, 4]
def baseStart_3962091 : Nat := 118140960795 + 3962091 * 2 ^ 59
def prefixEnd_3962091 : Nat := 4983230072969 + 3 ^ 40 * 3962091 * 2
def baseEnd_3962091 : Nat := 678152359951054344813727

theorem tailTrace_3962091 : CollatzResearch.WordTrace tailWord_3962091 prefixEnd_3962091 678152359951054344813727 := by
  unfold tailWord_3962091
  simp only [CollatzResearch.WordTrace]
  refine ⟨144509330689028453115358127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96339553792685635410238751 144509330689028453115358127)
  ·
    refine ⟨216763996033542679673037191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144509330689028453115358127 216763996033542679673037191)
    ·
      refine ⟨325145994050314019509555787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216763996033542679673037191 325145994050314019509555787)
      ·
        refine ⟨487718991075471029264333681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325145994050314019509555787 487718991075471029264333681)
        ·
          refine ⟨365789243306603271948250261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487718991075471029264333681 365789243306603271948250261)
          ·
            refine ⟨17146370779997028372574231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 365789243306603271948250261 17146370779997028372574231)
            ·
              refine ⟨25719556169995542558861347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17146370779997028372574231 25719556169995542558861347)
              ·
                refine ⟨38579334254993313838292021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25719556169995542558861347 38579334254993313838292021)
                ·
                  refine ⟨3616812586405623172339877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38579334254993313838292021 3616812586405623172339877)
                  ·
                    refine ⟨678152359951054344813727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3616812586405623172339877 678152359951054344813727)
                    ·
                      rfl

theorem cell23_3962091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 4].length) (baseStart_3962091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962091 prefixEnd_3962091 := by exact prefixLift 3962091
  have htrace : WordTrace (prefixWord ++ tailWord_3962091) baseStart_3962091 baseEnd_3962091 := by
    simpa [prefixWord, tailWord_3962091, baseEnd_3962091] using wordTrace_append hprefix tailTrace_3962091
  have hstable : (prefixWord ++ tailWord_3962091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962091).length < 2 ^ (prefixWord ++ tailWord_3962091).sum := by decide
  have hdescent : baseEnd_3962091 < baseStart_3962091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962095 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 2, 5]
def baseStart_3962095 : Nat := 118140960795 + 3962095 * 2 ^ 59
def prefixEnd_3962095 : Nat := 4983230072969 + 3 ^ 40 * 3962095 * 2
def baseEnd_3962095 : Nat := 678153044591927006263721

theorem tailTrace_3962095 : CollatzResearch.WordTrace tailWord_3962095 prefixEnd_3962095 678153044591927006263721 := by
  unfold tailWord_3962095
  simp only [CollatzResearch.WordTrace]
  refine ⟨144509476581013961798503739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96339651054009307865669159 144509476581013961798503739)
  ·
    refine ⟨216764214871520942697755609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144509476581013961798503739 216764214871520942697755609)
    ·
      refine ⟨162573161153640707023316707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216764214871520942697755609 162573161153640707023316707)
      ·
        refine ⟨243859741730461060534975061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162573161153640707023316707 243859741730461060534975061)
        ·
          refine ⟨2857731348403840553144239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 243859741730461060534975061 2857731348403840553144239)
          ·
            refine ⟨4286597022605760829716359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857731348403840553144239 4286597022605760829716359)
            ·
              refine ⟨6429895533908641244574539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286597022605760829716359 6429895533908641244574539)
              ·
                refine ⟨9644843300862961866861809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6429895533908641244574539 9644843300862961866861809)
                ·
                  refine ⟨7233632475647221400146357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644843300862961866861809 7233632475647221400146357)
                  ·
                    refine ⟨678153044591927006263721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7233632475647221400146357 678153044591927006263721)
                    ·
                      rfl

theorem cell23_3962095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 5].length) (baseStart_3962095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962095 prefixEnd_3962095 := by exact prefixLift 3962095
  have htrace : WordTrace (prefixWord ++ tailWord_3962095) baseStart_3962095 baseEnd_3962095 := by
    simpa [prefixWord, tailWord_3962095, baseEnd_3962095] using wordTrace_append hprefix tailTrace_3962095
  have hstable : (prefixWord ++ tailWord_3962095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962095).length < 2 ^ (prefixWord ++ tailWord_3962095).sum := by decide
  have hdescent : baseEnd_3962095 < baseStart_3962095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962098 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3962098 : Nat := 118140960795 + 3962098 * 2 ^ 59
def prefixEnd_3962098 : Nat := 4983230072969 + 3 ^ 40 * 3962098 * 2
def baseEnd_3962098 : Nat := 2034460674217744507053649

theorem tailTrace_3962098 : CollatzResearch.WordTrace tailWord_3962098 prefixEnd_3962098 2034460674217744507053649 := by
  unfold tailWord_3962098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127396500000773327715737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96339724000002062207241965 36127396500000773327715737)
  ·
    refine ⟨27095547375000579995786803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36127396500000773327715737 27095547375000579995786803)
    ·
      refine ⟨40643321062500869993680205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27095547375000579995786803 40643321062500869993680205)
      ·
        refine ⟨15241245398437826247630077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40643321062500869993680205 15241245398437826247630077)
        ·
          refine ⟨5715467024414184842861279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15241245398437826247630077 5715467024414184842861279)
          ·
            refine ⟨8573200536621277264291919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715467024414184842861279 8573200536621277264291919)
            ·
              refine ⟨12859800804931915896437879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573200536621277264291919 12859800804931915896437879)
              ·
                refine ⟨19289701207397873844656819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12859800804931915896437879 19289701207397873844656819)
                ·
                  refine ⟨28934551811096810766985229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19289701207397873844656819 28934551811096810766985229)
                  ·
                    refine ⟨10850456929161304037619461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28934551811096810766985229 10850456929161304037619461)
                    ·
                      refine ⟨2034460674217744507053649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10850456929161304037619461 2034460674217744507053649)
                      ·
                        rfl

theorem cell23_3962098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3962098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962098 prefixEnd_3962098 := by exact prefixLift 3962098
  have htrace : WordTrace (prefixWord ++ tailWord_3962098) baseStart_3962098 baseEnd_3962098 := by
    simpa [prefixWord, tailWord_3962098, baseEnd_3962098] using wordTrace_append hprefix tailTrace_3962098
  have hstable : (prefixWord ++ tailWord_3962098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962098).length < 2 ^ (prefixWord ++ tailWord_3962098).sum := by decide
  have hdescent : baseEnd_3962098 < baseStart_3962098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962175 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 2, 3, 2]
def baseStart_3962175 : Nat := 118140960795 + 3962175 * 2 ^ 59
def prefixEnd_3962175 : Nat := 4983230072969 + 3 ^ 40 * 3962175 * 2
def baseEnd_3962175 : Nat := 2034500212228140705790795

theorem tailTrace_3962175 : CollatzResearch.WordTrace tailWord_3962175 prefixEnd_3962175 2034500212228140705790795 := by
  unfold tailWord_3962175
  simp only [CollatzResearch.WordTrace]
  refine ⟨144512394420724135461415979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96341596280482756974277319 144512394420724135461415979)
  ·
    refine ⟨216768591631086203192123969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144512394420724135461415979 216768591631086203192123969)
    ·
      refine ⟨162576443723314652394092977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216768591631086203192123969 162576443723314652394092977)
      ·
        refine ⟨121932332792485989295569733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162576443723314652394092977 121932332792485989295569733)
        ·
          refine ⟨22862312398591122992919325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121932332792485989295569733 22862312398591122992919325)
          ·
            refine ⟨8573367149471671122344747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22862312398591122992919325 8573367149471671122344747)
            ·
              refine ⟨12860050724207506683517121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573367149471671122344747 12860050724207506683517121)
              ·
                refine ⟨9645038043155630012637841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12860050724207506683517121 9645038043155630012637841)
                ·
                  refine ⟨7233778532366722509478381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9645038043155630012637841 7233778532366722509478381)
                  ·
                    refine ⟨2712666949637520941054393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7233778532366722509478381 2712666949637520941054393)
                    ·
                      refine ⟨2034500212228140705790795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712666949637520941054393 2034500212228140705790795)
                      ·
                        rfl

theorem cell23_3962175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_3962175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962175 prefixEnd_3962175 := by exact prefixLift 3962175
  have htrace : WordTrace (prefixWord ++ tailWord_3962175) baseStart_3962175 baseEnd_3962175 := by
    simpa [prefixWord, tailWord_3962175, baseEnd_3962175] using wordTrace_append hprefix tailTrace_3962175
  have hstable : (prefixWord ++ tailWord_3962175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962175).length < 2 ^ (prefixWord ++ tailWord_3962175).sum := by decide
  have hdescent : baseEnd_3962175 < baseStart_3962175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962189 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3962189 : Nat := 118140960795 + 3962189 * 2 ^ 59
def prefixEnd_3962189 : Nat := 4983230072969 + 3 ^ 40 * 3962189 * 2
def baseEnd_3962189 : Nat := 226056377884144850112859

theorem tailTrace_3962189 : CollatzResearch.WordTrace tailWord_3962189 prefixEnd_3962189 226056377884144850112859 := by
  unfold tailWord_3962189
  simp only [CollatzResearch.WordTrace]
  refine ⟨144512905042673415852425621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96341936695115610568283747 144512905042673415852425621)
  ·
    refine ⟨6774042423875316368082451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144512905042673415852425621 6774042423875316368082451)
    ·
      refine ⟨10161063635812974552123677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6774042423875316368082451 10161063635812974552123677)
      ·
        refine ⟨3810398863429865457046379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10161063635812974552123677 3810398863429865457046379)
        ·
          refine ⟨5715598295144798185569569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810398863429865457046379 5715598295144798185569569)
          ·
            refine ⟨4286698721358598639177177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5715598295144798185569569 4286698721358598639177177)
            ·
              refine ⟨3215024041018948979382883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4286698721358598639177177 3215024041018948979382883)
              ·
                refine ⟨4822536061528423469074325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215024041018948979382883 4822536061528423469074325)
                ·
                  refine ⟨226056377884144850112859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4822536061528423469074325 226056377884144850112859)
                  ·
                    rfl

theorem cell23_3962189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3962189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962189 prefixEnd_3962189 := by exact prefixLift 3962189
  have htrace : WordTrace (prefixWord ++ tailWord_3962189) baseStart_3962189 baseEnd_3962189 := by
    simpa [prefixWord, tailWord_3962189, baseEnd_3962189] using wordTrace_append hprefix tailTrace_3962189
  have hstable : (prefixWord ++ tailWord_3962189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962189).length < 2 ^ (prefixWord ++ tailWord_3962189).sum := by decide
  have hdescent : baseEnd_3962189 < baseStart_3962189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962201 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_3962201 : Nat := 118140960795 + 3962201 * 2 ^ 59
def prefixEnd_3962201 : Nat := 4983230072969 + 3 ^ 40 * 3962201 * 2
def baseEnd_3962201 : Nat := 2034513562725157604065675

theorem tailTrace_3962201 : CollatzResearch.WordTrace tailWord_3962201 prefixEnd_3962201 2034513562725157604065675 := by
  unfold tailWord_3962201
  simp only [CollatzResearch.WordTrace]
  refine ⟨144513342718629941901862457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96342228479086627934574971 144513342718629941901862457)
  ·
    refine ⟨108385007038972456426396843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144513342718629941901862457 108385007038972456426396843)
    ·
      refine ⟨162577510558458684639595265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108385007038972456426396843 162577510558458684639595265)
      ·
        refine ⟨121933132918844013479696449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162577510558458684639595265 121933132918844013479696449)
        ·
          refine ⟨91449849689133010109772337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121933132918844013479696449 91449849689133010109772337)
          ·
            refine ⟨68587387266849757582329253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91449849689133010109772337 68587387266849757582329253)
            ·
              refine ⟨12860135112534329546686735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68587387266849757582329253 12860135112534329546686735)
              ·
                refine ⟨19290202668801494320030103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12860135112534329546686735 19290202668801494320030103)
                ·
                  refine ⟨28935304003202241480045155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19290202668801494320030103 28935304003202241480045155)
                  ·
                    refine ⟨43402956004803362220067733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28935304003202241480045155 43402956004803362220067733)
                    ·
                      refine ⟨2034513562725157604065675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43402956004803362220067733 2034513562725157604065675)
                      ·
                        rfl

theorem cell23_3962201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_3962201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962201 prefixEnd_3962201 := by exact prefixLift 3962201
  have htrace : WordTrace (prefixWord ++ tailWord_3962201) baseStart_3962201 baseEnd_3962201 := by
    simpa [prefixWord, tailWord_3962201, baseEnd_3962201] using wordTrace_append hprefix tailTrace_3962201
  have hstable : (prefixWord ++ tailWord_3962201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962201).length < 2 ^ (prefixWord ++ tailWord_3962201).sum := by decide
  have hdescent : baseEnd_3962201 < baseStart_3962201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962211 : List Nat := [1, 1, 1, 5, 2, 2, 2, 9]
def baseStart_3962211 : Nat := 118140960795 + 3962211 * 2 ^ 59
def prefixEnd_3962211 : Nat := 4983230072969 + 3 ^ 40 * 3962211 * 2
def baseEnd_3962211 : Nat := 75352544353026020923727

theorem tailTrace_3962211 : CollatzResearch.WordTrace tailWord_3962211 prefixEnd_3962211 75352544353026020923727 := by
  unfold tailWord_3962211
  simp only [CollatzResearch.WordTrace]
  refine ⟨144513707448593713609726487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96342471632395809073150991 144513707448593713609726487)
  ·
    refine ⟨216770561172890570414589731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144513707448593713609726487 216770561172890570414589731)
    ·
      refine ⟨325155841759335855621884597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216770561172890570414589731 325155841759335855621884597)
      ·
        refine ⟨30483360164937736464551681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325155841759335855621884597 30483360164937736464551681)
        ·
          refine ⟨22862520123703302348413761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30483360164937736464551681 22862520123703302348413761)
          ·
            refine ⟨17146890092777476761310321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22862520123703302348413761 17146890092777476761310321)
            ·
              refine ⟨12860167569583107570982741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17146890092777476761310321 12860167569583107570982741)
              ·
                refine ⟨75352544353026020923727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12860167569583107570982741 75352544353026020923727)
                ·
                  rfl

theorem cell23_3962211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 9].length) (baseStart_3962211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962211 prefixEnd_3962211 := by exact prefixLift 3962211
  have htrace : WordTrace (prefixWord ++ tailWord_3962211) baseStart_3962211 baseEnd_3962211 := by
    simpa [prefixWord, tailWord_3962211, baseEnd_3962211] using wordTrace_append hprefix tailTrace_3962211
  have hstable : (prefixWord ++ tailWord_3962211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962211).length < 2 ^ (prefixWord ++ tailWord_3962211).sum := by decide
  have hdescent : baseEnd_3962211 < baseStart_3962211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962242 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3962242 : Nat := 118140960795 + 3962242 * 2 ^ 59
def prefixEnd_3962242 : Nat := 4983230072969 + 3 ^ 40 * 3962242 * 2
def baseEnd_3962242 : Nat := 2034534615431991943652987

theorem tailTrace_3962242 : CollatzResearch.WordTrace tailWord_3962242 prefixEnd_3962242 2034534615431991943652987 := by
  unfold tailWord_3962242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36128709527870351476026245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96343225407654270602736653 36128709527870351476026245)
  ·
    refine ⟨6774133036475690901754921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36128709527870351476026245 6774133036475690901754921)
    ·
      refine ⟨5080599777356768176316191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6774133036475690901754921 5080599777356768176316191)
      ·
        refine ⟨7620899666035152264474287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080599777356768176316191 7620899666035152264474287)
        ·
          refine ⟨11431349499052728396711431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620899666035152264474287 11431349499052728396711431)
          ·
            refine ⟨17147024248579092595067147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11431349499052728396711431 17147024248579092595067147)
            ·
              refine ⟨25720536372868638892600721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17147024248579092595067147 25720536372868638892600721)
              ·
                refine ⟨19290402279651479169450541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25720536372868638892600721 19290402279651479169450541)
                ·
                  refine ⟨7233900854869304688543953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19290402279651479169450541 7233900854869304688543953)
                  ·
                    refine ⟨5425425641151978516407965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7233900854869304688543953 5425425641151978516407965)
                    ·
                      refine ⟨2034534615431991943652987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425425641151978516407965 2034534615431991943652987)
                      ·
                        rfl

theorem cell23_3962242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3962242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962242 prefixEnd_3962242 := by exact prefixLift 3962242
  have htrace : WordTrace (prefixWord ++ tailWord_3962242) baseStart_3962242 baseEnd_3962242 := by
    simpa [prefixWord, tailWord_3962242, baseEnd_3962242] using wordTrace_append hprefix tailTrace_3962242
  have hstable : (prefixWord ++ tailWord_3962242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962242).length < 2 ^ (prefixWord ++ tailWord_3962242).sum := by decide
  have hdescent : baseEnd_3962242 < baseStart_3962242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962265 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 3, 3, 2]
def baseStart_3962265 : Nat := 118140960795 + 3962265 * 2 ^ 59
def prefixEnd_3962265 : Nat := 4983230072969 + 3 ^ 40 * 3962265 * 2
def baseEnd_3962265 : Nat := 2034546425487045353665381

theorem tailTrace_3962265 : CollatzResearch.WordTrace tailWord_3962265 prefixEnd_3962265 2034546425487045353665381 := by
  unfold tailWord_3962265
  simp only [CollatzResearch.WordTrace]
  refine ⟨144515676990398080832192249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96343784660265387221461499 144515676990398080832192249)
  ·
    refine ⟨108386757742798560624144187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144515676990398080832192249 108386757742798560624144187)
    ·
      refine ⟨162580136614197840936216281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108386757742798560624144187 162580136614197840936216281)
      ·
        refine ⟨121935102460648380702162211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162580136614197840936216281 121935102460648380702162211)
        ·
          refine ⟨182902653690972571053243317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121935102460648380702162211 182902653690972571053243317)
          ·
            refine ⟨17147123783528678536241561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182902653690972571053243317 17147123783528678536241561)
            ·
              refine ⟨12860342837646508902181171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17147123783528678536241561 12860342837646508902181171)
              ·
                refine ⟨19290514256469763353271757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12860342837646508902181171 19290514256469763353271757)
                ·
                  refine ⟨7233942846176161257476909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19290514256469763353271757 7233942846176161257476909)
                  ·
                    refine ⟨2712728567316060471553841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7233942846176161257476909 2712728567316060471553841)
                    ·
                      refine ⟨2034546425487045353665381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2712728567316060471553841 2034546425487045353665381)
                      ·
                        rfl

theorem cell23_3962265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_3962265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962265 prefixEnd_3962265 := by exact prefixLift 3962265
  have htrace : WordTrace (prefixWord ++ tailWord_3962265) baseStart_3962265 baseEnd_3962265 := by
    simpa [prefixWord, tailWord_3962265, baseEnd_3962265] using wordTrace_append hprefix tailTrace_3962265
  have hstable : (prefixWord ++ tailWord_3962265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962265).length < 2 ^ (prefixWord ++ tailWord_3962265).sum := by decide
  have hdescent : baseEnd_3962265 < baseStart_3962265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962318 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_3962318 : Nat := 118140960795 + 3962318 * 2 ^ 59
def prefixEnd_3962318 : Nat := 4983230072969 + 3 ^ 40 * 3962318 * 2
def baseEnd_3962318 : Nat := 226063737773525960700293

theorem tailTrace_3962318 : CollatzResearch.WordTrace tailWord_3962318 prefixEnd_3962318 226063737773525960700293 := by
  unfold tailWord_3962318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18064701257400758860483951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96345073372804047255914405 18064701257400758860483951)
  ·
    refine ⟨27097051886101138290725927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18064701257400758860483951 27097051886101138290725927)
    ·
      refine ⟨40645577829151707436088891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27097051886101138290725927 40645577829151707436088891)
      ·
        refine ⟨60968366743727561154133337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40645577829151707436088891 60968366743727561154133337)
        ·
          refine ⟨45726275057795670865600003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60968366743727561154133337 45726275057795670865600003)
          ·
            refine ⟨68589412586693506298400005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45726275057795670865600003 68589412586693506298400005)
            ·
              refine ⟨12860514860005032430950001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68589412586693506298400005 12860514860005032430950001)
              ·
                refine ⟨9645386145003774323212501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12860514860005032430950001 9645386145003774323212501)
                ·
                  refine ⟨226063737773525960700293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9645386145003774323212501 226063737773525960700293)
                  ·
                    rfl

theorem cell23_3962318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_3962318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962318 prefixEnd_3962318 := by exact prefixLift 3962318
  have htrace : WordTrace (prefixWord ++ tailWord_3962318) baseStart_3962318 baseEnd_3962318 := by
    simpa [prefixWord, tailWord_3962318, baseEnd_3962318] using wordTrace_append hprefix tailTrace_3962318
  have hstable : (prefixWord ++ tailWord_3962318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962318).length < 2 ^ (prefixWord ++ tailWord_3962318).sum := by decide
  have hdescent : baseEnd_3962318 < baseStart_3962318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962328 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_3962328 : Nat := 118140960795 + 3962328 * 2 ^ 59
def prefixEnd_3962328 : Nat := 4983230072969 + 3 ^ 40 * 3962328 * 2
def baseEnd_3962328 : Nat := 2034578774768278607177591

theorem tailTrace_3962328 : CollatzResearch.WordTrace tailWord_3962328 prefixEnd_3962328 2034578774768278607177591 := by
  unfold tailWord_3962328
  simp only [CollatzResearch.WordTrace]
  refine ⟨72258987394584921295867819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96345316526113228394490425 72258987394584921295867819)
  ·
    refine ⟨108388481091877381943801729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72258987394584921295867819 108388481091877381943801729)
    ·
      refine ⟨81291360818908036457851297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108388481091877381943801729 81291360818908036457851297)
      ·
        refine ⟨60968520614181027343388473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81291360818908036457851297 60968520614181027343388473)
        ·
          refine ⟨45726390460635770507541355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60968520614181027343388473 45726390460635770507541355)
          ·
            refine ⟨68589585690953655761312033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45726390460635770507541355 68589585690953655761312033)
            ·
              refine ⟨51442189268215241820984025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68589585690953655761312033 51442189268215241820984025)
              ·
                refine ⟨38581641951161431365738019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51442189268215241820984025 38581641951161431365738019)
                ·
                  refine ⟨57872462926742147048607029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38581641951161431365738019 57872462926742147048607029)
                  ·
                    refine ⟨5425543399382076285806909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57872462926742147048607029 5425543399382076285806909)
                    ·
                      refine ⟨2034578774768278607177591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425543399382076285806909 2034578774768278607177591)
                      ·
                        rfl

theorem cell23_3962328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_3962328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962328 prefixEnd_3962328 := by exact prefixLift 3962328
  have htrace : WordTrace (prefixWord ++ tailWord_3962328) baseStart_3962328 baseEnd_3962328 := by
    simpa [prefixWord, tailWord_3962328, baseEnd_3962328] using wordTrace_append hprefix tailTrace_3962328
  have hstable : (prefixWord ++ tailWord_3962328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962328).length < 2 ^ (prefixWord ++ tailWord_3962328).sum := by decide
  have hdescent : baseEnd_3962328 < baseStart_3962328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962352 : List Nat := [2, 1, 1, 1, 3, 5, 3, 2, 5]
def baseStart_3962352 : Nat := 118140960795 + 3962352 * 2 ^ 59
def prefixEnd_3962352 : Nat := 4983230072969 + 3 ^ 40 * 3962352 * 2
def baseEnd_3962352 : Nat := 226065677589331834808609

theorem tailTrace_3962352 : CollatzResearch.WordTrace tailWord_3962352 prefixEnd_3962352 226065677589331834808609 := by
  unfold tailWord_3962352
  simp only [CollatzResearch.WordTrace]
  refine ⟨72259425070541447345304655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96345900094055263127072873 72259425070541447345304655)
  ·
    refine ⟨108389137605812171017956983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72259425070541447345304655 108389137605812171017956983)
    ·
      refine ⟨162583706408718256526935475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108389137605812171017956983 162583706408718256526935475)
      ·
        refine ⟨243875559613077384790403213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162583706408718256526935475 243875559613077384790403213)
        ·
          refine ⟨91453334854904019296401205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243875559613077384790403213 91453334854904019296401205)
          ·
            refine ⟨8573750142647251809037613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91453334854904019296401205 8573750142647251809037613)
            ·
              refine ⟨3215156303492719428389105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8573750142647251809037613 3215156303492719428389105)
              ·
                refine ⟨2411367227619539571291829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215156303492719428389105 2411367227619539571291829)
                ·
                  refine ⟨226065677589331834808609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2411367227619539571291829 226065677589331834808609)
                  ·
                    rfl

theorem cell23_3962352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 5].length) (baseStart_3962352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962352 prefixEnd_3962352 := by exact prefixLift 3962352
  have htrace : WordTrace (prefixWord ++ tailWord_3962352) baseStart_3962352 baseEnd_3962352 := by
    simpa [prefixWord, tailWord_3962352, baseEnd_3962352] using wordTrace_append hprefix tailTrace_3962352
  have hstable : (prefixWord ++ tailWord_3962352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962352).length < 2 ^ (prefixWord ++ tailWord_3962352).sum := by decide
  have hdescent : baseEnd_3962352 < baseStart_3962352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962382 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3962382 : Nat := 118140960795 + 3962382 * 2 ^ 59
def prefixEnd_3962382 : Nat := 4983230072969 + 3 ^ 40 * 3962382 * 2
def baseEnd_3962382 : Nat := 678202167574540465300781

theorem tailTrace_3962382 : CollatzResearch.WordTrace tailWord_3962382 prefixEnd_3962382 678202167574540465300781 := by
  unfold tailWord_3962382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18064993041371776226775175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96346629553982806542800933 18064993041371776226775175)
  ·
    refine ⟨27097489562057664340162763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18064993041371776226775175 27097489562057664340162763)
    ·
      refine ⟨40646234343086496510244145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27097489562057664340162763 40646234343086496510244145)
      ·
        refine ⟨30484675757314872382683109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40646234343086496510244145 30484675757314872382683109)
        ·
          refine ⟨5715876704496538571753083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30484675757314872382683109 5715876704496538571753083)
          ·
            refine ⟨8573815056744807857629625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715876704496538571753083 8573815056744807857629625)
            ·
              refine ⟨6430361292558605893222219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8573815056744807857629625 6430361292558605893222219)
              ·
                refine ⟨9645541938837908839833329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430361292558605893222219 9645541938837908839833329)
                ·
                  refine ⟨7234156454128431629874997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9645541938837908839833329 7234156454128431629874997)
                  ·
                    refine ⟨678202167574540465300781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7234156454128431629874997 678202167574540465300781)
                    ·
                      rfl

theorem cell23_3962382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3962382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962382 prefixEnd_3962382 := by exact prefixLift 3962382
  have htrace : WordTrace (prefixWord ++ tailWord_3962382) baseStart_3962382 baseEnd_3962382 := by
    simpa [prefixWord, tailWord_3962382, baseEnd_3962382] using wordTrace_append hprefix tailTrace_3962382
  have hstable : (prefixWord ++ tailWord_3962382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962382).length < 2 ^ (prefixWord ++ tailWord_3962382).sum := by decide
  have hdescent : baseEnd_3962382 < baseStart_3962382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962385 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_3962385 : Nat := 118140960795 + 3962385 * 2 ^ 59
def prefixEnd_3962385 : Nat := 4983230072969 + 3 ^ 40 * 3962385 * 2
def baseEnd_3962385 : Nat := 2034608043165584884164829

theorem tailTrace_3962385 : CollatzResearch.WordTrace tailWord_3962385 prefixEnd_3962385 2034608043165584884164829 := by
  unfold tailWord_3962385
  simp only [CollatzResearch.WordTrace]
  refine ⟨144520053749963341326560609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96346702499975560884373739 144520053749963341326560609)
  ·
    refine ⟨108390040312472505994920457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144520053749963341326560609 108390040312472505994920457)
    ·
      refine ⟨81292530234354379496190343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108390040312472505994920457 81292530234354379496190343)
      ·
        refine ⟨121938795351531569244285515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81292530234354379496190343 121938795351531569244285515)
        ·
          refine ⟨182908193027297353866428273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121938795351531569244285515 182908193027297353866428273)
          ·
            refine ⟨137181144770473015399821205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182908193027297353866428273 137181144770473015399821205)
            ·
              refine ⟨6430366161115922596866619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137181144770473015399821205 6430366161115922596866619)
              ·
                refine ⟨9645549241673883895299929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430366161115922596866619 9645549241673883895299929)
                ·
                  refine ⟨7234161931255412921474947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9645549241673883895299929 7234161931255412921474947)
                  ·
                    refine ⟨10851242896883119382212421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7234161931255412921474947 10851242896883119382212421)
                    ·
                      refine ⟨2034608043165584884164829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10851242896883119382212421 2034608043165584884164829)
                      ·
                        rfl

theorem cell23_3962385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_3962385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962385 prefixEnd_3962385 := by exact prefixLift 3962385
  have htrace : WordTrace (prefixWord ++ tailWord_3962385) baseStart_3962385 baseEnd_3962385 := by
    simpa [prefixWord, tailWord_3962385, baseEnd_3962385] using wordTrace_append hprefix tailTrace_3962385
  have hstable : (prefixWord ++ tailWord_3962385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962385).length < 2 ^ (prefixWord ++ tailWord_3962385).sum := by decide
  have hdescent : baseEnd_3962385 < baseStart_3962385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962425 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 6]
def baseStart_3962425 : Nat := 118140960795 + 3962425 * 2 ^ 59
def prefixEnd_3962425 : Nat := 4983230072969 + 3 ^ 40 * 3962425 * 2
def baseEnd_3962425 : Nat := 226069842487973858629405

theorem tailTrace_3962425 : CollatzResearch.WordTrace tailWord_3962425 prefixEnd_3962425 226069842487973858629405 := by
  unfold tailWord_3962425
  simp only [CollatzResearch.WordTrace]
  refine ⟨144521512669818428158016729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96347675113212285438677819 144521512669818428158016729)
  ·
    refine ⟨108391134502363821118512547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144521512669818428158016729 108391134502363821118512547)
    ·
      refine ⟨162586701753545731677768821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108391134502363821118512547 162586701753545731677768821)
      ·
        refine ⟨15242503289394912344790827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162586701753545731677768821 15242503289394912344790827)
        ·
          refine ⟨22863754934092368517186241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15242503289394912344790827 22863754934092368517186241)
          ·
            refine ⟨17147816200569276387889681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22863754934092368517186241 17147816200569276387889681)
            ·
              refine ⟨12860862150426957290917261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17147816200569276387889681 12860862150426957290917261)
              ·
                refine ⟨4822823306410108984093973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12860862150426957290917261 4822823306410108984093973)
                ·
                  refine ⟨226069842487973858629405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4822823306410108984093973 226069842487973858629405)
                  ·
                    rfl

theorem cell23_3962425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 6].length) (baseStart_3962425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962425 prefixEnd_3962425 := by exact prefixLift 3962425
  have htrace : WordTrace (prefixWord ++ tailWord_3962425) baseStart_3962425 baseEnd_3962425 := by
    simpa [prefixWord, tailWord_3962425, baseEnd_3962425] using wordTrace_append hprefix tailTrace_3962425
  have hstable : (prefixWord ++ tailWord_3962425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962425).length < 2 ^ (prefixWord ++ tailWord_3962425).sum := by decide
  have hdescent : baseEnd_3962425 < baseStart_3962425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962439 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_3962439 : Nat := 118140960795 + 3962439 * 2 ^ 59
def prefixEnd_3962439 : Nat := 4983230072969 + 3 ^ 40 * 3962439 * 2
def baseEnd_3962439 : Nat := 2034635771120927672889581

theorem tailTrace_3962439 : CollatzResearch.WordTrace tailWord_3962439 prefixEnd_3962439 2034635771120927672889581 := by
  unfold tailWord_3962439
  simp only [CollatzResearch.WordTrace]
  refine ⟨144522023291767708549026371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96348015527845139032684247 144522023291767708549026371)
  ·
    refine ⟨216783034937651562823539557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144522023291767708549026371 216783034937651562823539557)
    ·
      refine ⟨40646819050809668029413667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216783034937651562823539557 40646819050809668029413667)
      ·
        refine ⟨60970228576214502044120501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40646819050809668029413667 60970228576214502044120501)
        ·
          refine ⟨5715958929020109566636297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60970228576214502044120501 5715958929020109566636297)
          ·
            refine ⟨4286969196765082174977223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5715958929020109566636297 4286969196765082174977223)
            ·
              refine ⟨6430453795147623262465835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286969196765082174977223 6430453795147623262465835)
              ·
                refine ⟨9645680692721434893698753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430453795147623262465835 9645680692721434893698753)
                ·
                  refine ⟨7234260519541076170274065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9645680692721434893698753 7234260519541076170274065)
                  ·
                    refine ⟨5425695389655807127705549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7234260519541076170274065 5425695389655807127705549)
                    ·
                      refine ⟨2034635771120927672889581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425695389655807127705549 2034635771120927672889581)
                      ·
                        rfl

theorem cell23_3962439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_3962439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962439 prefixEnd_3962439 := by exact prefixLift 3962439
  have htrace : WordTrace (prefixWord ++ tailWord_3962439) baseStart_3962439 baseEnd_3962439 := by
    simpa [prefixWord, tailWord_3962439, baseEnd_3962439] using wordTrace_append hprefix tailTrace_3962439
  have hstable : (prefixWord ++ tailWord_3962439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962439).length < 2 ^ (prefixWord ++ tailWord_3962439).sum := by decide
  have hdescent : baseEnd_3962439 < baseStart_3962439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962452 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_3962452 : Nat := 118140960795 + 3962452 * 2 ^ 59
def prefixEnd_3962452 : Nat := 4983230072969 + 3 ^ 40 * 3962452 * 2
def baseEnd_3962452 : Nat := 2034642446369436122027021

theorem tailTrace_3962452 : CollatzResearch.WordTrace tailWord_3962452 prefixEnd_3962452 2034642446369436122027021 := by
  unfold tailWord_3962452
  simp only [CollatzResearch.WordTrace]
  refine ⟨72261248720360305884624805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96348331627147074512833073 72261248720360305884624805)
  ·
    refine ⟨13548984135067557353367151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72261248720360305884624805 13548984135067557353367151)
    ·
      refine ⟨20323476202601336030050727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13548984135067557353367151 20323476202601336030050727)
      ·
        refine ⟨30485214303902004045076091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20323476202601336030050727 30485214303902004045076091)
        ·
          refine ⟨45727821455853006067614137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30485214303902004045076091 45727821455853006067614137)
          ·
            refine ⟨34295866091889754550710603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45727821455853006067614137 34295866091889754550710603)
            ·
              refine ⟨51443799137834631826065905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34295866091889754550710603 51443799137834631826065905)
              ·
                refine ⟨38582849353375973869549429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51443799137834631826065905 38582849353375973869549429)
                ·
                  refine ⟨3617142126878997550270259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38582849353375973869549429 3617142126878997550270259)
                  ·
                    refine ⟨5425713190318496325405389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3617142126878997550270259 5425713190318496325405389)
                    ·
                      refine ⟨2034642446369436122027021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425713190318496325405389 2034642446369436122027021)
                      ·
                        rfl

theorem cell23_3962452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_3962452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962452 prefixEnd_3962452 := by exact prefixLift 3962452
  have htrace : WordTrace (prefixWord ++ tailWord_3962452) baseStart_3962452 baseEnd_3962452 := by
    simpa [prefixWord, tailWord_3962452, baseEnd_3962452] using wordTrace_append hprefix tailTrace_3962452
  have hstable : (prefixWord ++ tailWord_3962452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962452).length < 2 ^ (prefixWord ++ tailWord_3962452).sum := by decide
  have hdescent : baseEnd_3962452 < baseStart_3962452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962469 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3962469 : Nat := 118140960795 + 3962469 * 2 ^ 59
def prefixEnd_3962469 : Nat := 4983230072969 + 3 ^ 40 * 3962469 * 2
def baseEnd_3962469 : Nat := 2034651175540562555514443

theorem tailTrace_3962469 : CollatzResearch.WordTrace tailWord_3962469 prefixEnd_3962469 2034651175540562555514443 := by
  unfold tailWord_3962469
  simp only [CollatzResearch.WordTrace]
  refine ⟨144523117481659023672618461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96348744987772682448412307 144523117481659023672618461)
  ·
    refine ⟨54196169055622133877231923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144523117481659023672618461 54196169055622133877231923)
    ·
      refine ⟨81294253583433200815847885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54196169055622133877231923 81294253583433200815847885)
      ·
        refine ⟨30485345093787450305942957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81294253583433200815847885 30485345093787450305942957)
        ·
          refine ⟨11432004410170293864728609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30485345093787450305942957 11432004410170293864728609)
          ·
            refine ⟨8574003307627720398546457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11432004410170293864728609 8574003307627720398546457)
            ·
              refine ⟨6430502480720790298909843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8574003307627720398546457 6430502480720790298909843)
              ·
                refine ⟨9645753721081185448364765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430502480720790298909843 9645753721081185448364765)
                ·
                  refine ⟨3617157645405444543136787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9645753721081185448364765 3617157645405444543136787)
                  ·
                    refine ⟨5425736468108166814705181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3617157645405444543136787 5425736468108166814705181)
                    ·
                      refine ⟨2034651175540562555514443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425736468108166814705181 2034651175540562555514443)
                      ·
                        rfl

theorem cell23_3962469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3962469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962469 prefixEnd_3962469 := by exact prefixLift 3962469
  have htrace : WordTrace (prefixWord ++ tailWord_3962469) baseStart_3962469 baseEnd_3962469 := by
    simpa [prefixWord, tailWord_3962469, baseEnd_3962469] using wordTrace_append hprefix tailTrace_3962469
  have hstable : (prefixWord ++ tailWord_3962469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962469).length < 2 ^ (prefixWord ++ tailWord_3962469).sum := by decide
  have hdescent : baseEnd_3962469 < baseStart_3962469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962495 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 3]
def baseStart_3962495 : Nat := 118140960795 + 3962495 * 2 ^ 59
def prefixEnd_3962495 : Nat := 4983230072969 + 3 ^ 40 * 3962495 * 2
def baseEnd_3962495 : Nat := 2034664526037579453789323

theorem tailTrace_3962495 : CollatzResearch.WordTrace tailWord_3962495 prefixEnd_3962495 2034664526037579453789323 := by
  unfold tailWord_3962495
  simp only [CollatzResearch.WordTrace]
  refine ⟨144524065779564830113064939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96349377186376553408709959 144524065779564830113064939)
  ·
    refine ⟨216786098669347245169597409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144524065779564830113064939 216786098669347245169597409)
    ·
      refine ⟨162589574002010433877198057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216786098669347245169597409 162589574002010433877198057)
      ·
        refine ⟨121942180501507825407898543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162589574002010433877198057 121942180501507825407898543)
        ·
          refine ⟨182913270752261738111847815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121942180501507825407898543 182913270752261738111847815)
          ·
            refine ⟨274369906128392607167771723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182913270752261738111847815 274369906128392607167771723)
            ·
              refine ⟨411554859192588910751657585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274369906128392607167771723 411554859192588910751657585)
              ·
                refine ⟨308666144394441683063743189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411554859192588910751657585 308666144394441683063743189)
                ·
                  refine ⟨7234362759244726946806481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 308666144394441683063743189 7234362759244726946806481)
                  ·
                    refine ⟨5425772069433545210104861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7234362759244726946806481 5425772069433545210104861)
                    ·
                      refine ⟨2034664526037579453789323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425772069433545210104861 2034664526037579453789323)
                      ·
                        rfl

theorem cell23_3962495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_3962495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962495 prefixEnd_3962495 := by exact prefixLift 3962495
  have htrace : WordTrace (prefixWord ++ tailWord_3962495) baseStart_3962495 baseEnd_3962495 := by
    simpa [prefixWord, tailWord_3962495, baseEnd_3962495] using wordTrace_append hprefix tailTrace_3962495
  have hstable : (prefixWord ++ tailWord_3962495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962495).length < 2 ^ (prefixWord ++ tailWord_3962495).sum := by decide
  have hdescent : baseEnd_3962495 < baseStart_3962495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962505 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_3962505 : Nat := 118140960795 + 3962505 * 2 ^ 59
def prefixEnd_3962505 : Nat := 4983230072969 + 3 ^ 40 * 3962505 * 2
def baseEnd_3962505 : Nat := 2034669660844124414664277

theorem tailTrace_3962505 : CollatzResearch.WordTrace tailWord_3962505 prefixEnd_3962505 2034669660844124414664277 := by
  unfold tailWord_3962505
  simp only [CollatzResearch.WordTrace]
  refine ⟨144524430509528601820928969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96349620339685734547285979 144524430509528601820928969)
  ·
    refine ⟨108393322882146451365696727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144524430509528601820928969 108393322882146451365696727)
    ·
      refine ⟨162589984323219677048545091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108393322882146451365696727 162589984323219677048545091)
      ·
        refine ⟨243884976484829515572817637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162589984323219677048545091 243884976484829515572817637)
        ·
          refine ⟨45728433090905534169903307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243884976484829515572817637 45728433090905534169903307)
          ·
            refine ⟨68592649636358301254854961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45728433090905534169903307 68592649636358301254854961)
            ·
              refine ⟨51444487227268725941141221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68592649636358301254854961 51444487227268725941141221)
              ·
                refine ⟨9645841355112886113963979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51444487227268725941141221 9645841355112886113963979)
                ·
                  refine ⟨14468762032669329170945969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9645841355112886113963979 14468762032669329170945969)
                  ·
                    refine ⟨10851571524501996878209477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14468762032669329170945969 10851571524501996878209477)
                    ·
                      refine ⟨2034669660844124414664277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10851571524501996878209477 2034669660844124414664277)
                      ·
                        rfl

theorem cell23_3962505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_3962505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962505 prefixEnd_3962505 := by exact prefixLift 3962505
  have htrace : WordTrace (prefixWord ++ tailWord_3962505) baseStart_3962505 baseEnd_3962505 := by
    simpa [prefixWord, tailWord_3962505, baseEnd_3962505] using wordTrace_append hprefix tailTrace_3962505
  have hstable : (prefixWord ++ tailWord_3962505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962505).length < 2 ^ (prefixWord ++ tailWord_3962505).sum := by decide
  have hdescent : baseEnd_3962505 < baseStart_3962505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962632 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_3962632 : Nat := 118140960795 + 3962632 * 2 ^ 59
def prefixEnd_3962632 : Nat := 4983230072969 + 3 ^ 40 * 3962632 * 2
def baseEnd_3962632 : Nat := 2034734872887245417776193

theorem tailTrace_3962632 : CollatzResearch.WordTrace tailWord_3962632 prefixEnd_3962632 2034734872887245417776193 := by
  unfold tailWord_3962632
  simp only [CollatzResearch.WordTrace]
  refine ⟨72264531290034251255401075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96352708386712335007201433 72264531290034251255401075)
  ·
    refine ⟨108396796935051376883101613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72264531290034251255401075 108396796935051376883101613)
    ·
      refine ⟨40648798850644266331163105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108396796935051376883101613 40648798850644266331163105)
      ·
        refine ⟨30486599137983199748372329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40648798850644266331163105 30486599137983199748372329)
        ·
          refine ⟨22864949353487399811279247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30486599137983199748372329 22864949353487399811279247)
          ·
            refine ⟨34297424030231099716918871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22864949353487399811279247 34297424030231099716918871)
            ·
              refine ⟨51446136045346649575378307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34297424030231099716918871 51446136045346649575378307)
              ·
                refine ⟨77169204068019974363067461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51446136045346649575378307 77169204068019974363067461)
                ·
                  refine ⟨14469225762753745193075149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77169204068019974363067461 14469225762753745193075149)
                  ·
                    refine ⟨5425959661032654447403181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14469225762753745193075149 5425959661032654447403181)
                    ·
                      refine ⟨2034734872887245417776193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5425959661032654447403181 2034734872887245417776193)
                      ·
                        rfl

theorem cell23_3962632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_3962632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962632 prefixEnd_3962632 := by exact prefixLift 3962632
  have htrace : WordTrace (prefixWord ++ tailWord_3962632) baseStart_3962632 baseEnd_3962632 := by
    simpa [prefixWord, tailWord_3962632, baseEnd_3962632] using wordTrace_append hprefix tailTrace_3962632
  have hstable : (prefixWord ++ tailWord_3962632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962632).length < 2 ^ (prefixWord ++ tailWord_3962632).sum := by decide
  have hdescent : baseEnd_3962632 < baseStart_3962632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962749 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_3962749 : Nat := 118140960795 + 3962749 * 2 ^ 59
def prefixEnd_3962749 : Nat := 4983230072969 + 3 ^ 40 * 3962749 * 2
def baseEnd_3962749 : Nat := 2034794950123821460013155

theorem tailTrace_3962749 : CollatzResearch.WordTrace tailWord_3962749 prefixEnd_3962749 2034794950123821460013155 := by
  unfold tailWord_3962749
  simp only [CollatzResearch.WordTrace]
  refine ⟨144533329920644631492811301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96355553280429754328540867 144533329920644631492811301)
  ·
    refine ⟨27099999360120868404902119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144533329920644631492811301 27099999360120868404902119)
    ·
      refine ⟨40649999040181302607353179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27099999360120868404902119 40649999040181302607353179)
      ·
        refine ⟨60974998560271953911029769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40649999040181302607353179 60974998560271953911029769)
        ·
          refine ⟨45731248920203965433272327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60974998560271953911029769 45731248920203965433272327)
          ·
            refine ⟨68596873380305948149908491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45731248920203965433272327 68596873380305948149908491)
            ·
              refine ⟨102895310070458922224862737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68596873380305948149908491 102895310070458922224862737)
              ·
                refine ⟨77171482552844191668647053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102895310070458922224862737 77171482552844191668647053)
                ·
                  refine ⟨28939305957316571875742645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77171482552844191668647053 28939305957316571875742645)
                  ·
                    refine ⟨2713059933498428613350873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28939305957316571875742645 2713059933498428613350873)
                    ·
                      refine ⟨2034794950123821460013155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713059933498428613350873 2034794950123821460013155)
                      ·
                        rfl

theorem cell23_3962749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_3962749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962749 prefixEnd_3962749 := by exact prefixLift 3962749
  have htrace : WordTrace (prefixWord ++ tailWord_3962749) baseStart_3962749 baseEnd_3962749 := by
    simpa [prefixWord, tailWord_3962749, baseEnd_3962749] using wordTrace_append hprefix tailTrace_3962749
  have hstable : (prefixWord ++ tailWord_3962749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962749).length < 2 ^ (prefixWord ++ tailWord_3962749).sum := by decide
  have hdescent : baseEnd_3962749 < baseStart_3962749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962750 : List Nat := [4, 2, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3962750 : Nat := 118140960795 + 3962750 * 2 ^ 59
def prefixEnd_3962750 : Nat := 4983230072969 + 3 ^ 40 * 3962750 * 2
def baseEnd_3962750 : Nat := 678265154534825318700217

theorem tailTrace_3962750 : CollatzResearch.WordTrace tailWord_3962750 prefixEnd_3962750 678265154534825318700217 := by
  unfold tailWord_3962750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066670799205126082949713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96355577595760672442398469 18066670799205126082949713)
  ·
    refine ⟨13550003099403844562212285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18066670799205126082949713 13550003099403844562212285)
    ·
      refine ⟨5081251162276441710829607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13550003099403844562212285 5081251162276441710829607)
      ·
        refine ⟨7621876743414662566244411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081251162276441710829607 7621876743414662566244411)
        ·
          refine ⟨11432815115121993849366617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7621876743414662566244411 11432815115121993849366617)
          ·
            refine ⟨8574611336341495387024963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11432815115121993849366617 8574611336341495387024963)
            ·
              refine ⟨12861917004512243080537445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574611336341495387024963 12861917004512243080537445)
              ·
                refine ⟨2411609438346045577600771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12861917004512243080537445 2411609438346045577600771)
                ·
                  refine ⟨3617414157519068366401157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411609438346045577600771 3617414157519068366401157)
                  ·
                    refine ⟨678265154534825318700217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3617414157519068366401157 678265154534825318700217)
                    ·
                      rfl

theorem cell23_3962750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3962750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962750 prefixEnd_3962750 := by exact prefixLift 3962750
  have htrace : WordTrace (prefixWord ++ tailWord_3962750) baseStart_3962750 baseEnd_3962750 := by
    simpa [prefixWord, tailWord_3962750, baseEnd_3962750] using wordTrace_append hprefix tailTrace_3962750
  have hstable : (prefixWord ++ tailWord_3962750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962750).length < 2 ^ (prefixWord ++ tailWord_3962750).sum := by decide
  have hdescent : baseEnd_3962750 < baseStart_3962750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962813 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_3962813 : Nat := 118140960795 + 3962813 * 2 ^ 59
def prefixEnd_3962813 : Nat := 4983230072969 + 3 ^ 40 * 3962813 * 2
def baseEnd_3962813 : Nat := 2034827812885709209612861

theorem tailTrace_3962813 : CollatzResearch.WordTrace tailWord_3962813 prefixEnd_3962813 2034827812885709209612861 := by
  unfold tailWord_3962813
  simp only [CollatzResearch.WordTrace]
  refine ⟨144535664192412770423141093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96357109461608513615427395 144535664192412770423141093)
  ·
    refine ⟨27100437036077394454338955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144535664192412770423141093 27100437036077394454338955)
    ·
      refine ⟨40650655554116091681508433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27100437036077394454338955 40650655554116091681508433)
      ·
        refine ⟨30487991665587068761131325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40650655554116091681508433 30487991665587068761131325)
        ·
          refine ⟨11432996874595150785424247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30487991665587068761131325 11432996874595150785424247)
          ·
            refine ⟨17149495311892726178136371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11432996874595150785424247 17149495311892726178136371)
            ·
              refine ⟨25724242967839089267204557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17149495311892726178136371 25724242967839089267204557)
              ·
                refine ⟨9646591112939658475201709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25724242967839089267204557 9646591112939658475201709)
                ·
                  refine ⟨3617471667352371928200641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9646591112939658475201709 3617471667352371928200641)
                  ·
                    refine ⟨2713103750514278946150481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3617471667352371928200641 2713103750514278946150481)
                    ·
                      refine ⟨2034827812885709209612861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713103750514278946150481 2034827812885709209612861)
                      ·
                        rfl

theorem cell23_3962813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_3962813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962813 prefixEnd_3962813 := by exact prefixLift 3962813
  have htrace : WordTrace (prefixWord ++ tailWord_3962813) baseStart_3962813 baseEnd_3962813 := by
    simpa [prefixWord, tailWord_3962813, baseEnd_3962813] using wordTrace_append hprefix tailTrace_3962813
  have hstable : (prefixWord ++ tailWord_3962813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962813).length < 2 ^ (prefixWord ++ tailWord_3962813).sum := by decide
  have hdescent : baseEnd_3962813 < baseStart_3962813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962832 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 2, 7]
def baseStart_3962832 : Nat := 118140960795 + 3962832 * 2 ^ 59
def prefixEnd_3962832 : Nat := 4983230072969 + 3 ^ 40 * 3962832 * 2
def baseEnd_3962832 : Nat := 678279189672714878425091

theorem tailTrace_3962832 : CollatzResearch.WordTrace tailWord_3962832 prefixEnd_3962832 678279189672714878425091 := by
  unfold tailWord_3962832
  simp only [CollatzResearch.WordTrace]
  refine ⟨72268178589671968334041375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96357571452895957778721833 72268178589671968334041375)
  ·
    refine ⟨108402267884507952501062063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72268178589671968334041375 108402267884507952501062063)
    ·
      refine ⟨162603401826761928751593095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108402267884507952501062063 162603401826761928751593095)
      ·
        refine ⟨243905102740142893127389643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162603401826761928751593095 243905102740142893127389643)
        ·
          refine ⟨365857654110214339691084465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243905102740142893127389643 365857654110214339691084465)
          ·
            refine ⟨274393240582660754768313349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365857654110214339691084465 274393240582660754768313349)
            ·
              refine ⟨51448732609248891519058753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274393240582660754768313349 51448732609248891519058753)
              ·
                refine ⟨38586549456936668639294065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51448732609248891519058753 38586549456936668639294065)
                ·
                  refine ⟨28939912092702501479470549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38586549456936668639294065 28939912092702501479470549)
                  ·
                    refine ⟨678279189672714878425091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28939912092702501479470549 678279189672714878425091)
                    ·
                      rfl

theorem cell23_3962832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_3962832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962832 prefixEnd_3962832 := by exact prefixLift 3962832
  have htrace : WordTrace (prefixWord ++ tailWord_3962832) baseStart_3962832 baseEnd_3962832 := by
    simpa [prefixWord, tailWord_3962832, baseEnd_3962832] using wordTrace_append hprefix tailTrace_3962832
  have hstable : (prefixWord ++ tailWord_3962832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962832).length < 2 ^ (prefixWord ++ tailWord_3962832).sum := by decide
  have hdescent : baseEnd_3962832 < baseStart_3962832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962847 : List Nat := [1, 1, 2, 3, 4, 3, 1, 3, 1, 2, 2]
def baseStart_3962847 : Nat := 118140960795 + 3962847 * 2 ^ 59
def prefixEnd_3962847 : Nat := 4983230072969 + 3 ^ 40 * 3962847 * 2
def baseEnd_3962847 : Nat := 2034845271227962076587705

theorem tailTrace_3962847 : CollatzResearch.WordTrace tailWord_3962847 prefixEnd_3962847 2034845271227962076587705 := by
  unfold tailWord_3962847
  simp only [CollatzResearch.WordTrace]
  refine ⟨144536904274289594229878795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96357936182859729486585863 144536904274289594229878795)
  ·
    refine ⟨216805356411434391344818193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144536904274289594229878795 216805356411434391344818193)
    ·
      refine ⟨162604017308575793508613645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216805356411434391344818193 162604017308575793508613645)
      ·
        refine ⟨60976506490715922565730117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162604017308575793508613645 60976506490715922565730117)
        ·
          refine ⟨11433094967009235481074397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60976506490715922565730117 11433094967009235481074397)
          ·
            refine ⟨4287410612628463305402899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11433094967009235481074397 4287410612628463305402899)
            ·
              refine ⟨6431115918942694958104349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287410612628463305402899 6431115918942694958104349)
              ·
                refine ⟨2411668469603510609289131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6431115918942694958104349 2411668469603510609289131)
                ·
                  refine ⟨3617502704405265913933697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411668469603510609289131 3617502704405265913933697)
                  ·
                    refine ⟨2713127028303949435450273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3617502704405265913933697 2713127028303949435450273)
                    ·
                      refine ⟨2034845271227962076587705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713127028303949435450273 2034845271227962076587705)
                      ·
                        rfl

theorem cell23_3962847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_3962847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962847 prefixEnd_3962847 := by exact prefixLift 3962847
  have htrace : WordTrace (prefixWord ++ tailWord_3962847) baseStart_3962847 baseEnd_3962847 := by
    simpa [prefixWord, tailWord_3962847, baseEnd_3962847] using wordTrace_append hprefix tailTrace_3962847
  have hstable : (prefixWord ++ tailWord_3962847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962847).length < 2 ^ (prefixWord ++ tailWord_3962847).sum := by decide
  have hdescent : baseEnd_3962847 < baseStart_3962847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962856 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_3962856 : Nat := 118140960795 + 3962856 * 2 ^ 59
def prefixEnd_3962856 : Nat := 4983230072969 + 3 ^ 40 * 3962856 * 2
def baseEnd_3962856 : Nat := 2034849892553852541375163

theorem tailTrace_3962856 : CollatzResearch.WordTrace tailWord_3962856 prefixEnd_3962856 2034849892553852541375163 := by
  unfold tailWord_3962856
  simp only [CollatzResearch.WordTrace]
  refine ⟨72268616265628494383478211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96358155020837992511304281 72268616265628494383478211)
  ·
    refine ⟨108402924398442741575217317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72268616265628494383478211 108402924398442741575217317)
    ·
      refine ⟨20325548324708014045353247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108402924398442741575217317 20325548324708014045353247)
      ·
        refine ⟨30488322487062021068029871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20325548324708014045353247 30488322487062021068029871)
        ·
          refine ⟨45732483730593031602044807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30488322487062021068029871 45732483730593031602044807)
          ·
            refine ⟨68598725595889547403067211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45732483730593031602044807 68598725595889547403067211)
            ·
              refine ⟨102898088393834321104600817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68598725595889547403067211 102898088393834321104600817)
              ·
                refine ⟨77173566295375740828450613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102898088393834321104600817 77173566295375740828450613)
                ·
                  refine ⟨7235021840191475702667245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77173566295375740828450613 7235021840191475702667245)
                  ·
                    refine ⟨2713133190071803388500217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7235021840191475702667245 2713133190071803388500217)
                    ·
                      refine ⟨2034849892553852541375163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713133190071803388500217 2034849892553852541375163)
                      ·
                        rfl

theorem cell23_3962856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_3962856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962856 prefixEnd_3962856 := by exact prefixLift 3962856
  have htrace : WordTrace (prefixWord ++ tailWord_3962856) baseStart_3962856 baseEnd_3962856 := by
    simpa [prefixWord, tailWord_3962856, baseEnd_3962856] using wordTrace_append hprefix tailTrace_3962856
  have hstable : (prefixWord ++ tailWord_3962856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962856).length < 2 ^ (prefixWord ++ tailWord_3962856).sum := by decide
  have hdescent : baseEnd_3962856 < baseStart_3962856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962956 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_3962956 : Nat := 118140960795 + 3962956 * 2 ^ 59
def prefixEnd_3962956 : Nat := 4983230072969 + 3 ^ 40 * 3962956 * 2
def baseEnd_3962956 : Nat := 678300413539767383374901

theorem tailTrace_3962956 : CollatzResearch.WordTrace tailWord_3962956 prefixEnd_3962956 678300413539767383374901 := by
  unfold tailWord_3962956
  simp only [CollatzResearch.WordTrace]
  refine ⟨72270439915447352922798361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96360586553929803897064481 72270439915447352922798361)
  ·
    refine ⟨54202829936585514692098771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72270439915447352922798361 54202829936585514692098771)
    ·
      refine ⟨81304244904878272038148157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54202829936585514692098771 81304244904878272038148157)
      ·
        refine ⟨30489091839329352014305559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81304244904878272038148157 30489091839329352014305559)
        ·
          refine ⟨45733637758994028021458339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30489091839329352014305559 45733637758994028021458339)
          ·
            refine ⟨68600456638491042032187509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45733637758994028021458339 68600456638491042032187509)
            ·
              refine ⟨6431292809858535190517579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68600456638491042032187509 6431292809858535190517579)
              ·
                refine ⟨9646939214787802785776369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6431292809858535190517579 9646939214787802785776369)
                ·
                  refine ⟨7235204411090852089332277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9646939214787802785776369 7235204411090852089332277)
                  ·
                    refine ⟨678300413539767383374901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7235204411090852089332277 678300413539767383374901)
                    ·
                      rfl

theorem cell23_3962956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_3962956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962956 prefixEnd_3962956 := by exact prefixLift 3962956
  have htrace : WordTrace (prefixWord ++ tailWord_3962956) baseStart_3962956 baseEnd_3962956 := by
    simpa [prefixWord, tailWord_3962956, baseEnd_3962956] using wordTrace_append hprefix tailTrace_3962956
  have hstable : (prefixWord ++ tailWord_3962956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962956).length < 2 ^ (prefixWord ++ tailWord_3962956).sum := by decide
  have hdescent : baseEnd_3962956 < baseStart_3962956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962959 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_3962959 : Nat := 118140960795 + 3962959 * 2 ^ 59
def prefixEnd_3962959 : Nat := 4983230072969 + 3 ^ 40 * 3962959 * 2
def baseEnd_3962959 : Nat := 2034902781061265638387189

theorem tailTrace_3962959 : CollatzResearch.WordTrace tailWord_3962959 prefixEnd_3962959 2034902781061265638387189 := by
  unfold tailWord_3962959
  simp only [CollatzResearch.WordTrace]
  refine ⟨144540989249883837357955931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96360659499922558238637287 144540989249883837357955931)
  ·
    refine ⟨216811483874825756036933897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144540989249883837357955931 216811483874825756036933897)
    ·
      refine ⟨162608612906119317027700423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216811483874825756036933897 162608612906119317027700423)
      ·
        refine ⟨243912919359178975541550635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162608612906119317027700423 243912919359178975541550635)
        ·
          refine ⟨365869379038768463312325953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243912919359178975541550635 365869379038768463312325953)
          ·
            refine ⟨274402034279076347484244465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365869379038768463312325953 274402034279076347484244465)
            ·
              refine ⟨205801525709307260613183349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274402034279076347484244465 205801525709307260613183349)
              ·
                refine ⟨19293893035247555682485939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205801525709307260613183349 19293893035247555682485939)
                ·
                  refine ⟨28940839552871333523728909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19293893035247555682485939 28940839552871333523728909)
                  ·
                    refine ⟨10852814832326750071398341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28940839552871333523728909 10852814832326750071398341)
                    ·
                      refine ⟨2034902781061265638387189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10852814832326750071398341 2034902781061265638387189)
                      ·
                        rfl

theorem cell23_3962959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_3962959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962959 prefixEnd_3962959 := by exact prefixLift 3962959
  have htrace : WordTrace (prefixWord ++ tailWord_3962959) baseStart_3962959 baseEnd_3962959 := by
    simpa [prefixWord, tailWord_3962959, baseEnd_3962959] using wordTrace_append hprefix tailTrace_3962959
  have hstable : (prefixWord ++ tailWord_3962959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962959).length < 2 ^ (prefixWord ++ tailWord_3962959).sum := by decide
  have hdescent : baseEnd_3962959 < baseStart_3962959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962979 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3962979 : Nat := 118140960795 + 3962979 * 2 ^ 59
def prefixEnd_3962979 : Nat := 4983230072969 + 3 ^ 40 * 3962979 * 2
def baseEnd_3962979 : Nat := 2034913050674355560137097

theorem tailTrace_3962979 : CollatzResearch.WordTrace tailWord_3962979 prefixEnd_3962979 2034913050674355560137097 := by
  unfold tailWord_3962979
  simp only [CollatzResearch.WordTrace]
  refine ⟨144541718709811380773683991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96361145806540920515789327 144541718709811380773683991)
  ·
    refine ⟨216812578064717071160525987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144541718709811380773683991 216812578064717071160525987)
    ·
      refine ⟨325218867097075606740788981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216812578064717071160525987 325218867097075606740788981)
      ·
        refine ⟨30489268790350838131948967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325218867097075606740788981 30489268790350838131948967)
        ·
          refine ⟨45733903185526257197923451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30489268790350838131948967 45733903185526257197923451)
          ·
            refine ⟨68600854778289385796885177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45733903185526257197923451 68600854778289385796885177)
            ·
              refine ⟨51450641083717039347663883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68600854778289385796885177 51450641083717039347663883)
              ·
                refine ⟨77175961625575559021495825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51450641083717039347663883 77175961625575559021495825)
                ·
                  refine ⟨57881971219181669266121869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77175961625575559021495825 57881971219181669266121869)
                  ·
                    refine ⟨21705739207193125974795701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57881971219181669266121869 21705739207193125974795701)
                    ·
                      refine ⟨2034913050674355560137097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21705739207193125974795701 2034913050674355560137097)
                      ·
                        rfl

theorem cell23_3962979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3962979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3962979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3962979 prefixEnd_3962979 := by exact prefixLift 3962979
  have htrace : WordTrace (prefixWord ++ tailWord_3962979) baseStart_3962979 baseEnd_3962979 := by
    simpa [prefixWord, tailWord_3962979, baseEnd_3962979] using wordTrace_append hprefix tailTrace_3962979
  have hstable : (prefixWord ++ tailWord_3962979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962979).length < 2 ^ (prefixWord ++ tailWord_3962979).sum := by decide
  have hdescent : baseEnd_3962979 < baseStart_3962979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963016 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 8]
def baseStart_3963016 : Nat := 118140960795 + 3963016 * 2 ^ 59
def prefixEnd_3963016 : Nat := 4983230072969 + 3 ^ 40 * 3963016 * 2
def baseEnd_3963016 : Nat := 226103561050952435041603

theorem tailTrace_3963016 : CollatzResearch.WordTrace tailWord_3963016 prefixEnd_3963016 226103561050952435041603 := by
  unfold tailWord_3963016
  simp only [CollatzResearch.WordTrace]
  refine ⟨72271534105338668046390451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96362045473784890728520601 72271534105338668046390451)
  ·
    refine ⟨108407301158008002069585677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72271534105338668046390451 108407301158008002069585677)
    ·
      refine ⟨40652737934253000776094629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108407301158008002069585677 40652737934253000776094629)
      ·
        refine ⟨7622388362672437645517743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40652737934253000776094629 7622388362672437645517743)
        ·
          refine ⟨11433582544008656468276615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622388362672437645517743 11433582544008656468276615)
          ·
            refine ⟨17150373816012984702414923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11433582544008656468276615 17150373816012984702414923)
            ·
              refine ⟨25725560724019477053622385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17150373816012984702414923 25725560724019477053622385)
              ·
                refine ⟨19294170543014607790216789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25725560724019477053622385 19294170543014607790216789)
                ·
                  refine ⟨226103561050952435041603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19294170543014607790216789 226103561050952435041603)
                  ·
                    rfl

theorem cell23_3963016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 8].length) (baseStart_3963016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963016 prefixEnd_3963016 := by exact prefixLift 3963016
  have htrace : WordTrace (prefixWord ++ tailWord_3963016) baseStart_3963016 baseEnd_3963016 := by
    simpa [prefixWord, tailWord_3963016, baseEnd_3963016] using wordTrace_append hprefix tailTrace_3963016
  have hstable : (prefixWord ++ tailWord_3963016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963016).length < 2 ^ (prefixWord ++ tailWord_3963016).sum := by decide
  have hdescent : baseEnd_3963016 < baseStart_3963016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963037 : List Nat := [1, 4, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3963037 : Nat := 118140960795 + 3963037 * 2 ^ 59
def prefixEnd_3963037 : Nat := 4983230072969 + 3 ^ 40 * 3963037 * 2
def baseEnd_3963037 : Nat := 678314277517438777737277

theorem tailTrace_3963037 : CollatzResearch.WordTrace tailWord_3963037 prefixEnd_3963037 678314277517438777737277 := by
  unfold tailWord_3963037
  simp only [CollatzResearch.WordTrace]
  refine ⟨144543834143601256679295365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96362556095734171119530243 144543834143601256679295365)
  ·
    refine ⟨27101968901925235627367881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144543834143601256679295365 27101968901925235627367881)
    ·
      refine ⟨20326476676443926720525911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27101968901925235627367881 20326476676443926720525911)
      ·
        refine ⟨30489715014665890080788867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20326476676443926720525911 30489715014665890080788867)
        ·
          refine ⟨45734572521998835121183301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30489715014665890080788867 45734572521998835121183301)
          ·
            refine ⟨8575232347874781585221869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45734572521998835121183301 8575232347874781585221869)
            ·
              refine ⟨3215712130453043094458201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8575232347874781585221869 3215712130453043094458201)
              ·
                refine ⟨2411784097839782320843651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215712130453043094458201 2411784097839782320843651)
                ·
                  refine ⟨3617676146759673481265477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411784097839782320843651 3617676146759673481265477)
                  ·
                    refine ⟨678314277517438777737277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3617676146759673481265477 678314277517438777737277)
                    ·
                      rfl

theorem cell23_3963037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3963037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963037 prefixEnd_3963037 := by exact prefixLift 3963037
  have htrace : WordTrace (prefixWord ++ tailWord_3963037) baseStart_3963037 baseEnd_3963037 := by
    simpa [prefixWord, tailWord_3963037, baseEnd_3963037] using wordTrace_append hprefix tailTrace_3963037
  have hstable : (prefixWord ++ tailWord_3963037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963037).length < 2 ^ (prefixWord ++ tailWord_3963037).sum := by decide
  have hdescent : baseEnd_3963037 < baseStart_3963037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963050 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 6]
def baseStart_3963050 : Nat := 118140960795 + 3963050 * 2 ^ 59
def prefixEnd_3963050 : Nat := 4983230072969 + 3 ^ 40 * 3963050 * 2
def baseEnd_3963050 : Nat := 226105500866758309149919

theorem tailTrace_3963050 : CollatzResearch.WordTrace tailWord_3963050 prefixEnd_3963050 226105500866758309149919 := by
  unfold tailWord_3963050
  simp only [CollatzResearch.WordTrace]
  refine ⟨36136077073138539974879651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96362872195036106599679069 36136077073138539974879651)
  ·
    refine ⟨54204115609707809962319477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36136077073138539974879651 54204115609707809962319477)
    ·
      refine ⟨5081635838410107183967451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54204115609707809962319477 5081635838410107183967451)
      ·
        refine ⟨7622453757615160775951177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081635838410107183967451 7622453757615160775951177)
        ·
          refine ⟨5716840318211370581963383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7622453757615160775951177 5716840318211370581963383)
          ·
            refine ⟨8575260477317055872945075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716840318211370581963383 8575260477317055872945075)
            ·
              refine ⟨12862890715975583809417613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575260477317055872945075 12862890715975583809417613)
              ·
                refine ⟨4823584018490843928531605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12862890715975583809417613 4823584018490843928531605)
                ·
                  refine ⟨226105500866758309149919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4823584018490843928531605 226105500866758309149919)
                  ·
                    rfl

theorem cell23_3963050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_3963050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963050 prefixEnd_3963050 := by exact prefixLift 3963050
  have htrace : WordTrace (prefixWord ++ tailWord_3963050) baseStart_3963050 baseEnd_3963050 := by
    simpa [prefixWord, tailWord_3963050, baseEnd_3963050] using wordTrace_append hprefix tailTrace_3963050
  have hstable : (prefixWord ++ tailWord_3963050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963050).length < 2 ^ (prefixWord ++ tailWord_3963050).sum := by decide
  have hdescent : baseEnd_3963050 < baseStart_3963050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963063 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 1, 5]
def baseStart_3963063 : Nat := 118140960795 + 3963063 * 2 ^ 59
def prefixEnd_3963063 : Nat := 4983230072969 + 3 ^ 40 * 3963063 * 2
def baseEnd_3963063 : Nat := 678318727683111077162237

theorem tailTrace_3963063 : CollatzResearch.WordTrace tailWord_3963063 prefixEnd_3963063 678318727683111077162237 := by
  unfold tailWord_3963063
  simp only [CollatzResearch.WordTrace]
  refine ⟨144544782441507063119741843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96363188294338042079827895 144544782441507063119741843)
  ·
    refine ⟨216817173662260594679612765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144544782441507063119741843 216817173662260594679612765)
    ·
      refine ⟨81306440123347723004854787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216817173662260594679612765 81306440123347723004854787)
      ·
        refine ⟨121959660185021584507282181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81306440123347723004854787 121959660185021584507282181)
        ·
          refine ⟨22867436284691547095115409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121959660185021584507282181 22867436284691547095115409)
          ·
            refine ⟨17150577213518660321336557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22867436284691547095115409 17150577213518660321336557)
            ·
              refine ⟨6431466455069497620501209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17150577213518660321336557 6431466455069497620501209)
              ·
                refine ⟨4823599841302123215375907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431466455069497620501209 4823599841302123215375907)
                ·
                  refine ⟨7235399761953184823063861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823599841302123215375907 7235399761953184823063861)
                  ·
                    refine ⟨678318727683111077162237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7235399761953184823063861 678318727683111077162237)
                    ·
                      rfl

theorem cell23_3963063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_3963063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963063 prefixEnd_3963063 := by exact prefixLift 3963063
  have htrace : WordTrace (prefixWord ++ tailWord_3963063) baseStart_3963063 baseEnd_3963063 := by
    simpa [prefixWord, tailWord_3963063, baseEnd_3963063] using wordTrace_append hprefix tailTrace_3963063
  have hstable : (prefixWord ++ tailWord_3963063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963063).length < 2 ^ (prefixWord ++ tailWord_3963063).sum := by decide
  have hdescent : baseEnd_3963063 < baseStart_3963063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963150 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3963150 : Nat := 118140960795 + 3963150 * 2 ^ 59
def prefixEnd_3963150 : Nat := 4983230072969 + 3 ^ 40 * 3963150 * 2
def baseEnd_3963150 : Nat := 2035000855866274391098811

theorem tailTrace_3963150 : CollatzResearch.WordTrace tailWord_3963150 prefixEnd_3963150 2035000855866274391098811 := by
  unfold tailWord_3963150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18068494449023984622269863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96365303728127917985439269 18068494449023984622269863)
  ·
    refine ⟨27102741673535976933404795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18068494449023984622269863 27102741673535976933404795)
    ·
      refine ⟨40654112510303965400107193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27102741673535976933404795 40654112510303965400107193)
      ·
        refine ⟨30490584382727974050080395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40654112510303965400107193 30490584382727974050080395)
        ·
          refine ⟨45735876574091961075120593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30490584382727974050080395 45735876574091961075120593)
          ·
            refine ⟨34301907430568970806340445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45735876574091961075120593 34301907430568970806340445)
            ·
              refine ⟨12863215286463364052377667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34301907430568970806340445 12863215286463364052377667)
              ·
                refine ⟨19294822929695046078566501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12863215286463364052377667 19294822929695046078566501)
                ·
                  refine ⟨3617779299317821139731219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19294822929695046078566501 3617779299317821139731219)
                  ·
                    refine ⟨5426668948976731709596829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3617779299317821139731219 5426668948976731709596829)
                    ·
                      refine ⟨2035000855866274391098811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5426668948976731709596829 2035000855866274391098811)
                      ·
                        rfl

theorem cell23_3963150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3963150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963150 prefixEnd_3963150 := by exact prefixLift 3963150
  have htrace : WordTrace (prefixWord ++ tailWord_3963150) baseStart_3963150 baseEnd_3963150 := by
    simpa [prefixWord, tailWord_3963150, baseEnd_3963150] using wordTrace_append hprefix tailTrace_3963150
  have hstable : (prefixWord ++ tailWord_3963150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963150).length < 2 ^ (prefixWord ++ tailWord_3963150).sum := by decide
  have hdescent : baseEnd_3963150 < baseStart_3963150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963193 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3963193 : Nat := 118140960795 + 3963193 * 2 ^ 59
def prefixEnd_3963193 : Nat := 4983230072969 + 3 ^ 40 * 3963193 * 2
def baseEnd_3963193 : Nat := 2035022935534417722861113

theorem tailTrace_3963193 : CollatzResearch.WordTrace tailWord_3963193 prefixEnd_3963193 2035022935534417722861113 := by
  unfold tailWord_3963193
  simp only [CollatzResearch.WordTrace]
  refine ⟨144549523931036095321974233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96366349287357396881316155 144549523931036095321974233)
  ·
    refine ⟨108412142948277071491480675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144549523931036095321974233 108412142948277071491480675)
    ·
      refine ⟨162618214422415607237221013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108412142948277071491480675 162618214422415607237221013)
      ·
        refine ⟨7622728801050731589244735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162618214422415607237221013 7622728801050731589244735)
        ·
          refine ⟨11434093201576097383867103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622728801050731589244735 11434093201576097383867103)
          ·
            refine ⟨17151139802364146075800655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11434093201576097383867103 17151139802364146075800655)
            ·
              refine ⟨25726709703546219113700983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17151139802364146075800655 25726709703546219113700983)
              ·
                refine ⟨38590064555319328670551475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25726709703546219113700983 38590064555319328670551475)
                ·
                  refine ⟨57885096832978993005827213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38590064555319328670551475 57885096832978993005827213)
                  ·
                    refine ⟨21706911312367122377185205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57885096832978993005827213 21706911312367122377185205)
                    ·
                      refine ⟨2035022935534417722861113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21706911312367122377185205 2035022935534417722861113)
                      ·
                        rfl

theorem cell23_3963193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3963193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963193 prefixEnd_3963193 := by exact prefixLift 3963193
  have htrace : WordTrace (prefixWord ++ tailWord_3963193) baseStart_3963193 baseEnd_3963193 := by
    simpa [prefixWord, tailWord_3963193, baseEnd_3963193] using wordTrace_append hprefix tailTrace_3963193
  have hstable : (prefixWord ++ tailWord_3963193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963193).length < 2 ^ (prefixWord ++ tailWord_3963193).sum := by decide
  have hdescent : baseEnd_3963193 < baseStart_3963193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963207 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_3963207 : Nat := 118140960795 + 3963207 * 2 ^ 59
def prefixEnd_3963207 : Nat := 4983230072969 + 3 ^ 40 * 3963207 * 2
def baseEnd_3963207 : Nat := 2035030124263580668086049

theorem tailTrace_3963207 : CollatzResearch.WordTrace tailWord_3963207 prefixEnd_3963207 2035030124263580668086049 := by
  unfold tailWord_3963207
  simp only [CollatzResearch.WordTrace]
  refine ⟨144550034552985375712983875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96366689701990250475322583 144550034552985375712983875)
  ·
    refine ⟨216825051829478063569475813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144550034552985375712983875 216825051829478063569475813)
    ·
      refine ⟨40654697218027136919276715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216825051829478063569475813 40654697218027136919276715)
      ·
        refine ⟨60982045827040705378915073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40654697218027136919276715 60982045827040705378915073)
        ·
          refine ⟨45736534370280529034186305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60982045827040705378915073 45736534370280529034186305)
          ·
            refine ⟨34302400777710396775639729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45736534370280529034186305 34302400777710396775639729)
            ·
              refine ⟨25726800583282797581729797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34302400777710396775639729 25726800583282797581729797)
              ·
                refine ⟨4823775109365524546574337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25726800583282797581729797 4823775109365524546574337)
                ·
                  refine ⟨3617831332024143409930753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4823775109365524546574337 3617831332024143409930753)
                  ·
                    refine ⟨2713373499018107557448065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3617831332024143409930753 2713373499018107557448065)
                    ·
                      refine ⟨2035030124263580668086049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713373499018107557448065 2035030124263580668086049)
                      ·
                        rfl

theorem cell23_3963207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_3963207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963207 prefixEnd_3963207 := by exact prefixLift 3963207
  have htrace : WordTrace (prefixWord ++ tailWord_3963207) baseStart_3963207 baseEnd_3963207 := by
    simpa [prefixWord, tailWord_3963207, baseEnd_3963207] using wordTrace_append hprefix tailTrace_3963207
  have hstable : (prefixWord ++ tailWord_3963207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963207).length < 2 ^ (prefixWord ++ tailWord_3963207).sum := by decide
  have hdescent : baseEnd_3963207 < baseStart_3963207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963223 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_3963223 : Nat := 118140960795 + 3963223 * 2 ^ 59
def prefixEnd_3963223 : Nat := 4983230072969 + 3 ^ 40 * 3963223 * 2
def baseEnd_3963223 : Nat := 2035038339954052605485975

theorem tailTrace_3963223 : CollatzResearch.WordTrace tailWord_3963223 prefixEnd_3963223 2035038339954052605485975 := by
  unfold tailWord_3963223
  simp only [CollatzResearch.WordTrace]
  refine ⟨144550618120927410445566323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96367078747284940297044215 144550618120927410445566323)
  ·
    refine ⟨216825927181391115668349485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144550618120927410445566323 216825927181391115668349485)
    ·
      refine ⟨81309722693021668375631057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216825927181391115668349485 81309722693021668375631057)
      ·
        refine ⟨60982292019766251281723293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81309722693021668375631057 60982292019766251281723293)
        ·
          refine ⟨22868359507412344230646235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60982292019766251281723293 22868359507412344230646235)
          ·
            refine ⟨34302539261118516345969353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22868359507412344230646235 34302539261118516345969353)
            ·
              refine ⟨25726904445838887259477015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34302539261118516345969353 25726904445838887259477015)
              ·
                refine ⟨38590356668758330889215523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25726904445838887259477015 38590356668758330889215523)
                ·
                  refine ⟨57885535003137496333823285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38590356668758330889215523 57885535003137496333823285)
                  ·
                    refine ⟨5426768906544140281295933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57885535003137496333823285 5426768906544140281295933)
                    ·
                      refine ⟨2035038339954052605485975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5426768906544140281295933 2035038339954052605485975)
                      ·
                        rfl

theorem cell23_3963223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_3963223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963223 prefixEnd_3963223 := by exact prefixLift 3963223
  have htrace : WordTrace (prefixWord ++ tailWord_3963223) baseStart_3963223 baseEnd_3963223 := by
    simpa [prefixWord, tailWord_3963223, baseEnd_3963223] using wordTrace_append hprefix tailTrace_3963223
  have hstable : (prefixWord ++ tailWord_3963223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963223).length < 2 ^ (prefixWord ++ tailWord_3963223).sum := by decide
  have hdescent : baseEnd_3963223 < baseStart_3963223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963228 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3963228 : Nat := 118140960795 + 3963228 * 2 ^ 59
def prefixEnd_3963228 : Nat := 4983230072969 + 3 ^ 40 * 3963228 * 2
def baseEnd_3963228 : Nat := 2035040907357325085923453

theorem tailTrace_3963228 : CollatzResearch.WordTrace tailWord_3963228 prefixEnd_3963228 2035040907357325085923453 := by
  unfold tailWord_3963228
  simp only [CollatzResearch.WordTrace]
  refine ⟨72275400242954648149749169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96367200323939530866332225 72275400242954648149749169)
  ·
    refine ⟨54206550182215986112311877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72275400242954648149749169 54206550182215986112311877)
    ·
      refine ⟨10163728159165497396058477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54206550182215986112311877 10163728159165497396058477)
      ·
        refine ⟨3811398059687061523521929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10163728159165497396058477 3811398059687061523521929)
        ·
          refine ⟨2858548544765296142641447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3811398059687061523521929 2858548544765296142641447)
          ·
            refine ⟨4287822817147944213962171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858548544765296142641447 4287822817147944213962171)
            ·
              refine ⟨6431734225721916320943257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287822817147944213962171 6431734225721916320943257)
              ·
                refine ⟨4823800669291437240707443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431734225721916320943257 4823800669291437240707443)
                ·
                  refine ⟨7235701003937155861061165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823800669291437240707443 7235701003937155861061165)
                  ·
                    refine ⟨2713387876476433447897937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7235701003937155861061165 2713387876476433447897937)
                    ·
                      refine ⟨2035040907357325085923453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713387876476433447897937 2035040907357325085923453)
                      ·
                        rfl

theorem cell23_3963228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3963228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963228 prefixEnd_3963228 := by exact prefixLift 3963228
  have htrace : WordTrace (prefixWord ++ tailWord_3963228) baseStart_3963228 baseEnd_3963228 := by
    simpa [prefixWord, tailWord_3963228, baseEnd_3963228] using wordTrace_append hprefix tailTrace_3963228
  have hstable : (prefixWord ++ tailWord_3963228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963228).length < 2 ^ (prefixWord ++ tailWord_3963228).sum := by decide
  have hdescent : baseEnd_3963228 < baseStart_3963228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963290 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_3963290 : Nat := 118140960795 + 3963290 * 2 ^ 59
def prefixEnd_3963290 : Nat := 4983230072969 + 3 ^ 40 * 3963290 * 2
def baseEnd_3963290 : Nat := 678357581052634614449389

theorem tailTrace_3963290 : CollatzResearch.WordTrace tailWord_3963290 prefixEnd_3963290 678357581052634614449389 := by
  unfold tailWord_3963290
  simp only [CollatzResearch.WordTrace]
  refine ⟨36138265452921170222063831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96368707874456453925503549 36138265452921170222063831)
  ·
    refine ⟨54207398179381755333095747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36138265452921170222063831 54207398179381755333095747)
    ·
      refine ⟨81311097269072632999643621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54207398179381755333095747 81311097269072632999643621)
      ·
        refine ⟨15245830737951118687433179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81311097269072632999643621 15245830737951118687433179)
        ·
          refine ⟨22868746106926678031149769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15245830737951118687433179 22868746106926678031149769)
          ·
            refine ⟨17151559580195008523362327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22868746106926678031149769 17151559580195008523362327)
            ·
              refine ⟨25727339370292512785043491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17151559580195008523362327 25727339370292512785043491)
              ·
                refine ⟨38591009055438769177565237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25727339370292512785043491 38591009055438769177565237)
                ·
                  refine ⟨3617907098947384610396741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38591009055438769177565237 3617907098947384610396741)
                  ·
                    refine ⟨678357581052634614449389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3617907098947384610396741 678357581052634614449389)
                    ·
                      rfl

theorem cell23_3963290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_3963290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963290 prefixEnd_3963290 := by exact prefixLift 3963290
  have htrace : WordTrace (prefixWord ++ tailWord_3963290) baseStart_3963290 baseEnd_3963290 := by
    simpa [prefixWord, tailWord_3963290, baseEnd_3963290] using wordTrace_append hprefix tailTrace_3963290
  have hstable : (prefixWord ++ tailWord_3963290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963290).length < 2 ^ (prefixWord ++ tailWord_3963290).sum := by decide
  have hdescent : baseEnd_3963290 < baseStart_3963290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963294 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3963294 : Nat := 118140960795 + 3963294 * 2 ^ 59
def prefixEnd_3963294 : Nat := 4983230072969 + 3 ^ 40 * 3963294 * 2
def baseEnd_3963294 : Nat := 678358265693507275899383

theorem tailTrace_3963294 : CollatzResearch.WordTrace tailWord_3963294 prefixEnd_3963294 678358265693507275899383 := by
  unfold tailWord_3963294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069150962958773696425117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96368805135780126380933957 18069150962958773696425117)
  ·
    refine ⟨6775931611109540136159419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18069150962958773696425117 6775931611109540136159419)
    ·
      refine ⟨10163897416664310204239129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775931611109540136159419 10163897416664310204239129)
      ·
        refine ⟨7622923062498232653179347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10163897416664310204239129 7622923062498232653179347)
        ·
          refine ⟨11434384593747348979769021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622923062498232653179347 11434384593747348979769021)
          ·
            refine ⟨4287894222655255867413383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11434384593747348979769021 4287894222655255867413383)
            ·
              refine ⟨6431841333982883801120075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287894222655255867413383 6431841333982883801120075)
              ·
                refine ⟨9647762000974325701680113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6431841333982883801120075 9647762000974325701680113)
                ·
                  refine ⟨7235821500730744276260085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9647762000974325701680113 7235821500730744276260085)
                  ·
                    refine ⟨678358265693507275899383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7235821500730744276260085 678358265693507275899383)
                    ·
                      rfl

theorem cell23_3963294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3963294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963294 prefixEnd_3963294 := by exact prefixLift 3963294
  have htrace : WordTrace (prefixWord ++ tailWord_3963294) baseStart_3963294 baseEnd_3963294 := by
    simpa [prefixWord, tailWord_3963294, baseEnd_3963294] using wordTrace_append hprefix tailTrace_3963294
  have hstable : (prefixWord ++ tailWord_3963294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963294).length < 2 ^ (prefixWord ++ tailWord_3963294).sum := by decide
  have hdescent : baseEnd_3963294 < baseStart_3963294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963297 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3963297 : Nat := 118140960795 + 3963297 * 2 ^ 59
def prefixEnd_3963297 : Nat := 4983230072969 + 3 ^ 40 * 3963297 * 2
def baseEnd_3963297 : Nat := 2035076337522485315960635

theorem tailTrace_3963297 : CollatzResearch.WordTrace tailWord_3963297 prefixEnd_3963297 2035076337522485315960635 := by
  unfold tailWord_3963297
  simp only [CollatzResearch.WordTrace]
  refine ⟨144553317122659321083760145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96368878081772880722506763 144553317122659321083760145)
  ·
    refine ⟨108414987841994490812820109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144553317122659321083760145 108414987841994490812820109)
    ·
      refine ⟨40655620440747934054807541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108414987841994490812820109 40655620440747934054807541)
      ·
        refine ⟨3811464416320118817638207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40655620440747934054807541 3811464416320118817638207)
        ·
          refine ⟨5717196624480178226457311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3811464416320118817638207 5717196624480178226457311)
          ·
            refine ⟨8575794936720267339685967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5717196624480178226457311 8575794936720267339685967)
            ·
              refine ⟨12863692405080401009528951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575794936720267339685967 12863692405080401009528951)
              ·
                refine ⟨19295538607620601514293427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12863692405080401009528951 19295538607620601514293427)
                ·
                  refine ⟨28943307911430902271440141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19295538607620601514293427 28943307911430902271440141)
                  ·
                    refine ⟨10853740466786588351790053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28943307911430902271440141 10853740466786588351790053)
                    ·
                      refine ⟨2035076337522485315960635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10853740466786588351790053 2035076337522485315960635)
                      ·
                        rfl

theorem cell23_3963297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3963297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963297 prefixEnd_3963297 := by exact prefixLift 3963297
  have htrace : WordTrace (prefixWord ++ tailWord_3963297) baseStart_3963297 baseEnd_3963297 := by
    simpa [prefixWord, tailWord_3963297, baseEnd_3963297] using wordTrace_append hprefix tailTrace_3963297
  have hstable : (prefixWord ++ tailWord_3963297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963297).length < 2 ^ (prefixWord ++ tailWord_3963297).sum := by decide
  have hdescent : baseEnd_3963297 < baseStart_3963297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963324 : List Nat := [2, 2, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_3963324 : Nat := 118140960795 + 3963324 * 2 ^ 59
def prefixEnd_3963324 : Nat := 4983230072969 + 3 ^ 40 * 3963324 * 2
def baseEnd_3963324 : Nat := 678363400500052236774337

theorem tailTrace_3963324 : CollatzResearch.WordTrace tailWord_3963324 prefixEnd_3963324 678363400500052236774337 := by
  unfold tailWord_3963324
  simp only [CollatzResearch.WordTrace]
  refine ⟨72277150946780752347496513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96369534595707669796662017 72277150946780752347496513)
  ·
    refine ⟨54207863210085564260622385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72277150946780752347496513 54207863210085564260622385)
    ·
      refine ⟨40655897407564173195466789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54207863210085564260622385 40655897407564173195466789)
      ·
        refine ⟨7622980763918282474150023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40655897407564173195466789 7622980763918282474150023)
        ·
          refine ⟨11434471145877423711225035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622980763918282474150023 11434471145877423711225035)
          ·
            refine ⟨17151706718816135566837553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11434471145877423711225035 17151706718816135566837553)
            ·
              refine ⟨12863780039112101675128165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17151706718816135566837553 12863780039112101675128165)
              ·
                refine ⟨2411958757333519064086531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12863780039112101675128165 2411958757333519064086531)
                ·
                  refine ⟨3617938136000278596129797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411958757333519064086531 3617938136000278596129797)
                  ·
                    refine ⟨678363400500052236774337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3617938136000278596129797 678363400500052236774337)
                    ·
                      rfl

theorem cell23_3963324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_3963324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963324 prefixEnd_3963324 := by exact prefixLift 3963324
  have htrace : WordTrace (prefixWord ++ tailWord_3963324) baseStart_3963324 baseEnd_3963324 := by
    simpa [prefixWord, tailWord_3963324, baseEnd_3963324] using wordTrace_append hprefix tailTrace_3963324
  have hstable : (prefixWord ++ tailWord_3963324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963324).length < 2 ^ (prefixWord ++ tailWord_3963324).sum := by decide
  have hdescent : baseEnd_3963324 < baseStart_3963324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963357 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3963357 : Nat := 118140960795 + 3963357 * 2 ^ 59
def prefixEnd_3963357 : Nat := 4983230072969 + 3 ^ 40 * 3963357 * 2
def baseEnd_3963357 : Nat := 2035107146361755081210359

theorem tailTrace_3963357 : CollatzResearch.WordTrace tailWord_3963357 prefixEnd_3963357 2035107146361755081210359 := by
  unfold tailWord_3963357
  simp only [CollatzResearch.WordTrace]
  refine ⟨144555505502441951330944325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96370337001627967553962883 144555505502441951330944325)
  ·
    refine ⟨27104157281707865874552061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144555505502441951330944325 27104157281707865874552061)
    ·
      refine ⟨10164058980640449702957023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27104157281707865874552061 10164058980640449702957023)
      ·
        refine ⟨15246088470960674554435535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10164058980640449702957023 15246088470960674554435535)
        ·
          refine ⟨22869132706441011831653303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15246088470960674554435535 22869132706441011831653303)
          ·
            refine ⟨34303699059661517747479955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22869132706441011831653303 34303699059661517747479955)
            ·
              refine ⟨51455548589492276621219933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34303699059661517747479955 51455548589492276621219933)
              ·
                refine ⟨19295830721059603732957475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51455548589492276621219933 19295830721059603732957475)
                ·
                  refine ⟨28943746081589405599436213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19295830721059603732957475 28943746081589405599436213)
                  ·
                    refine ⟨2713476195149006774947145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28943746081589405599436213 2713476195149006774947145)
                    ·
                      refine ⟨2035107146361755081210359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713476195149006774947145 2035107146361755081210359)
                      ·
                        rfl

theorem cell23_3963357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3963357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963357 prefixEnd_3963357 := by exact prefixLift 3963357
  have htrace : WordTrace (prefixWord ++ tailWord_3963357) baseStart_3963357 baseEnd_3963357 := by
    simpa [prefixWord, tailWord_3963357, baseEnd_3963357] using wordTrace_append hprefix tailTrace_3963357
  have hstable : (prefixWord ++ tailWord_3963357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963357).length < 2 ^ (prefixWord ++ tailWord_3963357).sum := by decide
  have hdescent : baseEnd_3963357 < baseStart_3963357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963374 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_3963374 : Nat := 118140960795 + 3963374 * 2 ^ 59
def prefixEnd_3963374 : Nat := 4983230072969 + 3 ^ 40 * 3963374 * 2
def baseEnd_3963374 : Nat := 2035115875532881514697781

theorem tailTrace_3963374 : CollatzResearch.WordTrace tailWord_3963374 prefixEnd_3963374 2035115875532881514697781 := by
  unfold tailWord_3963374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069515692922545404289147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96370750362253575489542117 18069515692922545404289147)
  ·
    refine ⟨27104273539383818106433721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18069515692922545404289147 27104273539383818106433721)
    ·
      refine ⟨20328205154537863579825291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27104273539383818106433721 20328205154537863579825291)
      ·
        refine ⟨30492307731806795369737937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20328205154537863579825291 30492307731806795369737937)
        ·
          refine ⟨22869230798855096527303453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30492307731806795369737937 22869230798855096527303453)
          ·
            refine ⟨8575961549570661197738795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22869230798855096527303453 8575961549570661197738795)
            ·
              refine ⟨12863942324355991796608193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575961549570661197738795 12863942324355991796608193)
              ·
                refine ⟨9647956743266993847456145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12863942324355991796608193 9647956743266993847456145)
                ·
                  refine ⟨7235967557450245385592109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9647956743266993847456145 7235967557450245385592109)
                  ·
                    refine ⟨2713487834043842019597041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7235967557450245385592109 2713487834043842019597041)
                    ·
                      refine ⟨2035115875532881514697781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713487834043842019597041 2035115875532881514697781)
                      ·
                        rfl

theorem cell23_3963374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_3963374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963374 prefixEnd_3963374 := by exact prefixLift 3963374
  have htrace : WordTrace (prefixWord ++ tailWord_3963374) baseStart_3963374 baseEnd_3963374 := by
    simpa [prefixWord, tailWord_3963374, baseEnd_3963374] using wordTrace_append hprefix tailTrace_3963374
  have hstable : (prefixWord ++ tailWord_3963374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963374).length < 2 ^ (prefixWord ++ tailWord_3963374).sum := by decide
  have hdescent : baseEnd_3963374 < baseStart_3963374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963400 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3963400 : Nat := 118140960795 + 3963400 * 2 ^ 59
def prefixEnd_3963400 : Nat := 4983230072969 + 3 ^ 40 * 3963400 * 2
def baseEnd_3963400 : Nat := 2035129226029898412972661

theorem tailTrace_3963400 : CollatzResearch.WordTrace tailWord_3963400 prefixEnd_3963400 2035129226029898412972661 := by
  unfold tailWord_3963400
  simp only [CollatzResearch.WordTrace]
  refine ⟨72278536920643084837379827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96371382560857446449839769 72278536920643084837379827)
  ·
    refine ⟨108417805380964627256069741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72278536920643084837379827 108417805380964627256069741)
    ·
      refine ⟨40656677017861735221026153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108417805380964627256069741 40656677017861735221026153)
      ·
        refine ⟨30492507763396301415769615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40656677017861735221026153 30492507763396301415769615)
        ·
          refine ⟨45738761645094452123654423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30492507763396301415769615 45738761645094452123654423)
          ·
            refine ⟨68608142467641678185481635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45738761645094452123654423 68608142467641678185481635)
            ·
              refine ⟨102912213701462517278222453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68608142467641678185481635 102912213701462517278222453)
              ·
                refine ⟨9648020034512110994833355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102912213701462517278222453 9648020034512110994833355)
                ·
                  refine ⟨14472030051768166492250033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9648020034512110994833355 14472030051768166492250033)
                  ·
                    refine ⟨10854022538826124869187525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14472030051768166492250033 10854022538826124869187525)
                    ·
                      refine ⟨2035129226029898412972661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10854022538826124869187525 2035129226029898412972661)
                      ·
                        rfl

theorem cell23_3963400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3963400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963400 prefixEnd_3963400 := by exact prefixLift 3963400
  have htrace : WordTrace (prefixWord ++ tailWord_3963400) baseStart_3963400 baseEnd_3963400 := by
    simpa [prefixWord, tailWord_3963400, baseEnd_3963400] using wordTrace_append hprefix tailTrace_3963400
  have hstable : (prefixWord ++ tailWord_3963400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963400).length < 2 ^ (prefixWord ++ tailWord_3963400).sum := by decide
  have hdescent : baseEnd_3963400 < baseStart_3963400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963404 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_3963404 : Nat := 118140960795 + 3963404 * 2 ^ 59
def prefixEnd_3963404 : Nat := 4983230072969 + 3 ^ 40 * 3963404 * 2
def baseEnd_3963404 : Nat := 2035131279952516397322643

theorem tailTrace_3963404 : CollatzResearch.WordTrace tailWord_3963404 prefixEnd_3963404 2035131279952516397322643 := by
  unfold tailWord_3963404
  simp only [CollatzResearch.WordTrace]
  refine ⟨72278609866635839178952633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96371479822181118905270177 72278609866635839178952633)
  ·
    refine ⟨54208957399976879384214475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72278609866635839178952633 54208957399976879384214475)
    ·
      refine ⟨81313436099965319076321713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54208957399976879384214475 81313436099965319076321713)
      ·
        refine ⟨60985077074973989307241285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81313436099965319076321713 60985077074973989307241285)
        ·
          refine ⟨11434701951557622995107741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60985077074973989307241285 11434701951557622995107741)
          ·
            refine ⟨4288013231834108623165403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11434701951557622995107741 4288013231834108623165403)
            ·
              refine ⟨6432019847751162934748105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288013231834108623165403 6432019847751162934748105)
              ·
                refine ⟨4824014885813372201061079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6432019847751162934748105 4824014885813372201061079)
                ·
                  refine ⟨7236022328720058301591619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824014885813372201061079 7236022328720058301591619)
                  ·
                    refine ⟨10854033493080087452387429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7236022328720058301591619 10854033493080087452387429)
                    ·
                      refine ⟨2035131279952516397322643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10854033493080087452387429 2035131279952516397322643)
                      ·
                        rfl

theorem cell23_3963404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_3963404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963404 prefixEnd_3963404 := by exact prefixLift 3963404
  have htrace : WordTrace (prefixWord ++ tailWord_3963404) baseStart_3963404 baseEnd_3963404 := by
    simpa [prefixWord, tailWord_3963404, baseEnd_3963404] using wordTrace_append hprefix tailTrace_3963404
  have hstable : (prefixWord ++ tailWord_3963404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963404).length < 2 ^ (prefixWord ++ tailWord_3963404).sum := by decide
  have hdescent : baseEnd_3963404 < baseStart_3963404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963424 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3963424 : Nat := 118140960795 + 3963424 * 2 ^ 59
def prefixEnd_3963424 : Nat := 4983230072969 + 3 ^ 40 * 3963424 * 2
def baseEnd_3963424 : Nat := 2035141549565606319072551

theorem tailTrace_3963424 : CollatzResearch.WordTrace tailWord_3963424 prefixEnd_3963424 2035141549565606319072551 := by
  unfold tailWord_3963424
  simp only [CollatzResearch.WordTrace]
  refine ⟨72278974596599610886816663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96371966128799481182422217 72278974596599610886816663)
  ·
    refine ⟨108418461894899416330224995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72278974596599610886816663 108418461894899416330224995)
    ·
      refine ⟨162627692842349124495337493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108418461894899416330224995 162627692842349124495337493)
      ·
        refine ⟨7623173101985115210718945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162627692842349124495337493 7623173101985115210718945)
        ·
          refine ⟨5717379826488836408039209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7623173101985115210718945 5717379826488836408039209)
          ·
            refine ⟨4288034869866627306029407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5717379826488836408039209 4288034869866627306029407)
            ·
              refine ⟨6432052304799940959044111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288034869866627306029407 6432052304799940959044111)
              ·
                refine ⟨9648078457199911438566167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432052304799940959044111 9648078457199911438566167)
                ·
                  refine ⟨14472117685799867157849251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9648078457199911438566167 14472117685799867157849251)
                  ·
                    refine ⟨21708176528699800736773877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14472117685799867157849251 21708176528699800736773877)
                    ·
                      refine ⟨2035141549565606319072551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21708176528699800736773877 2035141549565606319072551)
                      ·
                        rfl

theorem cell23_3963424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3963424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963424 prefixEnd_3963424 := by exact prefixLift 3963424
  have htrace : WordTrace (prefixWord ++ tailWord_3963424) baseStart_3963424 baseEnd_3963424 := by
    simpa [prefixWord, tailWord_3963424, baseEnd_3963424] using wordTrace_append hprefix tailTrace_3963424
  have hstable : (prefixWord ++ tailWord_3963424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963424).length < 2 ^ (prefixWord ++ tailWord_3963424).sum := by decide
  have hdescent : baseEnd_3963424 < baseStart_3963424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963447 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 5, 3, 2]
def baseStart_3963447 : Nat := 118140960795 + 3963447 * 2 ^ 59
def prefixEnd_3963447 : Nat := 4983230072969 + 3 ^ 40 * 3963447 * 2
def baseEnd_3963447 : Nat := 2035153359620659729084945

theorem tailTrace_3963447 : CollatzResearch.WordTrace tailWord_3963447 prefixEnd_3963447 2035153359620659729084945 := by
  unfold tailWord_3963447
  simp only [CollatzResearch.WordTrace]
  refine ⟨144558788072115896701720595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96372525381410597801147063 144558788072115896701720595)
  ·
    refine ⟨216838182108173845052580893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144558788072115896701720595 216838182108173845052580893)
    ·
      refine ⟨81314318290565191894717835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216838182108173845052580893 81314318290565191894717835)
      ·
        refine ⟨121971477435847787842076753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81314318290565191894717835 121971477435847787842076753)
        ·
          refine ⟨91478608076885840881557565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121971477435847787842076753 91478608076885840881557565)
          ·
            refine ⟨34304478028832190330584087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91478608076885840881557565 34304478028832190330584087)
            ·
              refine ⟨51456717043248285495876131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34304478028832190330584087 51456717043248285495876131)
              ·
                refine ⟨77185075564872428243814197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51456717043248285495876131 77185075564872428243814197)
                ·
                  refine ⟨7236100834206790147857581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77185075564872428243814197 7236100834206790147857581)
                  ·
                    refine ⟨2713537812827546305446593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7236100834206790147857581 2713537812827546305446593)
                    ·
                      refine ⟨2035153359620659729084945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713537812827546305446593 2035153359620659729084945)
                      ·
                        rfl

theorem cell23_3963447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_3963447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963447 prefixEnd_3963447 := by exact prefixLift 3963447
  have htrace : WordTrace (prefixWord ++ tailWord_3963447) baseStart_3963447 baseEnd_3963447 := by
    simpa [prefixWord, tailWord_3963447, baseEnd_3963447] using wordTrace_append hprefix tailTrace_3963447
  have hstable : (prefixWord ++ tailWord_3963447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963447).length < 2 ^ (prefixWord ++ tailWord_3963447).sum := by decide
  have hdescent : baseEnd_3963447 < baseStart_3963447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963480 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_3963480 : Nat := 118140960795 + 3963480 * 2 ^ 59
def prefixEnd_3963480 : Nat := 4983230072969 + 3 ^ 40 * 3963480 * 2
def baseEnd_3963480 : Nat := 2035170304482258099972293

theorem tailTrace_3963480 : CollatzResearch.WordTrace tailWord_3963480 prefixEnd_3963480 2035170304482258099972293 := by
  unfold tailWord_3963480
  simp only [CollatzResearch.WordTrace]
  refine ⟨72279995840498171668835947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96373327787330895558447929 72279995840498171668835947)
  ·
    refine ⟨108419993760747257503253921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72279995840498171668835947 108419993760747257503253921)
    ·
      refine ⟨81314995320560443127440441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108419993760747257503253921 81314995320560443127440441)
      ·
        refine ⟨60986246490420332345580331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81314995320560443127440441 60986246490420332345580331)
        ·
          refine ⟨91479369735630498518370497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60986246490420332345580331 91479369735630498518370497)
          ·
            refine ⟨68609527301722873888777873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91479369735630498518370497 68609527301722873888777873)
            ·
              refine ⟨51457145476292155416583405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68609527301722873888777873 51457145476292155416583405)
              ·
                refine ⟨19296429553609558281218777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51457145476292155416583405 19296429553609558281218777)
                ·
                  refine ⟨14472322165207168710914083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19296429553609558281218777 14472322165207168710914083)
                  ·
                    refine ⟨21708483247810753066371125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14472322165207168710914083 21708483247810753066371125)
                    ·
                      refine ⟨2035170304482258099972293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21708483247810753066371125 2035170304482258099972293)
                      ·
                        rfl

theorem cell23_3963480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_3963480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963480 prefixEnd_3963480 := by exact prefixLift 3963480
  have htrace : WordTrace (prefixWord ++ tailWord_3963480) baseStart_3963480 baseEnd_3963480 := by
    simpa [prefixWord, tailWord_3963480, baseEnd_3963480] using wordTrace_append hprefix tailTrace_3963480
  have hstable : (prefixWord ++ tailWord_3963480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963480).length < 2 ^ (prefixWord ++ tailWord_3963480).sum := by decide
  have hdescent : baseEnd_3963480 < baseStart_3963480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963500 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 7]
def baseStart_3963500 : Nat := 118140960795 + 3963500 * 2 ^ 59
def prefixEnd_3963500 : Nat := 4983230072969 + 3 ^ 40 * 3963500 * 2
def baseEnd_3963500 : Nat := 226131174899483113524689

theorem tailTrace_3963500 : CollatzResearch.WordTrace tailWord_3963500 prefixEnd_3963500 226131174899483113524689 := by
  unfold tailWord_3963500
  simp only [CollatzResearch.WordTrace]
  refine ⟨72280360570461943376699977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96373814093949257835599969 72280360570461943376699977)
  ·
    refine ⟨54210270427846457532524983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72280360570461943376699977 54210270427846457532524983)
    ·
      refine ⟨81315405641769686298787475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54210270427846457532524983 81315405641769686298787475)
      ·
        refine ⟨121973108462654529448181213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81315405641769686298787475 121973108462654529448181213)
        ·
          refine ⟨45739915673495448543067955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121973108462654529448181213 45739915673495448543067955)
          ·
            refine ⟨68609873510243172814601933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45739915673495448543067955 68609873510243172814601933)
            ·
              refine ⟨25728702566341189805475725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68609873510243172814601933 25728702566341189805475725)
              ·
                refine ⟨9648263462377946177053397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25728702566341189805475725 9648263462377946177053397)
                ·
                  refine ⟨226131174899483113524689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9648263462377946177053397 226131174899483113524689)
                  ·
                    rfl

theorem cell23_3963500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_3963500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963500 prefixEnd_3963500 := by exact prefixLift 3963500
  have htrace : WordTrace (prefixWord ++ tailWord_3963500) baseStart_3963500 baseEnd_3963500 := by
    simpa [prefixWord, tailWord_3963500, baseEnd_3963500] using wordTrace_append hprefix tailTrace_3963500
  have hstable : (prefixWord ++ tailWord_3963500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963500).length < 2 ^ (prefixWord ++ tailWord_3963500).sum := by decide
  have hdescent : baseEnd_3963500 < baseStart_3963500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963577 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 5, 4]
def baseStart_3963577 : Nat := 118140960795 + 3963577 * 2 ^ 59
def prefixEnd_3963577 : Nat := 4983230072969 + 3 ^ 40 * 3963577 * 2
def baseEnd_3963577 : Nat := 678406704035248073486449

theorem tailTrace_3963577 : CollatzResearch.WordTrace tailWord_3963577 prefixEnd_3963577 678406704035248073486449 := by
  unfold tailWord_3963577
  simp only [CollatzResearch.WordTrace]
  refine ⟨144563529561644928903952985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96375686374429952602635323 144563529561644928903952985)
  ·
    refine ⟨108422647171233696677964739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144563529561644928903952985 108422647171233696677964739)
    ·
      refine ⟨162633970756850545016947109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108422647171233696677964739 162633970756850545016947109)
      ·
        refine ⟨30493869516909477190677583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162633970756850545016947109 30493869516909477190677583)
        ·
          refine ⟨45740804275364215786016375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30493869516909477190677583 45740804275364215786016375)
          ·
            refine ⟨68611206413046323679024563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45740804275364215786016375 68611206413046323679024563)
            ·
              refine ⟨102916809619569485518536845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68611206413046323679024563 102916809619569485518536845)
              ·
                refine ⟨38593803607338557069451317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102916809619569485518536845 38593803607338557069451317)
                ·
                  refine ⟨3618169088187989725261061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38593803607338557069451317 3618169088187989725261061)
                  ·
                    refine ⟨678406704035248073486449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3618169088187989725261061 678406704035248073486449)
                    ·
                      rfl

theorem cell23_3963577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_3963577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963577 prefixEnd_3963577 := by exact prefixLift 3963577
  have htrace : WordTrace (prefixWord ++ tailWord_3963577) baseStart_3963577 baseEnd_3963577 := by
    simpa [prefixWord, tailWord_3963577, baseEnd_3963577] using wordTrace_append hprefix tailTrace_3963577
  have hstable : (prefixWord ++ tailWord_3963577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963577).length < 2 ^ (prefixWord ++ tailWord_3963577).sum := by decide
  have hdescent : baseEnd_3963577 < baseStart_3963577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963584 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4]
def baseStart_3963584 : Nat := 118140960795 + 3963584 * 2 ^ 59
def prefixEnd_3963584 : Nat := 4983230072969 + 3 ^ 40 * 3963584 * 2
def baseEnd_3963584 : Nat := 2035223706470325693071815

theorem tailTrace_3963584 : CollatzResearch.WordTrace tailWord_3963584 prefixEnd_3963584 2035223706470325693071815 := by
  unfold tailWord_3963584
  simp only [CollatzResearch.WordTrace]
  refine ⟨72281892436309784549728903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96375856581746379399638537 72281892436309784549728903)
  ·
    refine ⟨108422838654464676824593355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72281892436309784549728903 108422838654464676824593355)
    ·
      refine ⟨162634257981697015236890033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108422838654464676824593355 162634257981697015236890033)
      ·
        refine ⟨121975693486272761427667525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162634257981697015236890033 121975693486272761427667525)
        ·
          refine ⟨22870442528676142767687661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121975693486272761427667525 22870442528676142767687661)
          ·
            refine ⟨8576415948253553537882873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22870442528676142767687661 8576415948253553537882873)
            ·
              refine ⟨6432311961190165153412155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8576415948253553537882873 6432311961190165153412155)
              ·
                refine ⟨9648467941785247730118233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432311961190165153412155 9648467941785247730118233)
                ·
                  refine ⟨7236350956338935797588675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9648467941785247730118233 7236350956338935797588675)
                  ·
                    refine ⟨10854526434508403696383013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7236350956338935797588675 10854526434508403696383013)
                    ·
                      refine ⟨2035223706470325693071815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10854526434508403696383013 2035223706470325693071815)
                      ·
                        rfl

theorem cell23_3963584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_3963584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963584 prefixEnd_3963584 := by exact prefixLift 3963584
  have htrace : WordTrace (prefixWord ++ tailWord_3963584) baseStart_3963584 baseEnd_3963584 := by
    simpa [prefixWord, tailWord_3963584, baseEnd_3963584] using wordTrace_append hprefix tailTrace_3963584
  have hstable : (prefixWord ++ tailWord_3963584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963584).length < 2 ^ (prefixWord ++ tailWord_3963584).sum := by decide
  have hdescent : baseEnd_3963584 < baseStart_3963584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963607 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 6]
def baseStart_3963607 : Nat := 118140960795 + 3963607 * 2 ^ 59
def prefixEnd_3963607 : Nat := 4983230072969 + 3 ^ 40 * 3963607 * 2
def baseEnd_3963607 : Nat := 226137279613931011453801

theorem tailTrace_3963607 : CollatzResearch.WordTrace tailWord_3963607 prefixEnd_3963607 226137279613931011453801 := by
  unfold tailWord_3963607
  simp only [CollatzResearch.WordTrace]
  refine ⟨144564623751536244027545075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96376415834357496018363383 144564623751536244027545075)
  ·
    refine ⟨216846935627304366041317613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144564623751536244027545075 216846935627304366041317613)
    ·
      refine ⟨81317600860239137265494105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216846935627304366041317613 81317600860239137265494105)
      ·
        refine ⟨60988200645179352949120579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81317600860239137265494105 60988200645179352949120579)
        ·
          refine ⟨91482300967769029423680869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60988200645179352949120579 91482300967769029423680869)
          ·
            refine ⟨17152931431456693016940163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91482300967769029423680869 17152931431456693016940163)
            ·
              refine ⟨25729397147185039525410245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17152931431456693016940163 25729397147185039525410245)
              ·
                refine ⟨4824261965097194911014421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25729397147185039525410245 4824261965097194911014421)
                ·
                  refine ⟨226137279613931011453801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4824261965097194911014421 226137279613931011453801)
                  ·
                    rfl

theorem cell23_3963607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 6].length) (baseStart_3963607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963607 prefixEnd_3963607 := by exact prefixLift 3963607
  have htrace : WordTrace (prefixWord ++ tailWord_3963607) baseStart_3963607 baseEnd_3963607 := by
    simpa [prefixWord, tailWord_3963607, baseEnd_3963607] using wordTrace_append hprefix tailTrace_3963607
  have hstable : (prefixWord ++ tailWord_3963607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963607).length < 2 ^ (prefixWord ++ tailWord_3963607).sum := by decide
  have hdescent : baseEnd_3963607 < baseStart_3963607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963697 : List Nat := [1, 2, 2, 3, 2, 1, 3, 9]
def baseStart_3963697 : Nat := 118140960795 + 3963697 * 2 ^ 59
def prefixEnd_3963697 : Nat := 4983230072969 + 3 ^ 40 * 3963697 * 2
def baseEnd_3963697 : Nat := 75380804806825324109585

theorem tailTrace_3963697 : CollatzResearch.WordTrace tailWord_3963697 prefixEnd_3963697 75380804806825324109585 := by
  unfold tailWord_3963697
  simp only [CollatzResearch.WordTrace]
  refine ⟨144567906321210189398321345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96378604214140126265547563 144567906321210189398321345)
  ·
    refine ⟨108425929740907642048741009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144567906321210189398321345 108425929740907642048741009)
    ·
      refine ⟨81319447305680731536555757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108425929740907642048741009 81319447305680731536555757)
      ·
        refine ⟨30494792739630274326208409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81319447305680731536555757 30494792739630274326208409)
        ·
          refine ⟨22871094554722705744656307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30494792739630274326208409 22871094554722705744656307)
          ·
            refine ⟨34306641832084058616984461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22871094554722705744656307 34306641832084058616984461)
            ·
              refine ⟨12864990687031521981369173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34306641832084058616984461 12864990687031521981369173)
              ·
                refine ⟨75380804806825324109585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12864990687031521981369173 75380804806825324109585)
                ·
                  rfl

theorem cell23_3963697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 9].length) (baseStart_3963697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963697 prefixEnd_3963697 := by exact prefixLift 3963697
  have htrace : WordTrace (prefixWord ++ tailWord_3963697) baseStart_3963697 baseEnd_3963697 := by
    simpa [prefixWord, tailWord_3963697, baseEnd_3963697] using wordTrace_append hprefix tailTrace_3963697
  have hstable : (prefixWord ++ tailWord_3963697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963697).length < 2 ^ (prefixWord ++ tailWord_3963697).sum := by decide
  have hdescent : baseEnd_3963697 < baseStart_3963697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963711 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 3]
def baseStart_3963711 : Nat := 118140960795 + 3963711 * 2 ^ 59
def prefixEnd_3963711 : Nat := 4983230072969 + 3 ^ 40 * 3963711 * 2
def baseEnd_3963711 : Nat := 2035288918513446696183731

theorem tailTrace_3963711 : CollatzResearch.WordTrace tailWord_3963711 prefixEnd_3963711 2035288918513446696183731 := by
  unfold tailWord_3963711
  simp only [CollatzResearch.WordTrace]
  refine ⟨144568416943159469789330987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96378944628772979859553991 144568416943159469789330987)
  ·
    refine ⟨216852625414739204683996481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144568416943159469789330987 216852625414739204683996481)
    ·
      refine ⟨162639469061054403512997361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216852625414739204683996481 162639469061054403512997361)
      ·
        refine ⟨121979601795790802634748021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162639469061054403512997361 121979601795790802634748021)
        ·
          refine ⟨11435587668355387747007627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121979601795790802634748021 11435587668355387747007627)
          ·
            refine ⟨17153381502533081620511441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435587668355387747007627 17153381502533081620511441)
            ·
              refine ⟨12865036126899811215383581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17153381502533081620511441 12865036126899811215383581)
              ·
                refine ⟨4824388547587429205768843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12865036126899811215383581 4824388547587429205768843)
                ·
                  refine ⟨7236582821381143808653265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824388547587429205768843 7236582821381143808653265)
                  ·
                    refine ⟨5427437116035857856489949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236582821381143808653265 5427437116035857856489949)
                    ·
                      refine ⟨2035288918513446696183731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5427437116035857856489949 2035288918513446696183731)
                      ·
                        rfl

theorem cell23_3963711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_3963711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963711 prefixEnd_3963711 := by exact prefixLift 3963711
  have htrace : WordTrace (prefixWord ++ tailWord_3963711) baseStart_3963711 baseEnd_3963711 := by
    simpa [prefixWord, tailWord_3963711, baseEnd_3963711] using wordTrace_append hprefix tailTrace_3963711
  have hstable : (prefixWord ++ tailWord_3963711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963711).length < 2 ^ (prefixWord ++ tailWord_3963711).sum := by decide
  have hdescent : baseEnd_3963711 < baseStart_3963711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963758 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3963758 : Nat := 118140960795 + 3963758 * 2 ^ 59
def prefixEnd_3963758 : Nat := 4983230072969 + 3 ^ 40 * 3963758 * 2
def baseEnd_3963758 : Nat := 2035313052104208012296015

theorem tailTrace_3963758 : CollatzResearch.WordTrace tailWord_3963758 prefixEnd_3963758 2035313052104208012296015 := by
  unfold tailWord_3963758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18071266396748649602036491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96380087449326131210861285 18071266396748649602036491)
  ·
    refine ⟨27106899595122974403054737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18071266396748649602036491 27106899595122974403054737)
    ·
      refine ⟨20330174696342230802291053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27106899595122974403054737 20330174696342230802291053)
      ·
        refine ⟨7623815511128336550859145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20330174696342230802291053 7623815511128336550859145)
        ·
          refine ⟨5717861633346252413144359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7623815511128336550859145 5717861633346252413144359)
          ·
            refine ⟨8576792450019378619716539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5717861633346252413144359 8576792450019378619716539)
            ·
              refine ⟨12865188675029067929574809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8576792450019378619716539 12865188675029067929574809)
              ·
                refine ⟨9648891506271800947181107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12865188675029067929574809 9648891506271800947181107)
                ·
                  refine ⟨14473337259407701420771661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9648891506271800947181107 14473337259407701420771661)
                  ·
                    refine ⟨5427501472277888032789373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14473337259407701420771661 5427501472277888032789373)
                    ·
                      refine ⟨2035313052104208012296015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5427501472277888032789373 2035313052104208012296015)
                      ·
                        rfl

theorem cell23_3963758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3963758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963758 prefixEnd_3963758 := by exact prefixLift 3963758
  have htrace : WordTrace (prefixWord ++ tailWord_3963758) baseStart_3963758 baseEnd_3963758 := by
    simpa [prefixWord, tailWord_3963758, baseEnd_3963758] using wordTrace_append hprefix tailTrace_3963758
  have hstable : (prefixWord ++ tailWord_3963758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963758).length < 2 ^ (prefixWord ++ tailWord_3963758).sum := by decide
  have hdescent : baseEnd_3963758 < baseStart_3963758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963828 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3963828 : Nat := 118140960795 + 3963828 * 2 ^ 59
def prefixEnd_3963828 : Nat := 4983230072969 + 3 ^ 40 * 3963828 * 2
def baseEnd_3963828 : Nat := 2035348995750022738420693

theorem tailTrace_3963828 : CollatzResearch.WordTrace tailWord_3963828 prefixEnd_3963828 2035348995750022738420693 := by
  unfold tailWord_3963828
  simp only [CollatzResearch.WordTrace]
  refine ⟨72286342141867799385670069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96381789522490399180893425 72286342141867799385670069)
  ·
    refine ⟨6776844575800106192406569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72286342141867799385670069 6776844575800106192406569)
    ·
      refine ⟨5082633431850079644304927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6776844575800106192406569 5082633431850079644304927)
      ·
        refine ⟨7623950147775119466457391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082633431850079644304927 7623950147775119466457391)
        ·
          refine ⟨11435925221662679199686087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7623950147775119466457391 11435925221662679199686087)
          ·
            refine ⟨17153887832494018799529131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435925221662679199686087 17153887832494018799529131)
            ·
              refine ⟨25730831748741028199293697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17153887832494018799529131 25730831748741028199293697)
              ·
                refine ⟨19298123811555771149470273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25730831748741028199293697 19298123811555771149470273)
                ·
                  refine ⟨14473592858666828362102705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19298123811555771149470273 14473592858666828362102705)
                  ·
                    refine ⟨10855194644000121271577029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14473592858666828362102705 10855194644000121271577029)
                    ·
                      refine ⟨2035348995750022738420693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10855194644000121271577029 2035348995750022738420693)
                      ·
                        rfl

theorem cell23_3963828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3963828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963828 prefixEnd_3963828 := by exact prefixLift 3963828
  have htrace : WordTrace (prefixWord ++ tailWord_3963828) baseStart_3963828 baseEnd_3963828 := by
    simpa [prefixWord, tailWord_3963828, baseEnd_3963828] using wordTrace_append hprefix tailTrace_3963828
  have hstable : (prefixWord ++ tailWord_3963828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963828).length < 2 ^ (prefixWord ++ tailWord_3963828).sum := by decide
  have hdescent : baseEnd_3963828 < baseStart_3963828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963834 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_3963834 : Nat := 118140960795 + 3963834 * 2 ^ 59
def prefixEnd_3963834 : Nat := 4983230072969 + 3 ^ 40 * 3963834 * 2
def baseEnd_3963834 : Nat := 678450692211316571648555

theorem tailTrace_3963834 : CollatzResearch.WordTrace tailWord_3963834 prefixEnd_3963834 678450692211316571648555 := by
  unfold tailWord_3963834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36143225780428465449014639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96381935414475907864039037 36143225780428465449014639)
  ·
    refine ⟨54214838670642698173521959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36143225780428465449014639 54214838670642698173521959)
    ·
      refine ⟨81322258005964047260282939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54214838670642698173521959 81322258005964047260282939)
      ·
        refine ⟨121983387008946070890424409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81322258005964047260282939 121983387008946070890424409)
        ·
          refine ⟨91487540256709553167818307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121983387008946070890424409 91487540256709553167818307)
          ·
            refine ⟨137231310385064329751727461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91487540256709553167818307 137231310385064329751727461)
            ·
              refine ⟨25730870697199561828448899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137231310385064329751727461 25730870697199561828448899)
              ·
                refine ⟨38596306045799342742673349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25730870697199561828448899 38596306045799342742673349)
                ·
                  refine ⟨7236807383587376764251253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38596306045799342742673349 7236807383587376764251253)
                  ·
                    refine ⟨678450692211316571648555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7236807383587376764251253 678450692211316571648555)
                    ·
                      rfl

theorem cell23_3963834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_3963834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963834 prefixEnd_3963834 := by exact prefixLift 3963834
  have htrace : WordTrace (prefixWord ++ tailWord_3963834) baseStart_3963834 baseEnd_3963834 := by
    simpa [prefixWord, tailWord_3963834, baseEnd_3963834] using wordTrace_append hprefix tailTrace_3963834
  have hstable : (prefixWord ++ tailWord_3963834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963834).length < 2 ^ (prefixWord ++ tailWord_3963834).sum := by decide
  have hdescent : baseEnd_3963834 < baseStart_3963834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963898 : List Nat := [3, 1, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_3963898 : Nat := 118140960795 + 3963898 * 2 ^ 59
def prefixEnd_3963898 : Nat := 4983230072969 + 3 ^ 40 * 3963898 * 2
def baseEnd_3963898 : Nat := 678461646465279154848457

theorem tailTrace_3963898 : CollatzResearch.WordTrace tailWord_3963898 prefixEnd_3963898 678461646465279154848457 := by
  unfold tailWord_3963898
  simp only [CollatzResearch.WordTrace]
  refine ⟨36143809348370500181597087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96383491595654667150925565 36143809348370500181597087)
  ·
    refine ⟨54215714022555750272395631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36143809348370500181597087 54215714022555750272395631)
    ·
      refine ⟨81323571033833625408593447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54215714022555750272395631 81323571033833625408593447)
      ·
        refine ⟨121985356550750438112890171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81323571033833625408593447 121985356550750438112890171)
        ·
          refine ⟨182978034826125657169335257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121985356550750438112890171 182978034826125657169335257)
          ·
            refine ⟨137233526119594242877001443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182978034826125657169335257 137233526119594242877001443)
            ·
              refine ⟨205850289179391364315502165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137233526119594242877001443 205850289179391364315502165)
              ·
                refine ⟨2412308076320992550572291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 205850289179391364315502165 2412308076320992550572291)
                ·
                  refine ⟨3618462114481488825858437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412308076320992550572291 3618462114481488825858437)
                  ·
                    refine ⟨678461646465279154848457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3618462114481488825858437 678461646465279154848457)
                    ·
                      rfl

theorem cell23_3963898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_3963898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963898 prefixEnd_3963898 := by exact prefixLift 3963898
  have htrace : WordTrace (prefixWord ++ tailWord_3963898) baseStart_3963898 baseEnd_3963898 := by
    simpa [prefixWord, tailWord_3963898, baseEnd_3963898] using wordTrace_append hprefix tailTrace_3963898
  have hstable : (prefixWord ++ tailWord_3963898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963898).length < 2 ^ (prefixWord ++ tailWord_3963898).sum := by decide
  have hdescent : baseEnd_3963898 < baseStart_3963898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963911 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 6]
def baseStart_3963911 : Nat := 118140960795 + 3963911 * 2 ^ 59
def prefixEnd_3963911 : Nat := 4983230072969 + 3 ^ 40 * 3963911 * 2
def baseEnd_3963911 : Nat := 226154623849371768186979

theorem tailTrace_3963911 : CollatzResearch.WordTrace tailWord_3963911 prefixEnd_3963911 226154623849371768186979 := by
  unfold tailWord_3963911
  simp only [CollatzResearch.WordTrace]
  refine ⟨144575711542434903946611587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96383807694956602631074391 144575711542434903946611587)
  ·
    refine ⟨216863567313652355919917381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144575711542434903946611587 216863567313652355919917381)
    ·
      refine ⟨40661918871309816734984509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216863567313652355919917381 40661918871309816734984509)
      ·
        refine ⟨15248219576741181275619191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40661918871309816734984509 15248219576741181275619191)
        ·
          refine ⟨22872329365111771913428787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15248219576741181275619191 22872329365111771913428787)
          ·
            refine ⟨34308494047667657870143181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22872329365111771913428787 34308494047667657870143181)
            ·
              refine ⟨12865685267875371701303693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34308494047667657870143181 12865685267875371701303693)
              ·
                refine ⟨4824631975453264387988885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12865685267875371701303693 4824631975453264387988885)
                ·
                  refine ⟨226154623849371768186979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4824631975453264387988885 226154623849371768186979)
                  ·
                    rfl

theorem cell23_3963911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 6].length) (baseStart_3963911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963911 prefixEnd_3963911 := by exact prefixLift 3963911
  have htrace : WordTrace (prefixWord ++ tailWord_3963911) baseStart_3963911 baseEnd_3963911 := by
    simpa [prefixWord, tailWord_3963911, baseEnd_3963911] using wordTrace_append hprefix tailTrace_3963911
  have hstable : (prefixWord ++ tailWord_3963911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963911).length < 2 ^ (prefixWord ++ tailWord_3963911).sum := by decide
  have hdescent : baseEnd_3963911 < baseStart_3963911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963931 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 5, 5, 2]
def baseStart_3963931 : Nat := 118140960795 + 3963931 * 2 ^ 59
def prefixEnd_3963931 : Nat := 4983230072969 + 3 ^ 40 * 3963931 * 2
def baseEnd_3963931 : Nat := 2035401884257435835432719

theorem tailTrace_3963931 : CollatzResearch.WordTrace tailWord_3963931 prefixEnd_3963931 2035401884257435835432719 := by
  unfold tailWord_3963931
  simp only [CollatzResearch.WordTrace]
  refine ⟨144576441002362447362339647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96384294001574964908226431 144576441002362447362339647)
  ·
    refine ⟨216864661503543671043509471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144576441002362447362339647 216864661503543671043509471)
    ·
      refine ⟨325296992255315506565264207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216864661503543671043509471 325296992255315506565264207)
      ·
        refine ⟨487945488382973259847896311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325296992255315506565264207 487945488382973259847896311)
        ·
          refine ⟨731918232574459889771844467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487945488382973259847896311 731918232574459889771844467)
          ·
            refine ⟨1097877348861689834657766701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731918232574459889771844467 1097877348861689834657766701)
            ·
              refine ⟨411704005823133687996662513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097877348861689834657766701 411704005823133687996662513)
              ·
                refine ⟨308778004367350265997496885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411704005823133687996662513 308778004367350265997496885)
                ·
                  refine ⟨28947937909439087437265333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308778004367350265997496885 28947937909439087437265333)
                  ·
                    refine ⟨2713869179009914447243625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28947937909439087437265333 2713869179009914447243625)
                    ·
                      refine ⟨2035401884257435835432719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713869179009914447243625 2035401884257435835432719)
                      ·
                        rfl

theorem cell23_3963931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5, 2].length) (baseStart_3963931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963931 prefixEnd_3963931 := by exact prefixLift 3963931
  have htrace : WordTrace (prefixWord ++ tailWord_3963931) baseStart_3963931 baseEnd_3963931 := by
    simpa [prefixWord, tailWord_3963931, baseEnd_3963931] using wordTrace_append hprefix tailTrace_3963931
  have hstable : (prefixWord ++ tailWord_3963931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963931).length < 2 ^ (prefixWord ++ tailWord_3963931).sum := by decide
  have hdescent : baseEnd_3963931 < baseStart_3963931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963948 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 2, 3, 2]
def baseStart_3963948 : Nat := 118140960795 + 3963948 * 2 ^ 59
def prefixEnd_3963948 : Nat := 4983230072969 + 3 ^ 40 * 3963948 * 2
def baseEnd_3963948 : Nat := 2035410613428562268920141

theorem tailTrace_3963948 : CollatzResearch.WordTrace tailWord_3963948 prefixEnd_3963948 2035410613428562268920141 := by
  unfold tailWord_3963948
  simp only [CollatzResearch.WordTrace]
  refine ⟨72288530521650429632854249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96384707362200572843805665 72288530521650429632854249)
  ·
    refine ⟨54216397891237822224640687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72288530521650429632854249 54216397891237822224640687)
    ·
      refine ⟨81324596836856733336961031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54216397891237822224640687 81324596836856733336961031)
      ·
        refine ⟨121986895255285100005441547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81324596836856733336961031 121986895255285100005441547)
        ·
          refine ⟨182980342882927650008162321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121986895255285100005441547 182980342882927650008162321)
          ·
            refine ⟨137235257162195737506121741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182980342882927650008162321 137235257162195737506121741)
            ·
              refine ⟨51463221435823401564795653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137235257162195737506121741 51463221435823401564795653)
              ·
                refine ⟨9649354019216887793399185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51463221435823401564795653 9649354019216887793399185)
                ·
                  refine ⟨7237015514412665845049389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9649354019216887793399185 7237015514412665845049389)
                  ·
                    refine ⟨2713880817904749691893521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7237015514412665845049389 2713880817904749691893521)
                    ·
                      refine ⟨2035410613428562268920141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713880817904749691893521 2035410613428562268920141)
                      ·
                        rfl

theorem cell23_3963948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_3963948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963948 prefixEnd_3963948 := by exact prefixLift 3963948
  have htrace : WordTrace (prefixWord ++ tailWord_3963948) baseStart_3963948 baseEnd_3963948 := by
    simpa [prefixWord, tailWord_3963948, baseEnd_3963948] using wordTrace_append hprefix tailTrace_3963948
  have hstable : (prefixWord ++ tailWord_3963948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963948).length < 2 ^ (prefixWord ++ tailWord_3963948).sum := by decide
  have hdescent : baseEnd_3963948 < baseStart_3963948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963958 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3963958 : Nat := 118140960795 + 3963958 * 2 ^ 59
def prefixEnd_3963958 : Nat := 4983230072969 + 3 ^ 40 * 3963958 * 2
def baseEnd_3963958 : Nat := 678471916078369076598365

theorem tailTrace_3963958 : CollatzResearch.WordTrace tailWord_3963958 prefixEnd_3963958 678471916078369076598365 := by
  unfold tailWord_3963958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036089110829039435848283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96384950515509753982381685 9036089110829039435848283)
  ·
    refine ⟨13554133666243559153772425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036089110829039435848283 13554133666243559153772425)
    ·
      refine ⟨10165600249682669365329319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13554133666243559153772425 10165600249682669365329319)
      ·
        refine ⟨15248400374524004047993979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165600249682669365329319 15248400374524004047993979)
        ·
          refine ⟨22872600561786006071990969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15248400374524004047993979 22872600561786006071990969)
          ·
            refine ⟨17154450421339504553993227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22872600561786006071990969 17154450421339504553993227)
            ·
              refine ⟨25731675632009256830989841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17154450421339504553993227 25731675632009256830989841)
              ·
                refine ⟨19298756724006942623242381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25731675632009256830989841 19298756724006942623242381)
                ·
                  refine ⟨7237033771502603483715893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19298756724006942623242381 7237033771502603483715893)
                  ·
                    refine ⟨678471916078369076598365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7237033771502603483715893 678471916078369076598365)
                    ·
                      rfl

theorem cell23_3963958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3963958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963958 prefixEnd_3963958 := by exact prefixLift 3963958
  have htrace : WordTrace (prefixWord ++ tailWord_3963958) baseStart_3963958 baseEnd_3963958 := by
    simpa [prefixWord, tailWord_3963958, baseEnd_3963958] using wordTrace_append hprefix tailTrace_3963958
  have hstable : (prefixWord ++ tailWord_3963958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963958).length < 2 ^ (prefixWord ++ tailWord_3963958).sum := by decide
  have hdescent : baseEnd_3963958 < baseStart_3963958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963971 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 1, 6]
def baseStart_3963971 : Nat := 118140960795 + 3963971 * 2 ^ 59
def prefixEnd_3963971 : Nat := 4983230072969 + 3 ^ 40 * 3963971 * 2
def baseEnd_3963971 : Nat := 678474141161205226310845

theorem tailTrace_3963971 : CollatzResearch.WordTrace tailWord_3963971 prefixEnd_3963971 678474141161205226310845 := by
  unfold tailWord_3963971
  simp only [CollatzResearch.WordTrace]
  refine ⟨144577899922217534193795767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96385266614811689462530511 144577899922217534193795767)
  ·
    refine ⟨216866849883326301290693651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144577899922217534193795767 216866849883326301290693651)
    ·
      refine ⟨325300274824989451936040477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216866849883326301290693651 325300274824989451936040477)
      ·
        refine ⟨121987603059371044476015179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325300274824989451936040477 121987603059371044476015179)
        ·
          refine ⟨182981404589056566714022769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121987603059371044476015179 182981404589056566714022769)
          ·
            refine ⟨137236053441792425035517077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182981404589056566714022769 137236053441792425035517077)
            ·
              refine ⟨6432940005084019923539863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137236053441792425035517077 6432940005084019923539863)
              ·
                refine ⟨9649410007626029885309795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432940005084019923539863 9649410007626029885309795)
                ·
                  refine ⟨14474115011439044827964693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9649410007626029885309795 14474115011439044827964693)
                  ·
                    refine ⟨678474141161205226310845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14474115011439044827964693 678474141161205226310845)
                    ·
                      rfl

theorem cell23_3963971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 6].length) (baseStart_3963971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963971 prefixEnd_3963971 := by exact prefixLift 3963971
  have htrace : WordTrace (prefixWord ++ tailWord_3963971) baseStart_3963971 baseEnd_3963971 := by
    simpa [prefixWord, tailWord_3963971, baseEnd_3963971] using wordTrace_append hprefix tailTrace_3963971
  have hstable : (prefixWord ++ tailWord_3963971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963971).length < 2 ^ (prefixWord ++ tailWord_3963971).sum := by decide
  have hdescent : baseEnd_3963971 < baseStart_3963971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963984 : List Nat := [2, 1, 1, 1, 1, 3, 1, 13]
def baseStart_3963984 : Nat := 118140960795 + 3963984 * 2 ^ 59
def prefixEnd_3963984 : Nat := 4983230072969 + 3 ^ 40 * 3963984 * 2
def baseEnd_3963984 : Nat := 75386262916004597335925

theorem tailTrace_3963984 : CollatzResearch.WordTrace tailWord_3963984 prefixEnd_3963984 75386262916004597335925 := by
  unfold tailWord_3963984
  simp only [CollatzResearch.WordTrace]
  refine ⟨72289187035585218707009503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96385582714113624942679337 72289187035585218707009503)
  ·
    refine ⟨108433780553377828060514255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72289187035585218707009503 108433780553377828060514255)
    ·
      refine ⟨162650670830066742090771383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108433780553377828060514255 162650670830066742090771383)
      ·
        refine ⟨243976006245100113136157075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162650670830066742090771383 243976006245100113136157075)
        ·
          refine ⟨365964009367650169704235613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243976006245100113136157075 365964009367650169704235613)
          ·
            refine ⟨137236503512868813639088355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365964009367650169704235613 137236503512868813639088355)
            ·
              refine ⟨205854755269303220458632533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137236503512868813639088355 205854755269303220458632533)
              ·
                refine ⟨75386262916004597335925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 205854755269303220458632533 75386262916004597335925)
                ·
                  rfl

theorem cell23_3963984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 13].length) (baseStart_3963984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3963984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3963984 prefixEnd_3963984 := by exact prefixLift 3963984
  have htrace : WordTrace (prefixWord ++ tailWord_3963984) baseStart_3963984 baseEnd_3963984 := by
    simpa [prefixWord, tailWord_3963984, baseEnd_3963984] using wordTrace_append hprefix tailTrace_3963984
  have hstable : (prefixWord ++ tailWord_3963984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963984).length < 2 ^ (prefixWord ++ tailWord_3963984).sum := by decide
  have hdescent : baseEnd_3963984 < baseStart_3963984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964012 : List Nat := [2, 2, 1, 1, 3, 2, 1, 6, 1, 2, 2]
def baseStart_3964012 : Nat := 118140960795 + 3964012 * 2 ^ 59
def prefixEnd_3964012 : Nat := 4983230072969 + 3 ^ 40 * 3964012 * 2
def baseEnd_3964012 : Nat := 2035443476190450018519847

theorem tailTrace_3964012 : CollatzResearch.WordTrace tailWord_3964012 prefixEnd_3964012 2035443476190450018519847 := by
  unfold tailWord_3964012
  simp only [CollatzResearch.WordTrace]
  refine ⟨72289697657534499098019145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96386263543379332130692193 72289697657534499098019145)
  ·
    refine ⟨54217273243150874323514359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72289697657534499098019145 54217273243150874323514359)
    ·
      refine ⟨81325909864726311485271539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54217273243150874323514359 81325909864726311485271539)
      ·
        refine ⟨121988864797089467227907309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81325909864726311485271539 121988864797089467227907309)
        ·
          refine ⟨45745824298908550210465241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121988864797089467227907309 45745824298908550210465241)
          ·
            refine ⟨34309368224181412657848931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45745824298908550210465241 34309368224181412657848931)
            ·
              refine ⟨51464052336272118986773397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34309368224181412657848931 51464052336272118986773397)
              ·
                refine ⟨2412377453262755577505003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51464052336272118986773397 2412377453262755577505003)
                ·
                  refine ⟨3618566179894133366257505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412377453262755577505003 3618566179894133366257505)
                  ·
                    refine ⟨2713924634920600024693129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3618566179894133366257505 2713924634920600024693129)
                    ·
                      refine ⟨2035443476190450018519847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713924634920600024693129 2035443476190450018519847)
                      ·
                        rfl

theorem cell23_3964012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_3964012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964012 prefixEnd_3964012 := by exact prefixLift 3964012
  have htrace : WordTrace (prefixWord ++ tailWord_3964012) baseStart_3964012 baseEnd_3964012 := by
    simpa [prefixWord, tailWord_3964012, baseEnd_3964012] using wordTrace_append hprefix tailTrace_3964012
  have hstable : (prefixWord ++ tailWord_3964012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964012).length < 2 ^ (prefixWord ++ tailWord_3964012).sum := by decide
  have hdescent : baseEnd_3964012 < baseStart_3964012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964022 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_3964022 : Nat := 118140960795 + 3964022 * 2 ^ 59
def prefixEnd_3964022 : Nat := 4983230072969 + 3 ^ 40 * 3964022 * 2
def baseEnd_3964022 : Nat := 678482870332331659798267

theorem tailTrace_3964022 : CollatzResearch.WordTrace tailWord_3964022 prefixEnd_3964022 678482870332331659798267 := by
  unfold tailWord_3964022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036235002814548118993895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96386506696688513269268213 9036235002814548118993895)
  ·
    refine ⟨13554352504221822178490843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036235002814548118993895 13554352504221822178490843)
    ·
      refine ⟨20331528756332733267736265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13554352504221822178490843 20331528756332733267736265)
      ·
        refine ⟨15248646567249549950802199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20331528756332733267736265 15248646567249549950802199)
        ·
          refine ⟨22872969850874324926203299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15248646567249549950802199 22872969850874324926203299)
          ·
            refine ⟨34309454776311487389304949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22872969850874324926203299 34309454776311487389304949)
            ·
              refine ⟨3216511385279201942747339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34309454776311487389304949 3216511385279201942747339)
              ·
                refine ⟨4824767077918802914121009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216511385279201942747339 4824767077918802914121009)
                ·
                  refine ⟨3618575308439102185590757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4824767077918802914121009 3618575308439102185590757)
                  ·
                    refine ⟨678482870332331659798267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3618575308439102185590757 678482870332331659798267)
                    ·
                      rfl

theorem cell23_3964022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_3964022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964022 prefixEnd_3964022 := by exact prefixLift 3964022
  have htrace : WordTrace (prefixWord ++ tailWord_3964022) baseStart_3964022 baseEnd_3964022 := by
    simpa [prefixWord, tailWord_3964022, baseEnd_3964022] using wordTrace_append hprefix tailTrace_3964022
  have hstable : (prefixWord ++ tailWord_3964022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964022).length < 2 ^ (prefixWord ++ tailWord_3964022).sum := by decide
  have hdescent : baseEnd_3964022 < baseStart_3964022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964025 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 4]
def baseStart_3964025 : Nat := 118140960795 + 3964025 * 2 ^ 59
def prefixEnd_3964025 : Nat := 4983230072969 + 3 ^ 40 * 3964025 * 2
def baseEnd_3964025 : Nat := 2035450151438958467657287

theorem tailTrace_3964025 : CollatzResearch.WordTrace tailWord_3964025 prefixEnd_3964025 2035450151438958467657287 := by
  unfold tailWord_3964025
  simp only [CollatzResearch.WordTrace]
  refine ⟨144579869464021901416261529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96386579642681267610841019 144579869464021901416261529)
  ·
    refine ⟨108434902098016426062196147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144579869464021901416261529 108434902098016426062196147)
    ·
      refine ⟨162652353147024639093294221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108434902098016426062196147 162652353147024639093294221)
      ·
        refine ⟨60994632430134239659985333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162652353147024639093294221 60994632430134239659985333)
        ·
          refine ⟨5718246790325084968123625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60994632430134239659985333 5718246790325084968123625)
          ·
            refine ⟨4288685092743813726092719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5718246790325084968123625 4288685092743813726092719)
            ·
              refine ⟨6433027639115720589139079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288685092743813726092719 6433027639115720589139079)
              ·
                refine ⟨9649541458673580883708619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433027639115720589139079 9649541458673580883708619)
                ·
                  refine ⟨14474312188010371325562929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9649541458673580883708619 14474312188010371325562929)
                  ·
                    refine ⟨10855734141007778494172197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14474312188010371325562929 10855734141007778494172197)
                    ·
                      refine ⟨2035450151438958467657287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10855734141007778494172197 2035450151438958467657287)
                      ·
                        rfl

theorem cell23_3964025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_3964025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964025 prefixEnd_3964025 := by exact prefixLift 3964025
  have htrace : WordTrace (prefixWord ++ tailWord_3964025) baseStart_3964025 baseEnd_3964025 := by
    simpa [prefixWord, tailWord_3964025, baseEnd_3964025] using wordTrace_append hprefix tailTrace_3964025
  have hstable : (prefixWord ++ tailWord_3964025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964025).length < 2 ^ (prefixWord ++ tailWord_3964025).sum := by decide
  have hdescent : baseEnd_3964025 < baseStart_3964025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964041 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_3964041 : Nat := 118140960795 + 3964041 * 2 ^ 59
def prefixEnd_3964041 : Nat := 4983230072969 + 3 ^ 40 * 3964041 * 2
def baseEnd_3964041 : Nat := 2035458367129430405057213

theorem tailTrace_3964041 : CollatzResearch.WordTrace tailWord_3964041 prefixEnd_3964041 2035458367129430405057213 := by
  unfold tailWord_3964041
  simp only [CollatzResearch.WordTrace]
  refine ⟨144580453031963936148843977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96386968687975957432562651 144580453031963936148843977)
  ·
    refine ⟨108435339773972952111632983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144580453031963936148843977 108435339773972952111632983)
    ·
      refine ⟨162653009660959428167449475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108435339773972952111632983 162653009660959428167449475)
      ·
        refine ⟨243979514491439142251174213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162653009660959428167449475 243979514491439142251174213)
        ·
          refine ⟨45746158967144839172095165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243979514491439142251174213 45746158967144839172095165)
          ·
            refine ⟨17154809612679314689535687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45746158967144839172095165 17154809612679314689535687)
            ·
              refine ⟨25732214419018972034303531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17154809612679314689535687 25732214419018972034303531)
              ·
                refine ⟨38598321628528458051455297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25732214419018972034303531 38598321628528458051455297)
                ·
                  refine ⟨28948741221396343538591473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38598321628528458051455297 28948741221396343538591473)
                  ·
                    refine ⟨21711555916047257653943605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28948741221396343538591473 21711555916047257653943605)
                    ·
                      refine ⟨2035458367129430405057213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21711555916047257653943605 2035458367129430405057213)
                      ·
                        rfl

theorem cell23_3964041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_3964041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964041 prefixEnd_3964041 := by exact prefixLift 3964041
  have htrace : WordTrace (prefixWord ++ tailWord_3964041) baseStart_3964041 baseEnd_3964041 := by
    simpa [prefixWord, tailWord_3964041, baseEnd_3964041] using wordTrace_append hprefix tailTrace_3964041
  have hstable : (prefixWord ++ tailWord_3964041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964041).length < 2 ^ (prefixWord ++ tailWord_3964041).sum := by decide
  have hdescent : baseEnd_3964041 < baseStart_3964041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964046 : List Nat := [4, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3964046 : Nat := 118140960795 + 3964046 * 2 ^ 59
def prefixEnd_3964046 : Nat := 4983230072969 + 3 ^ 40 * 3964046 * 2
def baseEnd_3964046 : Nat := 2035460934532702885494691

theorem tailTrace_3964046 : CollatzResearch.WordTrace tailWord_3964046 prefixEnd_3964046 2035460934532702885494691 := by
  unfold tailWord_3964046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18072579424618227750346999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96387090264630548001850661 18072579424618227750346999)
  ·
    refine ⟨27108869136927341625520499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18072579424618227750346999 27108869136927341625520499)
    ·
      refine ⟨40663303705391012438280749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27108869136927341625520499 40663303705391012438280749)
      ·
        refine ⟨15248738889521629664355281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40663303705391012438280749 15248738889521629664355281)
        ·
          refine ⟨11436554167141222248266461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15248738889521629664355281 11436554167141222248266461)
          ·
            refine ⟨4288707812677958343099923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11436554167141222248266461 4288707812677958343099923)
            ·
              refine ⟨6433061719016937514649885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288707812677958343099923 6433061719016937514649885)
              ·
                refine ⟨2412398144631351567993707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6433061719016937514649885 2412398144631351567993707)
                ·
                  refine ⟨3618597216947027351990561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412398144631351567993707 3618597216947027351990561)
                  ·
                    refine ⟨2713947912710270513992921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3618597216947027351990561 2713947912710270513992921)
                    ·
                      refine ⟨2035460934532702885494691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2713947912710270513992921 2035460934532702885494691)
                      ·
                        rfl

theorem cell23_3964046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3964046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964046 prefixEnd_3964046 := by exact prefixLift 3964046
  have htrace : WordTrace (prefixWord ++ tailWord_3964046) baseStart_3964046 baseEnd_3964046 := by
    simpa [prefixWord, tailWord_3964046, baseEnd_3964046] using wordTrace_append hprefix tailTrace_3964046
  have hstable : (prefixWord ++ tailWord_3964046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964046).length < 2 ^ (prefixWord ++ tailWord_3964046).sum := by decide
  have hdescent : baseEnd_3964046 < baseStart_3964046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964062 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3964062 : Nat := 118140960795 + 3964062 * 2 ^ 59
def prefixEnd_3964062 : Nat := 4983230072969 + 3 ^ 40 * 3964062 * 2
def baseEnd_3964062 : Nat := 2035469150223174822894617

theorem tailTrace_3964062 : CollatzResearch.WordTrace tailWord_3964062 prefixEnd_3964062 2035469150223174822894617 := by
  unfold tailWord_3964062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18072652370610982091919805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96387479309925237823572293 18072652370610982091919805)
  ·
    refine ⟨6777244638979118284469927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18072652370610982091919805 6777244638979118284469927)
    ·
      refine ⟨10165866958468677426704891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777244638979118284469927 10165866958468677426704891)
      ·
        refine ⟨15248800437703016140057337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165866958468677426704891 15248800437703016140057337)
        ·
          refine ⟨11436600328277262105043003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15248800437703016140057337 11436600328277262105043003)
          ·
            refine ⟨17154900492415893157564505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11436600328277262105043003 17154900492415893157564505)
            ·
              refine ⟨12866175369311919868173379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17154900492415893157564505 12866175369311919868173379)
              ·
                refine ⟨19299263053967879802260069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12866175369311919868173379 19299263053967879802260069)
                ·
                  refine ⟨3618611822618977462923763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19299263053967879802260069 3618611822618977462923763)
                  ·
                    refine ⟨5427917733928466194385645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3618611822618977462923763 5427917733928466194385645)
                    ·
                      refine ⟨2035469150223174822894617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5427917733928466194385645 2035469150223174822894617)
                      ·
                        rfl

theorem cell23_3964062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3964062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964062 prefixEnd_3964062 := by exact prefixLift 3964062
  have htrace : WordTrace (prefixWord ++ tailWord_3964062) baseStart_3964062 baseEnd_3964062 := by
    simpa [prefixWord, tailWord_3964062, baseEnd_3964062] using wordTrace_append hprefix tailTrace_3964062
  have hstable : (prefixWord ++ tailWord_3964062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964062).length < 2 ^ (prefixWord ++ tailWord_3964062).sum := by decide
  have hdescent : baseEnd_3964062 < baseStart_3964062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964121 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 3, 7]
def baseStart_3964121 : Nat := 118140960795 + 3964121 * 2 ^ 59
def prefixEnd_3964121 : Nat := 4983230072969 + 3 ^ 40 * 3964121 * 2
def baseEnd_3964121 : Nat := 678499815193930030685615

theorem tailTrace_3964121 : CollatzResearch.WordTrace tailWord_3964121 prefixEnd_3964121 678499815193930030685615 := by
  unfold tailWord_3964121
  simp only [CollatzResearch.WordTrace]
  refine ⟨144583370871674109811756217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96388913914449406541170811 144583370871674109811756217)
  ·
    refine ⟨108437528153755582358817163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144583370871674109811756217 108437528153755582358817163)
    ·
      refine ⟨162656292230633373538225745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108437528153755582358817163 162656292230633373538225745)
      ·
        refine ⟨121992219172975030153669309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162656292230633373538225745 121992219172975030153669309)
        ·
          refine ⟨45747082189865636307625991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121992219172975030153669309 45747082189865636307625991)
          ·
            refine ⟨68620623284798454461438987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45747082189865636307625991 68620623284798454461438987)
            ·
              refine ⟨102930934927197681692158481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68620623284798454461438987 102930934927197681692158481)
              ·
                refine ⟨77198201195398261269118861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102930934927197681692158481 77198201195398261269118861)
                ·
                  refine ⟨28949325448274347975919573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77198201195398261269118861 28949325448274347975919573)
                  ·
                    refine ⟨678499815193930030685615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28949325448274347975919573 678499815193930030685615)
                    ·
                      rfl

theorem cell23_3964121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_3964121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964121 prefixEnd_3964121 := by exact prefixLift 3964121
  have htrace : WordTrace (prefixWord ++ tailWord_3964121) baseStart_3964121 baseEnd_3964121 := by
    simpa [prefixWord, tailWord_3964121, baseEnd_3964121] using wordTrace_append hprefix tailTrace_3964121
  have hstable : (prefixWord ++ tailWord_3964121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964121).length < 2 ^ (prefixWord ++ tailWord_3964121).sum := by decide
  have hdescent : baseEnd_3964121 < baseStart_3964121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964151 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 2, 8]
def baseStart_3964151 : Nat := 118140960795 + 3964151 * 2 ^ 59
def prefixEnd_3964151 : Nat := 4983230072969 + 3 ^ 40 * 3964151 * 2
def baseEnd_3964151 : Nat := 678504950000474991560569

theorem tailTrace_3964151 : CollatzResearch.WordTrace tailWord_3964151 prefixEnd_3964151 678504950000474991560569 := by
  unfold tailWord_3964151
  simp only [CollatzResearch.WordTrace]
  refine ⟨144584465061565424935348307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96389643374376949956898871 144584465061565424935348307)
  ·
    refine ⟨216876697592348137403022461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144584465061565424935348307 216876697592348137403022461)
    ·
      refine ⟨81328761597130551526133423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216876697592348137403022461 81328761597130551526133423)
      ·
        refine ⟨121993142395695827289200135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81328761597130551526133423 121993142395695827289200135)
        ·
          refine ⟨182989713593543740933800203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121993142395695827289200135 182989713593543740933800203)
          ·
            refine ⟨274484570390315611400700305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182989713593543740933800203 274484570390315611400700305)
            ·
              refine ⟨205863427792736708550525229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274484570390315611400700305 205863427792736708550525229)
              ·
                refine ⟨77198785422276265706446961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205863427792736708550525229 77198785422276265706446961)
                ·
                  refine ⟨57899089066707199279835221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77198785422276265706446961 57899089066707199279835221)
                  ·
                    refine ⟨678504950000474991560569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57899089066707199279835221 678504950000474991560569)
                    ·
                      rfl

theorem cell23_3964151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_3964151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964151 prefixEnd_3964151 := by exact prefixLift 3964151
  have htrace : WordTrace (prefixWord ++ tailWord_3964151) baseStart_3964151 baseEnd_3964151 := by
    simpa [prefixWord, tailWord_3964151, baseEnd_3964151] using wordTrace_append hprefix tailTrace_3964151
  have hstable : (prefixWord ++ tailWord_3964151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964151).length < 2 ^ (prefixWord ++ tailWord_3964151).sum := by decide
  have hdescent : baseEnd_3964151 < baseStart_3964151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964202 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3964202 : Nat := 118140960795 + 3964202 * 2 ^ 59
def prefixEnd_3964202 : Nat := 4983230072969 + 3 ^ 40 * 3964202 * 2
def baseEnd_3964202 : Nat := 678513679171601425047991

theorem tailTrace_3964202 : CollatzResearch.WordTrace tailWord_3964202 prefixEnd_3964202 678513679171601425047991 := by
  unfold tailWord_3964202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36146581296095165161363715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96390883456253773763636573 36146581296095165161363715)
  ·
    refine ⟨54219871944142747742045573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36146581296095165161363715 54219871944142747742045573)
    ·
      refine ⟨10166225989526765201633545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54219871944142747742045573 10166225989526765201633545)
      ·
        refine ⟨7624669492145073901225159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10166225989526765201633545 7624669492145073901225159)
        ·
          refine ⟨11437004238217610851837739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624669492145073901225159 11437004238217610851837739)
          ·
            refine ⟨17155506357326416277756609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437004238217610851837739 17155506357326416277756609)
            ·
              refine ⟨12866629767994812208317457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17155506357326416277756609 12866629767994812208317457)
              ·
                refine ⟨9649972325996109156238093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12866629767994812208317457 9649972325996109156238093)
                ·
                  refine ⟨3618739622248540933589285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9649972325996109156238093 3618739622248540933589285)
                  ·
                    refine ⟨678513679171601425047991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3618739622248540933589285 678513679171601425047991)
                    ·
                      rfl

theorem cell23_3964202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3964202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964202 prefixEnd_3964202 := by exact prefixLift 3964202
  have htrace : WordTrace (prefixWord ++ tailWord_3964202) baseStart_3964202 baseEnd_3964202 := by
    simpa [prefixWord, tailWord_3964202, baseEnd_3964202] using wordTrace_append hprefix tailTrace_3964202
  have hstable : (prefixWord ++ tailWord_3964202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964202).length < 2 ^ (prefixWord ++ tailWord_3964202).sum := by decide
  have hdescent : baseEnd_3964202 < baseStart_3964202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964208 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3]
def baseStart_3964208 : Nat := 118140960795 + 3964208 * 2 ^ 59
def prefixEnd_3964208 : Nat := 4983230072969 + 3 ^ 40 * 3964208 * 2
def baseEnd_3964208 : Nat := 2035544118398731251668945

theorem tailTrace_3964208 : CollatzResearch.WordTrace tailWord_3964208 prefixEnd_3964208 2035544118398731251668945 := by
  unfold tailWord_3964208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72293272011179461835086639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96391029348239282446782185 72293272011179461835086639)
  ·
    refine ⟨108439908016769192752629959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72293272011179461835086639 108439908016769192752629959)
    ·
      refine ⟨162659862025153789128944939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108439908016769192752629959 162659862025153789128944939)
      ·
        refine ⟨243989793037730683693417409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162659862025153789128944939 243989793037730683693417409)
        ·
          refine ⟨182992344778298012770063057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243989793037730683693417409 182992344778298012770063057)
          ·
            refine ⟨137244258583723509577547293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182992344778298012770063057 137244258583723509577547293)
            ·
              refine ⟨51466596968896316091580235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137244258583723509577547293 51466596968896316091580235)
              ·
                refine ⟨77199895453344474137370353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51466596968896316091580235 77199895453344474137370353)
                ·
                  refine ⟨57899921590008355603027765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77199895453344474137370353 57899921590008355603027765)
                  ·
                    refine ⟨5428117649063283337783853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57899921590008355603027765 5428117649063283337783853)
                    ·
                      refine ⟨2035544118398731251668945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5428117649063283337783853 2035544118398731251668945)
                      ·
                        rfl

theorem cell23_3964208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_3964208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964208 prefixEnd_3964208 := by exact prefixLift 3964208
  have htrace : WordTrace (prefixWord ++ tailWord_3964208) baseStart_3964208 baseEnd_3964208 := by
    simpa [prefixWord, tailWord_3964208, baseEnd_3964208] using wordTrace_append hprefix tailTrace_3964208
  have hstable : (prefixWord ++ tailWord_3964208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964208).length < 2 ^ (prefixWord ++ tailWord_3964208).sum := by decide
  have hdescent : baseEnd_3964208 < baseStart_3964208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964212 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3964212 : Nat := 118140960795 + 3964212 * 2 ^ 59
def prefixEnd_3964212 : Nat := 4983230072969 + 3 ^ 40 * 3964212 * 2
def baseEnd_3964212 : Nat := 2035546172321349236018927

theorem tailTrace_3964212 : CollatzResearch.WordTrace tailWord_3964212 prefixEnd_3964212 2035546172321349236018927 := by
  unfold tailWord_3964212
  simp only [CollatzResearch.WordTrace]
  refine ⟨72293344957172216176659445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96391126609562954902212593 72293344957172216176659445)
  ·
    refine ⟨6777501089734895266561823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72293344957172216176659445 6777501089734895266561823)
    ·
      refine ⟨10166251634602342899842735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777501089734895266561823 10166251634602342899842735)
      ·
        refine ⟨15249377451903514349764103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166251634602342899842735 15249377451903514349764103)
        ·
          refine ⟨22874066177855271524646155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15249377451903514349764103 22874066177855271524646155)
          ·
            refine ⟨34311099266782907286969233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22874066177855271524646155 34311099266782907286969233)
            ·
              refine ⟨25733324450087180465226925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34311099266782907286969233 25733324450087180465226925)
              ·
                refine ⟨9649996668782692674460097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25733324450087180465226925 9649996668782692674460097)
                ·
                  refine ⟨7237497501587019505845073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9649996668782692674460097 7237497501587019505845073)
                  ·
                    refine ⟨5428123126190264629383805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7237497501587019505845073 5428123126190264629383805)
                    ·
                      refine ⟨2035546172321349236018927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5428123126190264629383805 2035546172321349236018927)
                      ·
                        rfl

theorem cell23_3964212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3964212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964212 prefixEnd_3964212 := by exact prefixLift 3964212
  have htrace : WordTrace (prefixWord ++ tailWord_3964212) baseStart_3964212 baseEnd_3964212 := by
    simpa [prefixWord, tailWord_3964212, baseEnd_3964212] using wordTrace_append hprefix tailTrace_3964212
  have hstable : (prefixWord ++ tailWord_3964212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964212).length < 2 ^ (prefixWord ++ tailWord_3964212).sum := by decide
  have hdescent : baseEnd_3964212 < baseStart_3964212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964265 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 4]
def baseStart_3964265 : Nat := 118140960795 + 3964265 * 2 ^ 59
def prefixEnd_3964265 : Nat := 4983230072969 + 3 ^ 40 * 3964265 * 2
def baseEnd_3964265 : Nat := 2035573386796037528656183

theorem tailTrace_3964265 : CollatzResearch.WordTrace tailWord_3964265 prefixEnd_3964265 2035573386796037528656183 := by
  unfold tailWord_3964265
  simp only [CollatzResearch.WordTrace]
  refine ⟨144588622983152422404998249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96392415322101614936665499 144588622983152422404998249)
  ·
    refine ⟨108441467237364316803748687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144588622983152422404998249 108441467237364316803748687)
    ·
      refine ⟨162662200856046475205623031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108441467237364316803748687 162662200856046475205623031)
      ·
        refine ⟨243993301284069712808434547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162662200856046475205623031 243993301284069712808434547)
        ·
          refine ⟨365989951926104569212651821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243993301284069712808434547 365989951926104569212651821)
          ·
            refine ⟨137246231972289213454744433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365989951926104569212651821 137246231972289213454744433)
            ·
              refine ⟨102934673979216910091058325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137246231972289213454744433 102934673979216910091058325)
              ·
                refine ⟨4825062842775792660518359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102934673979216910091058325 4825062842775792660518359)
                ·
                  refine ⟨7237594264163688990777539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825062842775792660518359 7237594264163688990777539)
                  ·
                    refine ⟨10856391396245533486166309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7237594264163688990777539 10856391396245533486166309)
                    ·
                      refine ⟨2035573386796037528656183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10856391396245533486166309 2035573386796037528656183)
                      ·
                        rfl

theorem cell23_3964265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_3964265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964265 prefixEnd_3964265 := by exact prefixLift 3964265
  have htrace : WordTrace (prefixWord ++ tailWord_3964265) baseStart_3964265 baseEnd_3964265 := by
    simpa [prefixWord, tailWord_3964265, baseEnd_3964265] using wordTrace_append hprefix tailTrace_3964265
  have hstable : (prefixWord ++ tailWord_3964265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964265).length < 2 ^ (prefixWord ++ tailWord_3964265).sum := by decide
  have hdescent : baseEnd_3964265 < baseStart_3964265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964269 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_3964269 : Nat := 118140960795 + 3964269 * 2 ^ 59
def prefixEnd_3964269 : Nat := 4983230072969 + 3 ^ 40 * 3964269 * 2
def baseEnd_3964269 : Nat := 2035575440718655513006165

theorem tailTrace_3964269 : CollatzResearch.WordTrace tailWord_3964269 prefixEnd_3964269 2035575440718655513006165 := by
  unfold tailWord_3964269
  simp only [CollatzResearch.WordTrace]
  refine ⟨144588768875137931088143861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96392512583425287392095907 144588768875137931088143861)
  ·
    refine ⟨13555197082044181039513487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144588768875137931088143861 13555197082044181039513487)
    ·
      refine ⟨20332795623066271559270231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555197082044181039513487 20332795623066271559270231)
      ·
        refine ⟨30499193434599407338905347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20332795623066271559270231 30499193434599407338905347)
        ·
          refine ⟨45748790151899111008358021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30499193434599407338905347 45748790151899111008358021)
          ·
            refine ⟨8577898153481083314067129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45748790151899111008358021 8577898153481083314067129)
            ·
              refine ⟨6433423615110812485550347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577898153481083314067129 6433423615110812485550347)
              ·
                refine ⟨9650135422666218728325521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433423615110812485550347 9650135422666218728325521)
                ·
                  refine ⟨7237601566999664046244141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9650135422666218728325521 7237601566999664046244141)
                  ·
                    refine ⟨2714100587624874017341553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7237601566999664046244141 2714100587624874017341553)
                    ·
                      refine ⟨2035575440718655513006165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714100587624874017341553 2035575440718655513006165)
                      ·
                        rfl

theorem cell23_3964269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_3964269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964269 prefixEnd_3964269 := by exact prefixLift 3964269
  have htrace : WordTrace (prefixWord ++ tailWord_3964269) baseStart_3964269 baseEnd_3964269 := by
    simpa [prefixWord, tailWord_3964269, baseEnd_3964269] using wordTrace_append hprefix tailTrace_3964269
  have hstable : (prefixWord ++ tailWord_3964269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964269).length < 2 ^ (prefixWord ++ tailWord_3964269).sum := by decide
  have hdescent : baseEnd_3964269 < baseStart_3964269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964282 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2]
def baseStart_3964282 : Nat := 118140960795 + 3964282 * 2 ^ 59
def prefixEnd_3964282 : Nat := 4983230072969 + 3 ^ 40 * 3964282 * 2
def baseEnd_3964282 : Nat := 2035582115967163962143605

theorem tailTrace_3964282 : CollatzResearch.WordTrace tailWord_3964282 prefixEnd_3964282 2035582115967163962143605 := by
  unfold tailWord_3964282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36147310756022708577091775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96392828682727222872244733 36147310756022708577091775)
  ·
    refine ⟨54220966134034062865637663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36147310756022708577091775 54220966134034062865637663)
    ·
      refine ⟨81331449201051094298456495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54220966134034062865637663 81331449201051094298456495)
      ·
        refine ⟨121997173801576641447684743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81331449201051094298456495 121997173801576641447684743)
        ·
          refine ⟨182995760702364962171527115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121997173801576641447684743 182995760702364962171527115)
          ·
            refine ⟨274493641053547443257290673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182995760702364962171527115 274493641053547443257290673)
            ·
              refine ⟨205870230790160582442968005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274493641053547443257290673 205870230790160582442968005)
              ·
                refine ⟨38600668273155109208056501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205870230790160582442968005 38600668273155109208056501)
                ·
                  refine ⟨3618812650608291488255297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38600668273155109208056501 3618812650608291488255297)
                  ·
                    refine ⟨2714109487956218616191473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3618812650608291488255297 2714109487956218616191473)
                    ·
                      refine ⟨2035582115967163962143605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714109487956218616191473 2035582115967163962143605)
                      ·
                        rfl

theorem cell23_3964282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_3964282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964282 prefixEnd_3964282 := by exact prefixLift 3964282
  have htrace : WordTrace (prefixWord ++ tailWord_3964282) baseStart_3964282 baseEnd_3964282 := by
    simpa [prefixWord, tailWord_3964282, baseEnd_3964282] using wordTrace_append hprefix tailTrace_3964282
  have hstable : (prefixWord ++ tailWord_3964282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964282).length < 2 ^ (prefixWord ++ tailWord_3964282).sum := by decide
  have hdescent : baseEnd_3964282 < baseStart_3964282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964292 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_3964292 : Nat := 118140960795 + 3964292 * 2 ^ 59
def prefixEnd_3964292 : Nat := 4983230072969 + 3 ^ 40 * 3964292 * 2
def baseEnd_3964292 : Nat := 678529083591236307672853

theorem tailTrace_3964292 : CollatzResearch.WordTrace tailWord_3964292 prefixEnd_3964292 678529083591236307672853 := by
  unfold tailWord_3964292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72294803877027303008115565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96393071836036404010820753 72294803877027303008115565)
  ·
    refine ⟨27110551453885238628043337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72294803877027303008115565 27110551453885238628043337)
    ·
      refine ⟨20332913590413928971032503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27110551453885238628043337 20332913590413928971032503)
      ·
        refine ⟨30499370385620893456548755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20332913590413928971032503 30499370385620893456548755)
        ·
          refine ⟨45749055578431340184823133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30499370385620893456548755 45749055578431340184823133)
          ·
            refine ⟨17155895841911752569308675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45749055578431340184823133 17155895841911752569308675)
            ·
              refine ⟨25733843762867628853963013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17155895841911752569308675 25733843762867628853963013)
              ·
                refine ⟨4825095705537680410118065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25733843762867628853963013 4825095705537680410118065)
                ·
                  refine ⟨3618821779153260307588549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4825095705537680410118065 3618821779153260307588549)
                  ·
                    refine ⟨678529083591236307672853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3618821779153260307588549 678529083591236307672853)
                    ·
                      rfl

theorem cell23_3964292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_3964292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964292 prefixEnd_3964292 := by exact prefixLift 3964292
  have htrace : WordTrace (prefixWord ++ tailWord_3964292) baseStart_3964292 baseEnd_3964292 := by
    simpa [prefixWord, tailWord_3964292, baseEnd_3964292] using wordTrace_append hprefix tailTrace_3964292
  have hstable : (prefixWord ++ tailWord_3964292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964292).length < 2 ^ (prefixWord ++ tailWord_3964292).sum := by decide
  have hdescent : baseEnd_3964292 < baseStart_3964292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964322 : List Nat := [3, 3, 1, 2, 1, 3, 3, 7]
def baseStart_3964322 : Nat := 118140960795 + 3964322 * 2 ^ 59
def prefixEnd_3964322 : Nat := 4983230072969 + 3 ^ 40 * 3964322 * 2
def baseEnd_3964322 : Nat := 75392690933086807616423

theorem tailTrace_3964322 : CollatzResearch.WordTrace tailWord_3964322 prefixEnd_3964322 75392690933086807616423 := by
  unfold tailWord_3964322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36147675485986480284955805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96393801295963947426548813 36147675485986480284955805)
  ·
    refine ⟨13555378307244930106858427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36147675485986480284955805 13555378307244930106858427)
    ·
      refine ⟨20333067460867395160287641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555378307244930106858427 20333067460867395160287641)
      ·
        refine ⟨15249800595650546370215731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20333067460867395160287641 15249800595650546370215731)
        ·
          refine ⟨22874700893475819555323597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15249800595650546370215731 22874700893475819555323597)
          ·
            refine ⟨8578012835053432333246349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22874700893475819555323597 8578012835053432333246349)
            ·
              refine ⟨3216754813145037124967381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8578012835053432333246349 3216754813145037124967381)
              ·
                refine ⟨75392690933086807616423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3216754813145037124967381 75392690933086807616423)
                ·
                  rfl

theorem cell23_3964322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 7].length) (baseStart_3964322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964322 prefixEnd_3964322 := by exact prefixLift 3964322
  have htrace : WordTrace (prefixWord ++ tailWord_3964322) baseStart_3964322 baseEnd_3964322 := by
    simpa [prefixWord, tailWord_3964322, baseEnd_3964322] using wordTrace_append hprefix tailTrace_3964322
  have hstable : (prefixWord ++ tailWord_3964322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964322).length < 2 ^ (prefixWord ++ tailWord_3964322).sum := by decide
  have hdescent : baseEnd_3964322 < baseStart_3964322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964333 : List Nat := [1, 5, 2, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3964333 : Nat := 118140960795 + 3964333 * 2 ^ 59
def prefixEnd_3964333 : Nat := 4983230072969 + 3 ^ 40 * 3964333 * 2
def baseEnd_3964333 : Nat := 2035608303480543262605871

theorem tailTrace_3964333 : CollatzResearch.WordTrace tailWord_3964333 prefixEnd_3964333 2035608303480543262605871 := by
  unfold tailWord_3964333
  simp only [CollatzResearch.WordTrace]
  refine ⟨144591103146906070018473653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96394068764604046678982435 144591103146906070018473653)
  ·
    refine ⟨13555415920022444064231905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144591103146906070018473653 13555415920022444064231905)
    ·
      refine ⟨10166561940016833048173929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13555415920022444064231905 10166561940016833048173929)
      ·
        refine ⟨7624921455012624786130447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10166561940016833048173929 7624921455012624786130447)
        ·
          refine ⟨11437382182518937179195671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624921455012624786130447 11437382182518937179195671)
          ·
            refine ⟨17156073273778405768793507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437382182518937179195671 17156073273778405768793507)
            ·
              refine ⟨25734109910667608653190261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17156073273778405768793507 25734109910667608653190261)
              ·
                refine ⟨2412572804125088311236587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25734109910667608653190261 2412572804125088311236587)
                ·
                  refine ⟨3618859206187632466854881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412572804125088311236587 3618859206187632466854881)
                  ·
                    refine ⟨2714144404640724350141161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3618859206187632466854881 2714144404640724350141161)
                    ·
                      refine ⟨2035608303480543262605871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714144404640724350141161 2035608303480543262605871)
                      ·
                        rfl

theorem cell23_3964333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3964333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964333 prefixEnd_3964333 := by exact prefixLift 3964333
  have htrace : WordTrace (prefixWord ++ tailWord_3964333) baseStart_3964333 baseEnd_3964333 := by
    simpa [prefixWord, tailWord_3964333, baseEnd_3964333] using wordTrace_append hprefix tailTrace_3964333
  have hstable : (prefixWord ++ tailWord_3964333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964333).length < 2 ^ (prefixWord ++ tailWord_3964333).sum := by decide
  have hdescent : baseEnd_3964333 < baseStart_3964333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964375 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_3964375 : Nat := 118140960795 + 3964375 * 2 ^ 59
def prefixEnd_3964375 : Nat := 4983230072969 + 3 ^ 40 * 3964375 * 2
def baseEnd_3964375 : Nat := 2035629869668032098280677

theorem tailTrace_3964375 : CollatzResearch.WordTrace tailWord_3964375 prefixEnd_3964375 2035629869668032098280677 := by
  unfold tailWord_3964375
  simp only [CollatzResearch.WordTrace]
  refine ⟨144592635012753911191502579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96395090008502607461001719 144592635012753911191502579)
  ·
    refine ⟨216888952519130866787253869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144592635012753911191502579 216888952519130866787253869)
    ·
      refine ⟨81333357194674075045220201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216888952519130866787253869 81333357194674075045220201)
      ·
        refine ⟨61000017896005556283915151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81333357194674075045220201 61000017896005556283915151)
        ·
          refine ⟨91500026844008334425872727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61000017896005556283915151 91500026844008334425872727)
          ·
            refine ⟨137250040266012501638809091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91500026844008334425872727 137250040266012501638809091)
            ·
              refine ⟨205875060399018752458213637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137250040266012501638809091 205875060399018752458213637)
              ·
                refine ⟨38601573824816016085915057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205875060399018752458213637 38601573824816016085915057)
                ·
                  refine ⟨28951180368612012064436293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38601573824816016085915057 28951180368612012064436293)
                  ·
                    refine ⟨5428346319114752262081805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28951180368612012064436293 5428346319114752262081805)
                    ·
                      refine ⟨2035629869668032098280677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5428346319114752262081805 2035629869668032098280677)
                      ·
                        rfl

theorem cell23_3964375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_3964375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964375 prefixEnd_3964375 := by exact prefixLift 3964375
  have htrace : WordTrace (prefixWord ++ tailWord_3964375) baseStart_3964375 baseEnd_3964375 := by
    simpa [prefixWord, tailWord_3964375, baseEnd_3964375] using wordTrace_append hprefix tailTrace_3964375
  have hstable : (prefixWord ++ tailWord_3964375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964375).length < 2 ^ (prefixWord ++ tailWord_3964375).sum := by decide
  have hdescent : baseEnd_3964375 < baseStart_3964375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964406 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_3964406 : Nat := 118140960795 + 3964406 * 2 ^ 59
def prefixEnd_3964406 : Nat := 4983230072969 + 3 ^ 40 * 3964406 * 2
def baseEnd_3964406 : Nat := 2035645787568321476993035

theorem tailTrace_3964406 : CollatzResearch.WordTrace tailWord_3964406 prefixEnd_3964406 2035645787568321476993035 := by
  unfold tailWord_3964406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037110354727600217867567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96395843783761068990587381 9037110354727600217867567)
  ·
    refine ⟨13555665532091400326801351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9037110354727600217867567 13555665532091400326801351)
    ·
      refine ⟨20333498298137100490202027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555665532091400326801351 20333498298137100490202027)
      ·
        refine ⟨30500247447205650735303041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20333498298137100490202027 30500247447205650735303041)
        ·
          refine ⟨22875185585404238051477281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30500247447205650735303041 22875185585404238051477281)
          ·
            refine ⟨17156389189053178538607961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22875185585404238051477281 17156389189053178538607961)
            ·
              refine ⟨12867291891789883903955971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17156389189053178538607961 12867291891789883903955971)
              ·
                refine ⟨19300937837684825855933957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867291891789883903955971 19300937837684825855933957)
                ·
                  refine ⟨3618925844565904847987617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19300937837684825855933957 3618925844565904847987617)
                  ·
                    refine ⟨2714194383424428635990713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3618925844565904847987617 2714194383424428635990713)
                    ·
                      refine ⟨2035645787568321476993035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714194383424428635990713 2035645787568321476993035)
                      ·
                        rfl

theorem cell23_3964406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_3964406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964406 prefixEnd_3964406 := by exact prefixLift 3964406
  have htrace : WordTrace (prefixWord ++ tailWord_3964406) baseStart_3964406 baseEnd_3964406 := by
    simpa [prefixWord, tailWord_3964406, baseEnd_3964406] using wordTrace_append hprefix tailTrace_3964406
  have hstable : (prefixWord ++ tailWord_3964406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964406).length < 2 ^ (prefixWord ++ tailWord_3964406).sum := by decide
  have hdescent : baseEnd_3964406 < baseStart_3964406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964412 : List Nat := [2, 2, 2, 1, 2, 1, 2, 6, 5]
def baseStart_3964412 : Nat := 118140960795 + 3964412 * 2 ^ 59
def prefixEnd_3964412 : Nat := 4983230072969 + 3 ^ 40 * 3964412 * 2
def baseEnd_3964412 : Nat := 226183207605805383724223

theorem tailTrace_3964412 : CollatzResearch.WordTrace tailWord_3964412 prefixEnd_3964412 226183207605805383724223 := by
  unfold tailWord_3964412
  simp only [CollatzResearch.WordTrace]
  refine ⟨72296992256809933255299745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96395989675746577673732993 72296992256809933255299745)
  ·
    refine ⟨54222744192607449941474809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72296992256809933255299745 54222744192607449941474809)
    ·
      refine ⟨40667058144455587456106107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54222744192607449941474809 40667058144455587456106107)
      ·
        refine ⟨61000587216683381184159161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40667058144455587456106107 61000587216683381184159161)
        ·
          refine ⟨45750440412512535888119371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61000587216683381184159161 45750440412512535888119371)
          ·
            refine ⟨68625660618768803832179057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45750440412512535888119371 68625660618768803832179057)
            ·
              refine ⟨51469245464076602874134293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68625660618768803832179057 51469245464076602874134293)
              ·
                refine ⟨2412620881128590759725045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51469245464076602874134293 2412620881128590759725045)
                ·
                  refine ⟨226183207605805383724223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2412620881128590759725045 226183207605805383724223)
                  ·
                    rfl

theorem cell23_3964412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_3964412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964412 prefixEnd_3964412 := by exact prefixLift 3964412
  have htrace : WordTrace (prefixWord ++ tailWord_3964412) baseStart_3964412 baseEnd_3964412 := by
    simpa [prefixWord, tailWord_3964412, baseEnd_3964412] using wordTrace_append hprefix tailTrace_3964412
  have hstable : (prefixWord ++ tailWord_3964412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964412).length < 2 ^ (prefixWord ++ tailWord_3964412).sum := by decide
  have hdescent : baseEnd_3964412 < baseStart_3964412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964423 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_3964423 : Nat := 118140960795 + 3964423 * 2 ^ 59
def prefixEnd_3964423 : Nat := 4983230072969 + 3 ^ 40 * 3964423 * 2
def baseEnd_3964423 : Nat := 2035654516739447910480457

theorem tailTrace_3964423 : CollatzResearch.WordTrace tailWord_3964423 prefixEnd_3964423 2035654516739447910480457 := by
  unfold tailWord_3964423
  simp only [CollatzResearch.WordTrace]
  refine ⟨144594385716580015389249923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96396257144386676926166615 144594385716580015389249923)
  ·
    refine ⟨216891578574870023083874885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144594385716580015389249923 216891578574870023083874885)
    ·
      refine ⟨40667170982788129328226541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216891578574870023083874885 40667170982788129328226541)
      ·
        refine ⟨15250189118545548498084953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40667170982788129328226541 15250189118545548498084953)
        ·
          refine ⟨11437641838909161373563715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15250189118545548498084953 11437641838909161373563715)
          ·
            refine ⟨17156462758363742060345573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437641838909161373563715 17156462758363742060345573)
            ·
              refine ⟨3216836767193201636314795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17156462758363742060345573 3216836767193201636314795)
              ·
                refine ⟨4825255150789802454472193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216836767193201636314795 4825255150789802454472193)
                ·
                  refine ⟨3618941363092351840854145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4825255150789802454472193 3618941363092351840854145)
                  ·
                    refine ⟨2714206022319263880640609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3618941363092351840854145 2714206022319263880640609)
                    ·
                      refine ⟨2035654516739447910480457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714206022319263880640609 2035654516739447910480457)
                      ·
                        rfl

theorem cell23_3964423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_3964423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964423 prefixEnd_3964423 := by exact prefixLift 3964423
  have htrace : WordTrace (prefixWord ++ tailWord_3964423) baseStart_3964423 baseEnd_3964423 := by
    simpa [prefixWord, tailWord_3964423, baseEnd_3964423] using wordTrace_append hprefix tailTrace_3964423
  have hstable : (prefixWord ++ tailWord_3964423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964423).length < 2 ^ (prefixWord ++ tailWord_3964423).sum := by decide
  have hdescent : baseEnd_3964423 < baseStart_3964423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964425 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 4, 5]
def baseStart_3964425 : Nat := 118140960795 + 3964425 * 2 ^ 59
def prefixEnd_3964425 : Nat := 4983230072969 + 3 ^ 40 * 3964425 * 2
def baseEnd_3964425 : Nat := 678551847900252300885149

theorem tailTrace_3964425 : CollatzResearch.WordTrace tailWord_3964425 prefixEnd_3964425 678551847900252300885149 := by
  unfold tailWord_3964425
  simp only [CollatzResearch.WordTrace]
  refine ⟨144594458662572769730822729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96396305775048513153881819 144594458662572769730822729)
  ·
    refine ⟨108445843996929577298117047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144594458662572769730822729 108445843996929577298117047)
    ·
      refine ⟨162668765995394365947175571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108445843996929577298117047 162668765995394365947175571)
      ·
        refine ⟨244003148993091548920763357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162668765995394365947175571 244003148993091548920763357)
        ·
          refine ⟨91501180872409330845286259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244003148993091548920763357 91501180872409330845286259)
          ·
            refine ⟨137251771308613996267929389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91501180872409330845286259 137251771308613996267929389)
            ·
              refine ⟨51469414240730248600473521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137251771308613996267929389 51469414240730248600473521)
              ·
                refine ⟨38602060680547686450355141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51469414240730248600473521 38602060680547686450355141)
                ·
                  refine ⟨7237886377602691209441589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38602060680547686450355141 7237886377602691209441589)
                  ·
                    refine ⟨678551847900252300885149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7237886377602691209441589 678551847900252300885149)
                    ·
                      rfl

theorem cell23_3964425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_3964425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964425 prefixEnd_3964425 := by exact prefixLift 3964425
  have htrace : WordTrace (prefixWord ++ tailWord_3964425) baseStart_3964425 baseEnd_3964425 := by
    simpa [prefixWord, tailWord_3964425, baseEnd_3964425] using wordTrace_append hprefix tailTrace_3964425
  have hstable : (prefixWord ++ tailWord_3964425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964425).length < 2 ^ (prefixWord ++ tailWord_3964425).sum := by decide
  have hdescent : baseEnd_3964425 < baseStart_3964425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964465 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3964465 : Nat := 118140960795 + 3964465 * 2 ^ 59
def prefixEnd_3964465 : Nat := 4983230072969 + 3 ^ 40 * 3964465 * 2
def baseEnd_3964465 : Nat := 2035676082926936746155263

theorem tailTrace_3964465 : CollatzResearch.WordTrace tailWord_3964465 prefixEnd_3964465 2035676082926936746155263 := by
  unfold tailWord_3964465
  simp only [CollatzResearch.WordTrace]
  refine ⟨144595917582427856562278849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96397278388285237708185899 144595917582427856562278849)
  ·
    refine ⟨108446938186820892421709137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144595917582427856562278849 108446938186820892421709137)
    ·
      refine ⟨81335203640115669316281853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108446938186820892421709137 81335203640115669316281853)
      ·
        refine ⟨30500701365043375993605695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81335203640115669316281853 30500701365043375993605695)
        ·
          refine ⟨45751052047565063990408543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30500701365043375993605695 45751052047565063990408543)
          ·
            refine ⟨68626578071347595985612815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45751052047565063990408543 68626578071347595985612815)
            ·
              refine ⟨102939867107021393978419223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68626578071347595985612815 102939867107021393978419223)
              ·
                refine ⟨154409800660532090967628835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102939867107021393978419223 154409800660532090967628835)
                ·
                  refine ⟨231614700990798136451443253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154409800660532090967628835 231614700990798136451443253)
                  ·
                    refine ⟨21713878217887325292322805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231614700990798136451443253 21713878217887325292322805)
                    ·
                      refine ⟨2035676082926936746155263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21713878217887325292322805 2035676082926936746155263)
                      ·
                        rfl

theorem cell23_3964465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3964465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964465 prefixEnd_3964465 := by exact prefixLift 3964465
  have htrace : WordTrace (prefixWord ++ tailWord_3964465) baseStart_3964465 baseEnd_3964465 := by
    simpa [prefixWord, tailWord_3964465, baseEnd_3964465] using wordTrace_append hprefix tailTrace_3964465
  have hstable : (prefixWord ++ tailWord_3964465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964465).length < 2 ^ (prefixWord ++ tailWord_3964465).sum := by decide
  have hdescent : baseEnd_3964465 < baseStart_3964465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964479 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 2, 4, 2]
def baseStart_3964479 : Nat := 118140960795 + 3964479 * 2 ^ 59
def prefixEnd_3964479 : Nat := 4983230072969 + 3 ^ 40 * 3964479 * 2
def baseEnd_3964479 : Nat := 2035683271656099691380199

theorem tailTrace_3964479 : CollatzResearch.WordTrace tailWord_3964479 prefixEnd_3964479 2035683271656099691380199 := by
  unfold tailWord_3964479
  simp only [CollatzResearch.WordTrace]
  refine ⟨144596428204377136953288491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96397618802918091302192327 144596428204377136953288491)
  ·
    refine ⟨216894642306565705429932737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144596428204377136953288491 216894642306565705429932737)
    ·
      refine ⟨162670981729924279072449553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216894642306565705429932737 162670981729924279072449553)
      ·
        refine ⟨122003236297443209304337165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162670981729924279072449553 122003236297443209304337165)
        ·
          refine ⟨45751213611541203489126437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122003236297443209304337165 45751213611541203489126437)
          ·
            refine ⟨8578352552163975654211207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45751213611541203489126437 8578352552163975654211207)
            ·
              refine ⟨12867528828245963481316811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578352552163975654211207 12867528828245963481316811)
              ·
                refine ⟨19301293242368945221975217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867528828245963481316811 19301293242368945221975217)
                ·
                  refine ⟨14475969931776708916481413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19301293242368945221975217 14475969931776708916481413)
                  ·
                    refine ⟨2714244362208132921840265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14475969931776708916481413 2714244362208132921840265)
                    ·
                      refine ⟨2035683271656099691380199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714244362208132921840265 2035683271656099691380199)
                      ·
                        rfl

theorem cell23_3964479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_3964479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964479 prefixEnd_3964479 := by exact prefixLift 3964479
  have htrace : WordTrace (prefixWord ++ tailWord_3964479) baseStart_3964479 baseEnd_3964479 := by
    simpa [prefixWord, tailWord_3964479, baseEnd_3964479] using wordTrace_append hprefix tailTrace_3964479
  have hstable : (prefixWord ++ tailWord_3964479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964479).length < 2 ^ (prefixWord ++ tailWord_3964479).sum := by decide
  have hdescent : baseEnd_3964479 < baseStart_3964479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964493 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3964493 : Nat := 118140960795 + 3964493 * 2 ^ 59
def prefixEnd_3964493 : Nat := 4983230072969 + 3 ^ 40 * 3964493 * 2
def baseEnd_3964493 : Nat := 678563486795087545535045

theorem tailTrace_3964493 : CollatzResearch.WordTrace tailWord_3964493 prefixEnd_3964493 678563486795087545535045 := by
  unfold tailWord_3964493
  simp only [CollatzResearch.WordTrace]
  refine ⟨144596938826326417344298133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96397959217550944896198755 144596938826326417344298133)
  ·
    refine ⟨6777981507484050813013975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144596938826326417344298133 6777981507484050813013975)
    ·
      refine ⟨10166972261226076219520963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777981507484050813013975 10166972261226076219520963)
      ·
        refine ⟨15250458391839114329281445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166972261226076219520963 15250458391839114329281445)
        ·
          refine ⟨2859460948469833936740271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15250458391839114329281445 2859460948469833936740271)
          ·
            refine ⟨4289191422704750905110407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859460948469833936740271 4289191422704750905110407)
            ·
              refine ⟨6433787134057126357665611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289191422704750905110407 6433787134057126357665611)
              ·
                refine ⟨9650680701085689536498417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433787134057126357665611 9650680701085689536498417)
                ·
                  refine ⟨7238010525814267152373813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9650680701085689536498417 7238010525814267152373813)
                  ·
                    refine ⟨678563486795087545535045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7238010525814267152373813 678563486795087545535045)
                    ·
                      rfl

theorem cell23_3964493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3964493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964493 prefixEnd_3964493 := by exact prefixLift 3964493
  have htrace : WordTrace (prefixWord ++ tailWord_3964493) baseStart_3964493 baseEnd_3964493 := by
    simpa [prefixWord, tailWord_3964493, baseEnd_3964493] using wordTrace_append hprefix tailTrace_3964493
  have hstable : (prefixWord ++ tailWord_3964493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964493).length < 2 ^ (prefixWord ++ tailWord_3964493).sum := by decide
  have hdescent : baseEnd_3964493 < baseStart_3964493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964505 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_3964505 : Nat := 118140960795 + 3964505 * 2 ^ 59
def prefixEnd_3964505 : Nat := 4983230072969 + 3 ^ 40 * 3964505 * 2
def baseEnd_3964505 : Nat := 2035696622153116589655079

theorem tailTrace_3964505 : CollatzResearch.WordTrace tailWord_3964505 prefixEnd_3964505 2035696622153116589655079 := by
  unfold tailWord_3964505
  simp only [CollatzResearch.WordTrace]
  refine ⟨144597376502282943393734969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96398251001521962262489979 144597376502282943393734969)
  ·
    refine ⟨108448032376712207545301227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144597376502282943393734969 108448032376712207545301227)
    ·
      refine ⟨162672048565068311317951841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108448032376712207545301227 162672048565068311317951841)
      ·
        refine ⟨122004036423801233488463881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162672048565068311317951841 122004036423801233488463881)
        ·
          refine ⟨91503027317850925116347911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122004036423801233488463881 91503027317850925116347911)
          ·
            refine ⟨137254540976776387674521867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91503027317850925116347911 137254540976776387674521867)
            ·
              refine ⟨205881811465164581511782801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137254540976776387674521867 205881811465164581511782801)
              ·
                refine ⟨154411358598873436133837101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205881811465164581511782801 154411358598873436133837101)
                ·
                  refine ⟨57904259474577538550188913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154411358598873436133837101 57904259474577538550188913)
                  ·
                    refine ⟨43428194605933153912641685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57904259474577538550188913 43428194605933153912641685)
                    ·
                      refine ⟨2035696622153116589655079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43428194605933153912641685 2035696622153116589655079)
                      ·
                        rfl

theorem cell23_3964505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_3964505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964505 prefixEnd_3964505 := by exact prefixLift 3964505
  have htrace : WordTrace (prefixWord ++ tailWord_3964505) baseStart_3964505 baseEnd_3964505 := by
    simpa [prefixWord, tailWord_3964505, baseEnd_3964505] using wordTrace_append hprefix tailTrace_3964505
  have hstable : (prefixWord ++ tailWord_3964505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964505).length < 2 ^ (prefixWord ++ tailWord_3964505).sum := by decide
  have hdescent : baseEnd_3964505 < baseStart_3964505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964522 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3964522 : Nat := 118140960795 + 3964522 * 2 ^ 59
def prefixEnd_3964522 : Nat := 4983230072969 + 3 ^ 40 * 3964522 * 2
def baseEnd_3964522 : Nat := 2035705351324243023142501

theorem tailTrace_3964522 : CollatzResearch.WordTrace tailWord_3964522 prefixEnd_3964522 2035705351324243023142501 := by
  unfold tailWord_3964522
  simp only [CollatzResearch.WordTrace]
  refine ⟨36149499135805338824275955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96398664362147570198069213 36149499135805338824275955)
  ·
    refine ⟨54224248703708008236413933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36149499135805338824275955 54224248703708008236413933)
    ·
      refine ⟨20334093263890503088655225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54224248703708008236413933 20334093263890503088655225)
      ·
        refine ⟨15250569947917877316491419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20334093263890503088655225 15250569947917877316491419)
        ·
          refine ⟨22875854921876815974737129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15250569947917877316491419 22875854921876815974737129)
          ·
            refine ⟨17156891191407611981052847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22875854921876815974737129 17156891191407611981052847)
            ·
              refine ⟨25735336787111417971579271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17156891191407611981052847 25735336787111417971579271)
              ·
                refine ⟨38603005180667126957368907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25735336787111417971579271 38603005180667126957368907)
                ·
                  refine ⟨57904507771000690436053361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38603005180667126957368907 57904507771000690436053361)
                  ·
                    refine ⟨43428380828250517827040021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57904507771000690436053361 43428380828250517827040021)
                    ·
                      refine ⟨2035705351324243023142501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43428380828250517827040021 2035705351324243023142501)
                      ·
                        rfl

theorem cell23_3964522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3964522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964522 prefixEnd_3964522 := by exact prefixLift 3964522
  have htrace : WordTrace (prefixWord ++ tailWord_3964522) baseStart_3964522 baseEnd_3964522 := by
    simpa [prefixWord, tailWord_3964522, baseEnd_3964522] using wordTrace_append hprefix tailTrace_3964522
  have hstable : (prefixWord ++ tailWord_3964522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964522).length < 2 ^ (prefixWord ++ tailWord_3964522).sum := by decide
  have hdescent : baseEnd_3964522 < baseStart_3964522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964549 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_3964549 : Nat := 118140960795 + 3964549 * 2 ^ 59
def prefixEnd_3964549 : Nat := 4983230072969 + 3 ^ 40 * 3964549 * 2
def baseEnd_3964549 : Nat := 678573071767304805834959

theorem tailTrace_3964549 : CollatzResearch.WordTrace tailWord_3964549 prefixEnd_3964549 678573071767304805834959 := by
  unfold tailWord_3964549
  simp only [CollatzResearch.WordTrace]
  refine ⟨144598981314123538908336701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96399320876082359272224467 144598981314123538908336701)
  ·
    refine ⟨54224617992796327090626263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144598981314123538908336701 54224617992796327090626263)
    ·
      refine ⟨81336926989194490635939395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54224617992796327090626263 81336926989194490635939395)
      ·
        refine ⟨122005390483791735953909093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81336926989194490635939395 122005390483791735953909093)
        ·
          refine ⟨22876010715710950491357955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122005390483791735953909093 22876010715710950491357955)
          ·
            refine ⟨34314016073566425737036933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22876010715710950491357955 34314016073566425737036933)
            ·
              refine ⟨6433878013793704825694425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34314016073566425737036933 6433878013793704825694425)
              ·
                refine ⟨4825408510345278619270819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6433878013793704825694425 4825408510345278619270819)
                ·
                  refine ⟨7238112765517917928906229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825408510345278619270819 7238112765517917928906229)
                  ·
                    refine ⟨678573071767304805834959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7238112765517917928906229 678573071767304805834959)
                    ·
                      rfl

theorem cell23_3964549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_3964549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964549 prefixEnd_3964549 := by exact prefixLift 3964549
  have htrace : WordTrace (prefixWord ++ tailWord_3964549) baseStart_3964549 baseEnd_3964549 := by
    simpa [prefixWord, tailWord_3964549, baseEnd_3964549] using wordTrace_append hprefix tailTrace_3964549
  have hstable : (prefixWord ++ tailWord_3964549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964549).length < 2 ^ (prefixWord ++ tailWord_3964549).sum := by decide
  have hdescent : baseEnd_3964549 < baseStart_3964549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964579 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 2, 4]
def baseStart_3964579 : Nat := 118140960795 + 3964579 * 2 ^ 59
def prefixEnd_3964579 : Nat := 4983230072969 + 3 ^ 40 * 3964579 * 2
def baseEnd_3964579 : Nat := 678578206573849766709913

theorem tailTrace_3964579 : CollatzResearch.WordTrace tailWord_3964579 prefixEnd_3964579 678578206573849766709913 := by
  unfold tailWord_3964579
  simp only [CollatzResearch.WordTrace]
  refine ⟨144600075504014854031928791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96400050336009902687952527 144600075504014854031928791)
  ·
    refine ⟨216900113256022281047893187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144600075504014854031928791 216900113256022281047893187)
    ·
      refine ⟨325350169884033421571839781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216900113256022281047893187 325350169884033421571839781)
      ·
        refine ⟨61003156853256266544719959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325350169884033421571839781 61003156853256266544719959)
        ·
          refine ⟨91504735279884399817079939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61003156853256266544719959 91504735279884399817079939)
          ·
            refine ⟨137257102919826599725619909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91504735279884399817079939 137257102919826599725619909)
            ·
              refine ⟨25735706797467487448553733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137257102919826599725619909 25735706797467487448553733)
              ·
                refine ⟨4825445024525153896603825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25735706797467487448553733 4825445024525153896603825)
                ·
                  refine ⟨3619083768393865422452869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4825445024525153896603825 3619083768393865422452869)
                  ·
                    refine ⟨678578206573849766709913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3619083768393865422452869 678578206573849766709913)
                    ·
                      rfl

theorem cell23_3964579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 4].length) (baseStart_3964579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964579 prefixEnd_3964579 := by exact prefixLift 3964579
  have htrace : WordTrace (prefixWord ++ tailWord_3964579) baseStart_3964579 baseEnd_3964579 := by
    simpa [prefixWord, tailWord_3964579, baseEnd_3964579] using wordTrace_append hprefix tailTrace_3964579
  have hstable : (prefixWord ++ tailWord_3964579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964579).length < 2 ^ (prefixWord ++ tailWord_3964579).sum := by decide
  have hdescent : baseEnd_3964579 < baseStart_3964579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964580 : List Nat := [2, 3, 1, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_3964580 : Nat := 118140960795 + 3964580 * 2 ^ 59
def prefixEnd_3964580 : Nat := 4983230072969 + 3 ^ 40 * 3964580 * 2
def baseEnd_3964580 : Nat := 2035735133202203796217235

theorem tailTrace_3964580 : CollatzResearch.WordTrace tailWord_3964580 prefixEnd_3964580 2035735133202203796217235 := by
  unfold tailWord_3964580
  simp only [CollatzResearch.WordTrace]
  refine ⟨72300055988505615601357597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96400074651340820801810129 72300055988505615601357597)
  ·
    refine ⟨27112520995689605850509099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72300055988505615601357597 27112520995689605850509099)
    ·
      refine ⟨40668781493534408775763649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27112520995689605850509099 40668781493534408775763649)
      ·
        refine ⟨30501586120150806581822737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40668781493534408775763649 30501586120150806581822737)
        ·
          refine ⟨22876189590113104936367053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30501586120150806581822737 22876189590113104936367053)
          ·
            refine ⟨8578571096292414351137645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22876189590113104936367053 8578571096292414351137645)
            ·
              refine ⟨3216964161109655381676617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8578571096292414351137645 3216964161109655381676617)
              ·
                refine ⟨2412723120832241536257463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216964161109655381676617 2412723120832241536257463)
                ·
                  refine ⟨3619084681248362304386195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412723120832241536257463 3619084681248362304386195)
                  ·
                    refine ⟨5428627021872543456579293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619084681248362304386195 5428627021872543456579293)
                    ·
                      refine ⟨2035735133202203796217235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5428627021872543456579293 2035735133202203796217235)
                      ·
                        rfl

theorem cell23_3964580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_3964580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964580 prefixEnd_3964580 := by exact prefixLift 3964580
  have htrace : WordTrace (prefixWord ++ tailWord_3964580) baseStart_3964580 baseEnd_3964580 := by
    simpa [prefixWord, tailWord_3964580, baseEnd_3964580] using wordTrace_append hprefix tailTrace_3964580
  have hstable : (prefixWord ++ tailWord_3964580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964580).length < 2 ^ (prefixWord ++ tailWord_3964580).sum := by decide
  have hdescent : baseEnd_3964580 < baseStart_3964580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964589 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3964589 : Nat := 118140960795 + 3964589 * 2 ^ 59
def prefixEnd_3964589 : Nat := 4983230072969 + 3 ^ 40 * 3964589 * 2
def baseEnd_3964589 : Nat := 2035739754528094261004693

theorem tailTrace_3964589 : CollatzResearch.WordTrace tailWord_3964589 prefixEnd_3964589 2035739754528094261004693 := by
  unfold tailWord_3964589
  simp only [CollatzResearch.WordTrace]
  refine ⟨144600440233978625739792821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96400293489319083826528547 144600440233978625739792821)
  ·
    refine ⟨13556291271935496163105577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144600440233978625739792821 13556291271935496163105577)
    ·
      refine ⟨10167218453951622122329183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13556291271935496163105577 10167218453951622122329183)
      ·
        refine ⟨15250827680927433183493775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10167218453951622122329183 15250827680927433183493775)
        ·
          refine ⟨22876241521391149775240663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15250827680927433183493775 22876241521391149775240663)
          ·
            refine ⟨34314362282086724662860995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22876241521391149775240663 34314362282086724662860995)
            ·
              refine ⟨51471543423130086994291493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34314362282086724662860995 51471543423130086994291493)
              ·
                refine ⟨9650914391836891311429655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51471543423130086994291493 9650914391836891311429655)
                ·
                  refine ⟨14476371587755336967144483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9650914391836891311429655 14476371587755336967144483)
                  ·
                    refine ⟨21714557381633005450716725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14476371587755336967144483 21714557381633005450716725)
                    ·
                      refine ⟨2035739754528094261004693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21714557381633005450716725 2035739754528094261004693)
                      ·
                        rfl

theorem cell23_3964589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3964589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964589 prefixEnd_3964589 := by exact prefixLift 3964589
  have htrace : WordTrace (prefixWord ++ tailWord_3964589) baseStart_3964589 baseEnd_3964589 := by
    simpa [prefixWord, tailWord_3964589, baseEnd_3964589] using wordTrace_append hprefix tailTrace_3964589
  have hstable : (prefixWord ++ tailWord_3964589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964589).length < 2 ^ (prefixWord ++ tailWord_3964589).sum := by decide
  have hdescent : baseEnd_3964589 < baseStart_3964589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964606 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_3964606 : Nat := 118140960795 + 3964606 * 2 ^ 59
def prefixEnd_3964606 : Nat := 4983230072969 + 3 ^ 40 * 3964606 * 2
def baseEnd_3964606 : Nat := 2035748483699220694492115

theorem tailTrace_3964606 : CollatzResearch.WordTrace tailWord_3964606 prefixEnd_3964606 2035748483699220694492115 := by
  unfold tailWord_3964606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18075132534364629705395209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96400706849944691762107781 18075132534364629705395209)
  ·
    refine ⟨13556349400773472279046407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18075132534364629705395209 13556349400773472279046407)
    ·
      refine ⟨20334524101160208418569611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13556349400773472279046407 20334524101160208418569611)
      ·
        refine ⟨30501786151740312627854417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20334524101160208418569611 30501786151740312627854417)
        ·
          refine ⟨22876339613805234470890813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30501786151740312627854417 22876339613805234470890813)
          ·
            refine ⟨8578627355176962926584055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22876339613805234470890813 8578627355176962926584055)
            ·
              refine ⟨12867941032765444389876083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578627355176962926584055 12867941032765444389876083)
              ·
                refine ⟨19301911549148166584814125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867941032765444389876083 19301911549148166584814125)
                ·
                  refine ⟨7238216830930562469305297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19301911549148166584814125 7238216830930562469305297)
                  ·
                    refine ⟨5428662623197921851978973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7238216830930562469305297 5428662623197921851978973)
                    ·
                      refine ⟨2035748483699220694492115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5428662623197921851978973 2035748483699220694492115)
                      ·
                        rfl

theorem cell23_3964606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_3964606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964606 prefixEnd_3964606 := by exact prefixLift 3964606
  have htrace : WordTrace (prefixWord ++ tailWord_3964606) baseStart_3964606 baseEnd_3964606 := by
    simpa [prefixWord, tailWord_3964606, baseEnd_3964606] using wordTrace_append hprefix tailTrace_3964606
  have hstable : (prefixWord ++ tailWord_3964606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964606).length < 2 ^ (prefixWord ++ tailWord_3964606).sum := by decide
  have hdescent : baseEnd_3964606 < baseStart_3964606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964619 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 3]
def baseStart_3964619 : Nat := 118140960795 + 3964619 * 2 ^ 59
def prefixEnd_3964619 : Nat := 4983230072969 + 3 ^ 40 * 3964619 * 2
def baseEnd_3964619 : Nat := 2035755158947729143629555

theorem tailTrace_3964619 : CollatzResearch.WordTrace tailWord_3964619 prefixEnd_3964619 2035755158947729143629555 := by
  unfold tailWord_3964619
  simp only [CollatzResearch.WordTrace]
  refine ⟨144601534423869940863384911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96401022949246627242256607 144601534423869940863384911)
  ·
    refine ⟨216902301635804911295077367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144601534423869940863384911 216902301635804911295077367)
    ·
      refine ⟨325353452453707366942616051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216902301635804911295077367 325353452453707366942616051)
      ·
        refine ⟨488030178680561050413924077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325353452453707366942616051 488030178680561050413924077)
        ·
          refine ⟨183011317005210393905221529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488030178680561050413924077 183011317005210393905221529)
          ·
            refine ⟨137258487753907795428916147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183011317005210393905221529 137258487753907795428916147)
            ·
              refine ⟨205887731630861693143374221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137258487753907795428916147 205887731630861693143374221)
              ·
                refine ⟨77207899361573134928765333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205887731630861693143374221 77207899361573134928765333)
                ·
                  refine ⟨3619120282573740699785875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77207899361573134928765333 3619120282573740699785875)
                  ·
                    refine ⟨5428680423860611049678813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619120282573740699785875 5428680423860611049678813)
                    ·
                      refine ⟨2035755158947729143629555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5428680423860611049678813 2035755158947729143629555)
                      ·
                        rfl

theorem cell23_3964619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 3].length) (baseStart_3964619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964619 prefixEnd_3964619 := by exact prefixLift 3964619
  have htrace : WordTrace (prefixWord ++ tailWord_3964619) baseStart_3964619 baseEnd_3964619 := by
    simpa [prefixWord, tailWord_3964619, baseEnd_3964619] using wordTrace_append hprefix tailTrace_3964619
  have hstable : (prefixWord ++ tailWord_3964619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964619).length < 2 ^ (prefixWord ++ tailWord_3964619).sum := by decide
  have hdescent : baseEnd_3964619 < baseStart_3964619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964652 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_3964652 : Nat := 118140960795 + 3964652 * 2 ^ 59
def prefixEnd_3964652 : Nat := 4983230072969 + 3 ^ 40 * 3964652 * 2
def baseEnd_3964652 : Nat := 678590701269775838172301

theorem tailTrace_3964652 : CollatzResearch.WordTrace tailWord_3964652 prefixEnd_3964652 678590701269775838172301 := by
  unfold tailWord_3964652
  simp only [CollatzResearch.WordTrace]
  refine ⟨72301369016375193749668105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96401825355166924999557473 72301369016375193749668105)
  ·
    refine ⟨54226026762281395312251079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72301369016375193749668105 54226026762281395312251079)
    ·
      refine ⟨81339040143422092968376619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54226026762281395312251079 81339040143422092968376619)
      ·
        refine ⟨122008560215133139452564929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81339040143422092968376619 122008560215133139452564929)
        ·
          refine ⟨91506420161349854589423697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122008560215133139452564929 91506420161349854589423697)
          ·
            refine ⟨68629815121012390942067773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91506420161349854589423697 68629815121012390942067773)
            ·
              refine ⟨25736180670379646603275415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68629815121012390942067773 25736180670379646603275415)
              ·
                refine ⟨38604271005569469904913123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25736180670379646603275415 38604271005569469904913123)
                ·
                  refine ⟨57906406508354204857369685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38604271005569469904913123 57906406508354204857369685)
                  ·
                    refine ⟨678590701269775838172301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57906406508354204857369685 678590701269775838172301)
                    ·
                      rfl

theorem cell23_3964652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_3964652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964652 prefixEnd_3964652 := by exact prefixLift 3964652
  have htrace : WordTrace (prefixWord ++ tailWord_3964652) baseStart_3964652 baseEnd_3964652 := by
    simpa [prefixWord, tailWord_3964652, baseEnd_3964652] using wordTrace_append hprefix tailTrace_3964652
  have hstable : (prefixWord ++ tailWord_3964652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964652).length < 2 ^ (prefixWord ++ tailWord_3964652).sum := by decide
  have hdescent : baseEnd_3964652 < baseStart_3964652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964653 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3964653 : Nat := 118140960795 + 3964653 * 2 ^ 59
def prefixEnd_3964653 : Nat := 4983230072969 + 3 ^ 40 * 3964653 * 2
def baseEnd_3964653 : Nat := 2035772617289982010604399

theorem tailTrace_3964653 : CollatzResearch.WordTrace tailWord_3964653 prefixEnd_3964653 2035772617289982010604399 := by
  unfold tailWord_3964653
  simp only [CollatzResearch.WordTrace]
  refine ⟨144602774505746764670122613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96401849670497843113415075 144602774505746764670122613)
  ·
    refine ⟨13556510109913759187823995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144602774505746764670122613 13556510109913759187823995)
    ·
      refine ⟨20334765164870638781735993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13556510109913759187823995 20334765164870638781735993)
      ·
        refine ⟨15251073873652979086301995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20334765164870638781735993 15251073873652979086301995)
        ·
          refine ⟨22876610810479468629452993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15251073873652979086301995 22876610810479468629452993)
          ·
            refine ⟨17157458107859601472089745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22876610810479468629452993 17157458107859601472089745)
            ·
              refine ⟨12868093580894701104067309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17157458107859601472089745 12868093580894701104067309)
              ·
                refine ⟨4825535092835512914025241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12868093580894701104067309 4825535092835512914025241)
                ·
                  refine ⟨3619151319626634685518931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4825535092835512914025241 3619151319626634685518931)
                  ·
                    refine ⟨5428726979439952028278397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619151319626634685518931 5428726979439952028278397)
                    ·
                      refine ⟨2035772617289982010604399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5428726979439952028278397 2035772617289982010604399)
                      ·
                        rfl

theorem cell23_3964653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3964653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964653 prefixEnd_3964653 := by exact prefixLift 3964653
  have htrace : WordTrace (prefixWord ++ tailWord_3964653) baseStart_3964653 baseEnd_3964653 := by
    simpa [prefixWord, tailWord_3964653, baseEnd_3964653] using wordTrace_append hprefix tailTrace_3964653
  have hstable : (prefixWord ++ tailWord_3964653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964653).length < 2 ^ (prefixWord ++ tailWord_3964653).sum := by decide
  have hdescent : baseEnd_3964653 < baseStart_3964653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964693 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_3964693 : Nat := 118140960795 + 3964693 * 2 ^ 59
def prefixEnd_3964693 : Nat := 4983230072969 + 3 ^ 40 * 3964693 * 2
def baseEnd_3964693 : Nat := 2035793156516161854104215

theorem tailTrace_3964693 : CollatzResearch.WordTrace tailWord_3964693 prefixEnd_3964693 2035793156516161854104215 := by
  unfold tailWord_3964693
  simp only [CollatzResearch.WordTrace]
  refine ⟨144604233425601851501578733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96402822283734567667719155 144604233425601851501578733)
  ·
    refine ⟨54226587534600694313092025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144604233425601851501578733 54226587534600694313092025)
    ·
      refine ⟨40669940650950520734819019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54226587534600694313092025 40669940650950520734819019)
      ·
        refine ⟨61004910976425781102228529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40669940650950520734819019 61004910976425781102228529)
        ·
          refine ⟨45753683232319335826671397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61004910976425781102228529 45753683232319335826671397)
          ·
            refine ⟨8578815606059875467500887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45753683232319335826671397 8578815606059875467500887)
            ·
              refine ⟨12868223409089813201251331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578815606059875467500887 12868223409089813201251331)
              ·
                refine ⟨19302335113634719801876997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12868223409089813201251331 19302335113634719801876997)
                ·
                  refine ⟨3619187833806509962851937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19302335113634719801876997 3619187833806509962851937)
                  ·
                    refine ⟨2714390875354882472138953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3619187833806509962851937 2714390875354882472138953)
                    ·
                      refine ⟨2035793156516161854104215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714390875354882472138953 2035793156516161854104215)
                      ·
                        rfl

theorem cell23_3964693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_3964693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964693 prefixEnd_3964693 := by exact prefixLift 3964693
  have htrace : WordTrace (prefixWord ++ tailWord_3964693) baseStart_3964693 baseEnd_3964693 := by
    simpa [prefixWord, tailWord_3964693, baseEnd_3964693] using wordTrace_append hprefix tailTrace_3964693
  have hstable : (prefixWord ++ tailWord_3964693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964693).length < 2 ^ (prefixWord ++ tailWord_3964693).sum := by decide
  have hdescent : baseEnd_3964693 < baseStart_3964693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964733 : List Nat := [1, 4, 1, 4, 1, 1, 3, 3, 5]
def baseStart_3964733 : Nat := 118140960795 + 3964733 * 2 ^ 59
def prefixEnd_3964733 : Nat := 4983230072969 + 3 ^ 40 * 3964733 * 2
def baseEnd_3964733 : Nat := 226201521749149077511559

theorem tailTrace_3964733 : CollatzResearch.WordTrace tailWord_3964733 prefixEnd_3964733 226201521749149077511559 := by
  unfold tailWord_3964733
  simp only [CollatzResearch.WordTrace]
  refine ⟨144605692345456938333034853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96403794896971292222023235 144605692345456938333034853)
  ·
    refine ⟨27113567314773175937444035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144605692345456938333034853 27113567314773175937444035)
    ·
      refine ⟨40670350972159763906166053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27113567314773175937444035 40670350972159763906166053)
      ·
        refine ⟨7625690807279955732406135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40670350972159763906166053 7625690807279955732406135)
        ·
          refine ⟨11438536210919933598609203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625690807279955732406135 11438536210919933598609203)
          ·
            refine ⟨17157804316379900397913805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438536210919933598609203 17157804316379900397913805)
            ·
              refine ⟨6434176618642462649217677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17157804316379900397913805 6434176618642462649217677)
              ·
                refine ⟨2412816231990923493456629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6434176618642462649217677 2412816231990923493456629)
                ·
                  refine ⟨226201521749149077511559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2412816231990923493456629 226201521749149077511559)
                  ·
                    rfl

theorem cell23_3964733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_3964733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964733 prefixEnd_3964733 := by exact prefixLift 3964733
  have htrace : WordTrace (prefixWord ++ tailWord_3964733) baseStart_3964733 baseEnd_3964733 := by
    simpa [prefixWord, tailWord_3964733, baseEnd_3964733] using wordTrace_append hprefix tailTrace_3964733
  have hstable : (prefixWord ++ tailWord_3964733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964733).length < 2 ^ (prefixWord ++ tailWord_3964733).sum := by decide
  have hdescent : baseEnd_3964733 < baseStart_3964733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964756 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3964756 : Nat := 118140960795 + 3964756 * 2 ^ 59
def prefixEnd_3964756 : Nat := 4983230072969 + 3 ^ 40 * 3964756 * 2
def baseEnd_3964756 : Nat := 2035825505797395107616425

theorem tailTrace_3964756 : CollatzResearch.WordTrace tailWord_3964756 prefixEnd_3964756 2035825505797395107616425 := by
  unfold tailWord_3964756
  simp only [CollatzResearch.WordTrace]
  refine ⟨72303265612186806630561061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96404354149582408840748081 72303265612186806630561061)
  ·
    refine ⟨13556862302285026243230199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72303265612186806630561061 13556862302285026243230199)
    ·
      refine ⟨20335293453427539364845299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13556862302285026243230199 20335293453427539364845299)
      ·
        refine ⟨30502940180141309047267949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20335293453427539364845299 30502940180141309047267949)
        ·
          refine ⟨11438602567552990892725481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30502940180141309047267949 11438602567552990892725481)
          ·
            refine ⟨8578951925664743169544111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11438602567552990892725481 8578951925664743169544111)
            ·
              refine ⟨12868427888497114754316167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578951925664743169544111 12868427888497114754316167)
              ·
                refine ⟨19302641832745672131474251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12868427888497114754316167 19302641832745672131474251)
                ·
                  refine ⟨28953962749118508197211377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19302641832745672131474251 28953962749118508197211377)
                  ·
                    refine ⟨21715472061838881147908533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28953962749118508197211377 21715472061838881147908533)
                    ·
                      refine ⟨2035825505797395107616425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21715472061838881147908533 2035825505797395107616425)
                      ·
                        rfl

theorem cell23_3964756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3964756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964756 prefixEnd_3964756 := by exact prefixLift 3964756
  have htrace : WordTrace (prefixWord ++ tailWord_3964756) baseStart_3964756 baseEnd_3964756 := by
    simpa [prefixWord, tailWord_3964756, baseEnd_3964756] using wordTrace_append hprefix tailTrace_3964756
  have hstable : (prefixWord ++ tailWord_3964756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964756).length < 2 ^ (prefixWord ++ tailWord_3964756).sum := by decide
  have hdescent : baseEnd_3964756 < baseStart_3964756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964776 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 5, 4]
def baseStart_3964776 : Nat := 118140960795 + 3964776 * 2 ^ 59
def prefixEnd_3964776 : Nat := 4983230072969 + 3 ^ 40 * 3964776 * 2
def baseEnd_3964776 : Nat := 678611925136828343122111

theorem tailTrace_3964776 : CollatzResearch.WordTrace tailWord_3964776 prefixEnd_3964776 678611925136828343122111 := by
  unfold tailWord_3964776
  simp only [CollatzResearch.WordTrace]
  refine ⟨72303630342150578338425091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96404840456200771117900121 72303630342150578338425091)
  ·
    refine ⟨108455445513225867507637637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72303630342150578338425091 108455445513225867507637637)
    ·
      refine ⟨20335396033729850157682057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108455445513225867507637637 20335396033729850157682057)
      ·
        refine ⟨15251547025297387618261543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20335396033729850157682057 15251547025297387618261543)
        ·
          refine ⟨22877320537946081427392315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15251547025297387618261543 22877320537946081427392315)
          ·
            refine ⟨34315980806919122141088473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22877320537946081427392315 34315980806919122141088473)
            ·
              refine ⟨25736985605189341605816355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34315980806919122141088473 25736985605189341605816355)
              ·
                refine ⟨38605478407784012408724533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25736985605189341605816355 38605478407784012408724533)
                ·
                  refine ⟨3619263600729751163317925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38605478407784012408724533 3619263600729751163317925)
                  ·
                    refine ⟨678611925136828343122111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3619263600729751163317925 678611925136828343122111)
                    ·
                      rfl

theorem cell23_3964776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_3964776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964776 prefixEnd_3964776 := by exact prefixLift 3964776
  have htrace : WordTrace (prefixWord ++ tailWord_3964776) baseStart_3964776 baseEnd_3964776 := by
    simpa [prefixWord, tailWord_3964776, baseEnd_3964776] using wordTrace_append hprefix tailTrace_3964776
  have hstable : (prefixWord ++ tailWord_3964776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964776).length < 2 ^ (prefixWord ++ tailWord_3964776).sum := by decide
  have hdescent : baseEnd_3964776 < baseStart_3964776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964793 : List Nat := [1, 2, 1, 3, 2, 2, 2, 5, 1, 4]
def baseStart_3964793 : Nat := 118140960795 + 3964793 * 2 ^ 59
def prefixEnd_3964793 : Nat := 4983230072969 + 3 ^ 40 * 3964793 * 2
def baseEnd_3964793 : Nat := 678614834860537154284585

theorem tailTrace_3964793 : CollatzResearch.WordTrace tailWord_3964793 prefixEnd_3964793 678614834860537154284585 := by
  unfold tailWord_3964793
  simp only [CollatzResearch.WordTrace]
  refine ⟨144607880725239568580219033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96405253816826379053479355 144607880725239568580219033)
  ·
    refine ⟨108455910543929676435164275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144607880725239568580219033 108455910543929676435164275)
    ·
      refine ⟨162683865815894514652746413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108455910543929676435164275 162683865815894514652746413)
      ·
        refine ⟨61006449680960442994779905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162683865815894514652746413 61006449680960442994779905)
        ·
          refine ⟨45754837260720332246084929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61006449680960442994779905 45754837260720332246084929)
          ·
            refine ⟨34316127945540249184563697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45754837260720332246084929 34316127945540249184563697)
            ·
              refine ⟨25737095959155186888422773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34316127945540249184563697 25737095959155186888422773)
              ·
                refine ⟨2412852746170798770789635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25737095959155186888422773 2412852746170798770789635)
                ·
                  refine ⟨3619279119256198156184453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412852746170798770789635 3619279119256198156184453)
                  ·
                    refine ⟨678614834860537154284585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3619279119256198156184453 678614834860537154284585)
                    ·
                      rfl

theorem cell23_3964793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 4].length) (baseStart_3964793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964793 prefixEnd_3964793 := by exact prefixLift 3964793
  have htrace : WordTrace (prefixWord ++ tailWord_3964793) baseStart_3964793 baseEnd_3964793 := by
    simpa [prefixWord, tailWord_3964793, baseEnd_3964793] using wordTrace_append hprefix tailTrace_3964793
  have hstable : (prefixWord ++ tailWord_3964793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964793).length < 2 ^ (prefixWord ++ tailWord_3964793).sum := by decide
  have hdescent : baseEnd_3964793 < baseStart_3964793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964809 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_3964809 : Nat := 118140960795 + 3964809 * 2 ^ 59
def prefixEnd_3964809 : Nat := 4983230072969 + 3 ^ 40 * 3964809 * 2
def baseEnd_3964809 : Nat := 2035852720272083400253681

theorem tailTrace_3964809 : CollatzResearch.WordTrace tailWord_3964809 prefixEnd_3964809 2035852720272083400253681 := by
  unfold tailWord_3964809
  simp only [CollatzResearch.WordTrace]
  refine ⟨144608464293181603312801481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96405642862121068875200987 144608464293181603312801481)
  ·
    refine ⟨108456348219886202484601111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144608464293181603312801481 108456348219886202484601111)
    ·
      refine ⟨162684522329829303726901667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108456348219886202484601111 162684522329829303726901667)
      ·
        refine ⟨244026783494743955590352501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162684522329829303726901667 244026783494743955590352501)
        ·
          refine ⟨22877510952632245836595547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244026783494743955590352501 22877510952632245836595547)
          ·
            refine ⟨34316266428948368754893321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22877510952632245836595547 34316266428948368754893321)
            ·
              refine ⟨25737199821711276566169991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34316266428948368754893321 25737199821711276566169991)
              ·
                refine ⟨38605799732566914849254987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25737199821711276566169991 38605799732566914849254987)
                ·
                  refine ⟨57908699598850372273882481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38605799732566914849254987 57908699598850372273882481)
                  ·
                    refine ⟨43431524699137779205411861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57908699598850372273882481 43431524699137779205411861)
                    ·
                      refine ⟨2035852720272083400253681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43431524699137779205411861 2035852720272083400253681)
                      ·
                        rfl

theorem cell23_3964809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_3964809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964809 prefixEnd_3964809 := by exact prefixLift 3964809
  have htrace : WordTrace (prefixWord ++ tailWord_3964809) baseStart_3964809 baseEnd_3964809 := by
    simpa [prefixWord, tailWord_3964809, baseEnd_3964809] using wordTrace_append hprefix tailTrace_3964809
  have hstable : (prefixWord ++ tailWord_3964809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964809).length < 2 ^ (prefixWord ++ tailWord_3964809).sum := by decide
  have hdescent : baseEnd_3964809 < baseStart_3964809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964836 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_3964836 : Nat := 118140960795 + 3964836 * 2 ^ 59
def prefixEnd_3964836 : Nat := 4983230072969 + 3 ^ 40 * 3964836 * 2
def baseEnd_3964836 : Nat := 678622194749918264872019

theorem tailTrace_3964836 : CollatzResearch.WordTrace tailWord_3964836 prefixEnd_3964836 678622194749918264872019 := by
  unfold tailWord_3964836
  simp only [CollatzResearch.WordTrace]
  refine ⟨72304724532041893462017181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96406299376055857949356241 72304724532041893462017181)
  ·
    refine ⟨27114271699515710048256443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72304724532041893462017181 27114271699515710048256443)
    ·
      refine ⟨40671407549273565072384665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27114271699515710048256443 40671407549273565072384665)
      ·
        refine ⟨30503555661955173804288499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40671407549273565072384665 30503555661955173804288499)
        ·
          refine ⟨45755333492932760706432749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30503555661955173804288499 45755333492932760706432749)
          ·
            refine ⟨17158250059849785264912281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45755333492932760706432749 17158250059849785264912281)
            ·
              refine ⟨12868687544887338948684211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17158250059849785264912281 12868687544887338948684211)
              ·
                refine ⟨19303031317331008423026317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12868687544887338948684211 19303031317331008423026317)
                ·
                  refine ⟨7238636743999128158634869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19303031317331008423026317 7238636743999128158634869)
                  ·
                    refine ⟨678622194749918264872019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7238636743999128158634869 678622194749918264872019)
                    ·
                      rfl

theorem cell23_3964836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_3964836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964836 prefixEnd_3964836 := by exact prefixLift 3964836
  have htrace : WordTrace (prefixWord ++ tailWord_3964836) baseStart_3964836 baseEnd_3964836 := by
    simpa [prefixWord, tailWord_3964836, baseEnd_3964836] using wordTrace_append hprefix tailTrace_3964836
  have hstable : (prefixWord ++ tailWord_3964836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964836).length < 2 ^ (prefixWord ++ tailWord_3964836).sum := by decide
  have hdescent : baseEnd_3964836 < baseStart_3964836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964853 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3964853 : Nat := 118140960795 + 3964853 * 2 ^ 59
def prefixEnd_3964853 : Nat := 4983230072969 + 3 ^ 40 * 3964853 * 2
def baseEnd_3964853 : Nat := 678625104473627076034493

theorem tailTrace_3964853 : CollatzResearch.WordTrace tailWord_3964853 prefixEnd_3964853 678625104473627076034493 := by
  unfold tailWord_3964853
  simp only [CollatzResearch.WordTrace]
  refine ⟨144610069105022198827403213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96406712736681465884935475 144610069105022198827403213)
  ·
    refine ⟨54228775914383324560276205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144610069105022198827403213 54228775914383324560276205)
    ·
      refine ⟨20335790967893746710103577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54228775914383324560276205 20335790967893746710103577)
      ·
        refine ⟨15251843225920310032577683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20335790967893746710103577 15251843225920310032577683)
        ·
          refine ⟨22877764838880465048866525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15251843225920310032577683 22877764838880465048866525)
          ·
            refine ⟨8579161814580174393324947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22877764838880465048866525 8579161814580174393324947)
            ·
              refine ⟨12868742721870261589987421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8579161814580174393324947 12868742721870261589987421)
              ·
                refine ⟨4825778520701348096245283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12868742721870261589987421 4825778520701348096245283)
                ·
                  refine ⟨7238667781052022144367925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825778520701348096245283 7238667781052022144367925)
                  ·
                    refine ⟨678625104473627076034493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7238667781052022144367925 678625104473627076034493)
                    ·
                      rfl

theorem cell23_3964853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3964853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964853 prefixEnd_3964853 := by exact prefixLift 3964853
  have htrace : WordTrace (prefixWord ++ tailWord_3964853) baseStart_3964853 baseEnd_3964853 := by
    simpa [prefixWord, tailWord_3964853, baseEnd_3964853] using wordTrace_append hprefix tailTrace_3964853
  have hstable : (prefixWord ++ tailWord_3964853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964853).length < 2 ^ (prefixWord ++ tailWord_3964853).sum := by decide
  have hdescent : baseEnd_3964853 < baseStart_3964853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964873 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 7, 2, 2]
def baseStart_3964873 : Nat := 118140960795 + 3964873 * 2 ^ 59
def prefixEnd_3964873 : Nat := 4983230072969 + 3 ^ 40 * 3964873 * 2
def baseEnd_3964873 : Nat := 2035885583033971149853387

theorem tailTrace_3964873 : CollatzResearch.WordTrace tailWord_3964873 prefixEnd_3964873 2035885583033971149853387 := by
  unfold tailWord_3964873
  simp only [CollatzResearch.WordTrace]
  refine ⟨144610798564949742243131273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96407199043299828162087515 144610798564949742243131273)
  ·
    refine ⟨108458098923712306682348455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144610798564949742243131273 108458098923712306682348455)
    ·
      refine ⟨162687148385568460023522683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108458098923712306682348455 162687148385568460023522683)
      ·
        refine ⟨244030722578352690035284025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162687148385568460023522683 244030722578352690035284025)
        ·
          refine ⟨183023041933764517526463019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244030722578352690035284025 183023041933764517526463019)
          ·
            refine ⟨274534562900646776289694529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183023041933764517526463019 274534562900646776289694529)
            ·
              refine ⟨205900922175485082217270897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274534562900646776289694529 205900922175485082217270897)
              ·
                refine ⟨154425691631613811662953173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205900922175485082217270897 154425691631613811662953173)
                ·
                  refine ⟨3619352147615948710850465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 154425691631613811662953173 3619352147615948710850465)
                  ·
                    refine ⟨2714514110711961533137849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3619352147615948710850465 2714514110711961533137849)
                    ·
                      refine ⟨2035885583033971149853387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714514110711961533137849 2035885583033971149853387)
                      ·
                        rfl

theorem cell23_3964873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 2, 2].length) (baseStart_3964873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964873 prefixEnd_3964873 := by exact prefixLift 3964873
  have htrace : WordTrace (prefixWord ++ tailWord_3964873) baseStart_3964873 baseEnd_3964873 := by
    simpa [prefixWord, tailWord_3964873, baseEnd_3964873] using wordTrace_append hprefix tailTrace_3964873
  have hstable : (prefixWord ++ tailWord_3964873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964873).length < 2 ^ (prefixWord ++ tailWord_3964873).sum := by decide
  have hdescent : baseEnd_3964873 < baseStart_3964873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964876 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3964876 : Nat := 118140960795 + 3964876 * 2 ^ 59
def prefixEnd_3964876 : Nat := 4983230072969 + 3 ^ 40 * 3964876 * 2
def baseEnd_3964876 : Nat := 2035887123475934638115873

theorem tailTrace_3964876 : CollatzResearch.WordTrace tailWord_3964876 prefixEnd_3964876 2035887123475934638115873 := by
  unfold tailWord_3964876
  simp only [CollatzResearch.WordTrace]
  refine ⟨72305453991969436877745241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96407271989292582503660321 72305453991969436877745241)
  ·
    refine ⟨54229090493977077658308931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72305453991969436877745241 54229090493977077658308931)
    ·
      refine ⟨81343635740965616487463397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54229090493977077658308931 81343635740965616487463397)
      ·
        refine ⟨15251931701431053091399387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81343635740965616487463397 15251931701431053091399387)
        ·
          refine ⟨22877897552146579637099081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15251931701431053091399387 22877897552146579637099081)
          ·
            refine ⟨17158423164109934727824311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22877897552146579637099081 17158423164109934727824311)
            ·
              refine ⟨25737634746164902091736467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17158423164109934727824311 25737634746164902091736467)
              ·
                refine ⟨38606452119247353137604701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25737634746164902091736467 38606452119247353137604701)
                ·
                  refine ⟨14477419544717757426601763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38606452119247353137604701 14477419544717757426601763)
                  ·
                    refine ⟨21716129317076636139902645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14477419544717757426601763 21716129317076636139902645)
                    ·
                      refine ⟨2035887123475934638115873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21716129317076636139902645 2035887123475934638115873)
                      ·
                        rfl

theorem cell23_3964876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3964876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964876 prefixEnd_3964876 := by exact prefixLift 3964876
  have htrace : WordTrace (prefixWord ++ tailWord_3964876) baseStart_3964876 baseEnd_3964876 := by
    simpa [prefixWord, tailWord_3964876, baseEnd_3964876] using wordTrace_append hprefix tailTrace_3964876
  have hstable : (prefixWord ++ tailWord_3964876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964876).length < 2 ^ (prefixWord ++ tailWord_3964876).sum := by decide
  have hdescent : baseEnd_3964876 < baseStart_3964876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964879 : List Nat := [1, 1, 2, 1, 1, 5, 2, 10]
def baseStart_3964879 : Nat := 118140960795 + 3964879 * 2 ^ 59
def prefixEnd_3964879 : Nat := 4983230072969 + 3 ^ 40 * 3964879 * 2
def baseEnd_3964879 : Nat := 75403283848811041717717

theorem tailTrace_3964879 : CollatzResearch.WordTrace tailWord_3964879 prefixEnd_3964879 75403283848811041717717 := by
  unfold tailWord_3964879
  simp only [CollatzResearch.WordTrace]
  refine ⟨144611017402928005267849691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96407344935285336845233127 144611017402928005267849691)
  ·
    refine ⟨216916526104392007901774537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144611017402928005267849691 216916526104392007901774537)
    ·
      refine ⟨162687394578294005926330903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216916526104392007901774537 162687394578294005926330903)
      ·
        refine ⟨244031091867441008889496355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162687394578294005926330903 244031091867441008889496355)
        ·
          refine ⟨366046637801161513334244533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244031091867441008889496355 366046637801161513334244533)
          ·
            refine ⟨34316872293858891875085425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366046637801161513334244533 34316872293858891875085425)
            ·
              refine ⟨25737654220394168906314069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34316872293858891875085425 25737654220394168906314069)
              ·
                refine ⟨75403283848811041717717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25737654220394168906314069 75403283848811041717717)
                ·
                  rfl

theorem cell23_3964879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 10].length) (baseStart_3964879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964879 prefixEnd_3964879 := by exact prefixLift 3964879
  have htrace : WordTrace (prefixWord ++ tailWord_3964879) baseStart_3964879 baseEnd_3964879 := by
    simpa [prefixWord, tailWord_3964879, baseEnd_3964879] using wordTrace_append hprefix tailTrace_3964879
  have hstable : (prefixWord ++ tailWord_3964879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964879).length < 2 ^ (prefixWord ++ tailWord_3964879).sum := by decide
  have hdescent : baseEnd_3964879 < baseStart_3964879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964890 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_3964890 : Nat := 118140960795 + 3964890 * 2 ^ 59
def prefixEnd_3964890 : Nat := 4983230072969 + 3 ^ 40 * 3964890 * 2
def baseEnd_3964890 : Nat := 2035894312205097583340809

theorem tailTrace_3964890 : CollatzResearch.WordTrace tailWord_3964890 prefixEnd_3964890 2035894312205097583340809 := by
  unfold tailWord_3964890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36152854651472038536625031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96407612403925436097666749 36152854651472038536625031)
  ·
    refine ⟨54229281977208057804937547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36152854651472038536625031 54229281977208057804937547)
    ·
      refine ⟨81343922965812086707406321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54229281977208057804937547 81343922965812086707406321)
      ·
        refine ⟨61007942224359065030554741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81343922965812086707406321 61007942224359065030554741)
        ·
          refine ⟨5719494583533662346614507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61007942224359065030554741 5719494583533662346614507)
          ·
            refine ⟨8579241875300493519921761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719494583533662346614507 8579241875300493519921761)
            ·
              refine ⟨6434431406475370139941321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8579241875300493519921761 6434431406475370139941321)
              ·
                refine ⟨4825823554856527604955991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6434431406475370139941321 4825823554856527604955991)
                ·
                  refine ⟨7238735332284791407433987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825823554856527604955991 7238735332284791407433987)
                  ·
                    refine ⟨10858102998427187111150981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7238735332284791407433987 10858102998427187111150981)
                    ·
                      refine ⟨2035894312205097583340809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10858102998427187111150981 2035894312205097583340809)
                      ·
                        rfl

theorem cell23_3964890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_3964890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964890 prefixEnd_3964890 := by exact prefixLift 3964890
  have htrace : WordTrace (prefixWord ++ tailWord_3964890) baseStart_3964890 baseEnd_3964890 := by
    simpa [prefixWord, tailWord_3964890, baseEnd_3964890] using wordTrace_append hprefix tailTrace_3964890
  have hstable : (prefixWord ++ tailWord_3964890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964890).length < 2 ^ (prefixWord ++ tailWord_3964890).sum := by decide
  have hdescent : baseEnd_3964890 < baseStart_3964890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964910 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3964910 : Nat := 118140960795 + 3964910 * 2 ^ 59
def prefixEnd_3964910 : Nat := 4983230072969 + 3 ^ 40 * 3964910 * 2
def baseEnd_3964910 : Nat := 2035904581818187505090717

theorem tailTrace_3964910 : CollatzResearch.WordTrace tailWord_3964910 prefixEnd_3964910 2035904581818187505090717 := by
  unfold tailWord_3964910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076518508226962195278523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96408098710543798374818789 18076518508226962195278523)
  ·
    refine ⟨27114777762340443292917785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18076518508226962195278523 27114777762340443292917785)
    ·
      refine ⟨20336083321755332469688339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27114777762340443292917785 20336083321755332469688339)
      ·
        refine ⟨30504124982632998704532509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20336083321755332469688339 30504124982632998704532509)
        ·
          refine ⟨11439046868487374514199691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30504124982632998704532509 11439046868487374514199691)
          ·
            refine ⟨17158570302731061771299537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439046868487374514199691 17158570302731061771299537)
            ·
              refine ⟨12868927727048296328474653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17158570302731061771299537 12868927727048296328474653)
              ·
                refine ⟨4825847897643111123177995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12868927727048296328474653 4825847897643111123177995)
                ·
                  refine ⟨7238771846464666684766993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825847897643111123177995 7238771846464666684766993)
                  ·
                    refine ⟨5429078884848500013575245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7238771846464666684766993 5429078884848500013575245)
                    ·
                      refine ⟨2035904581818187505090717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429078884848500013575245 2035904581818187505090717)
                      ·
                        rfl

theorem cell23_3964910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3964910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964910 prefixEnd_3964910 := by exact prefixLift 3964910
  have htrace : WordTrace (prefixWord ++ tailWord_3964910) baseStart_3964910 baseEnd_3964910 := by
    simpa [prefixWord, tailWord_3964910, baseEnd_3964910] using wordTrace_append hprefix tailTrace_3964910
  have hstable : (prefixWord ++ tailWord_3964910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964910).length < 2 ^ (prefixWord ++ tailWord_3964910).sum := by decide
  have hdescent : baseEnd_3964910 < baseStart_3964910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964913 : List Nat := [1, 2, 2, 2, 6, 1, 9]
def baseStart_3964913 : Nat := 118140960795 + 3964913 * 2 ^ 59
def prefixEnd_3964913 : Nat := 4983230072969 + 3 ^ 40 * 3964913 * 2
def baseEnd_3964913 : Nat := 25134643484693222140163

theorem tailTrace_3964913 : CollatzResearch.WordTrace tailWord_3964913 prefixEnd_3964913 25134643484693222140163 := by
  unfold tailWord_3964913
  simp only [CollatzResearch.WordTrace]
  refine ⟨144612257484804829074587393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96408171656536552716391595 144612257484804829074587393)
  ·
    refine ⟨108459193113603621805940545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144612257484804829074587393 108459193113603621805940545)
    ·
      refine ⟨81344394835202716354455409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108459193113603621805940545 81344394835202716354455409)
      ·
        refine ⟨61008296126402037265841557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81344394835202716354455409 61008296126402037265841557)
        ·
          refine ⟨2859763880925095496836323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61008296126402037265841557 2859763880925095496836323)
          ·
            refine ⟨4289645821387643245254485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859763880925095496836323 4289645821387643245254485)
            ·
              refine ⟨25134643484693222140163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4289645821387643245254485 25134643484693222140163)
              ·
                rfl

theorem cell23_3964913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 9].length) (baseStart_3964913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964913 prefixEnd_3964913 := by exact prefixLift 3964913
  have htrace : WordTrace (prefixWord ++ tailWord_3964913) baseStart_3964913 baseEnd_3964913 := by
    simpa [prefixWord, tailWord_3964913, baseEnd_3964913] using wordTrace_append hprefix tailTrace_3964913
  have hstable : (prefixWord ++ tailWord_3964913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964913).length < 2 ^ (prefixWord ++ tailWord_3964913).sum := by decide
  have hdescent : baseEnd_3964913 < baseStart_3964913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964923 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 3]
def baseStart_3964923 : Nat := 118140960795 + 3964923 * 2 ^ 59
def prefixEnd_3964923 : Nat := 4983230072969 + 3 ^ 40 * 3964923 * 2
def baseEnd_3964923 : Nat := 2035911257066695954228157

theorem tailTrace_3964923 : CollatzResearch.WordTrace tailWord_3964923 prefixEnd_3964923 2035911257066695954228157 := by
  unfold tailWord_3964923
  simp only [CollatzResearch.WordTrace]
  refine ⟨144612622214768600782451423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96408414809845733854967615 144612622214768600782451423)
  ·
    refine ⟨216918933322152901173677135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144612622214768600782451423 216918933322152901173677135)
    ·
      refine ⟨325378399983229351760515703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216918933322152901173677135 325378399983229351760515703)
      ·
        refine ⟨488067599974844027640773555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325378399983229351760515703 488067599974844027640773555)
        ·
          refine ⟨732101399962266041461160333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488067599974844027640773555 732101399962266041461160333)
          ·
            refine ⟨274538024985849765547935125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 732101399962266041461160333 274538024985849765547935125)
            ·
              refine ⟨12868969921211707760059459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274538024985849765547935125 12868969921211707760059459)
              ·
                refine ⟨19303454881817561640089189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12868969921211707760059459 19303454881817561640089189)
                ·
                  refine ⟨3619397790340792807516723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19303454881817561640089189 3619397790340792807516723)
                  ·
                    refine ⟨5429096685511189211275085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619397790340792807516723 5429096685511189211275085)
                    ·
                      refine ⟨2035911257066695954228157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429096685511189211275085 2035911257066695954228157)
                      ·
                        rfl

theorem cell23_3964923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 3].length) (baseStart_3964923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964923 prefixEnd_3964923 := by exact prefixLift 3964923
  have htrace : WordTrace (prefixWord ++ tailWord_3964923) baseStart_3964923 baseEnd_3964923 := by
    simpa [prefixWord, tailWord_3964923, baseEnd_3964923] using wordTrace_append hprefix tailTrace_3964923
  have hstable : (prefixWord ++ tailWord_3964923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964923).length < 2 ^ (prefixWord ++ tailWord_3964923).sum := by decide
  have hdescent : baseEnd_3964923 < baseStart_3964923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964924 : List Nat := [2, 2, 2, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_3964924 : Nat := 118140960795 + 3964924 * 2 ^ 59
def prefixEnd_3964924 : Nat := 4983230072969 + 3 ^ 40 * 3964924 * 2
def baseEnd_3964924 : Nat := 2035911770547350450315653

theorem tailTrace_3964924 : CollatzResearch.WordTrace tailWord_3964924 prefixEnd_3964924 2035911770547350450315653 := by
  unfold tailWord_3964924
  simp only [CollatzResearch.WordTrace]
  refine ⟨72306329343882488976618913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96408439125176651968825217 72306329343882488976618913)
  ·
    refine ⟨54229747007911866732464185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72306329343882488976618913 54229747007911866732464185)
    ·
      refine ⟨40672310255933900049348139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54229747007911866732464185 40672310255933900049348139)
      ·
        refine ⟨61008465383900850074022209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40672310255933900049348139 61008465383900850074022209)
        ·
          refine ⟨45756349037925637555516657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61008465383900850074022209 45756349037925637555516657)
          ·
            refine ⟨34317261778444228166637493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45756349037925637555516657 34317261778444228166637493)
            ·
              refine ⟨3217243291729146390622265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34317261778444228166637493 3217243291729146390622265)
              ·
                refine ⟨2412932468796859792966699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217243291729146390622265 2412932468796859792966699)
                ·
                  refine ⟨3619398703195289689450049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412932468796859792966699 3619398703195289689450049)
                  ·
                    refine ⟨2714549027396467267087537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3619398703195289689450049 2714549027396467267087537)
                    ·
                      refine ⟨2035911770547350450315653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714549027396467267087537 2035911770547350450315653)
                      ·
                        rfl

theorem cell23_3964924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_3964924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964924 prefixEnd_3964924 := by exact prefixLift 3964924
  have htrace : WordTrace (prefixWord ++ tailWord_3964924) baseStart_3964924 baseEnd_3964924 := by
    simpa [prefixWord, tailWord_3964924, baseEnd_3964924] using wordTrace_append hprefix tailTrace_3964924
  have hstable : (prefixWord ++ tailWord_3964924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964924).length < 2 ^ (prefixWord ++ tailWord_3964924).sum := by decide
  have hdescent : baseEnd_3964924 < baseStart_3964924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964940 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_3964940 : Nat := 118140960795 + 3964940 * 2 ^ 59
def prefixEnd_3964940 : Nat := 4983230072969 + 3 ^ 40 * 3964940 * 2
def baseEnd_3964940 : Nat := 2035919986237822387715579

theorem tailTrace_3964940 : CollatzResearch.WordTrace tailWord_3964940 prefixEnd_3964940 2035919986237822387715579 := by
  unfold tailWord_3964940
  simp only [CollatzResearch.WordTrace]
  refine ⟨72306621127853506342910137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96408828170471341790546849 72306621127853506342910137)
  ·
    refine ⟨54229965845890129757182603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72306621127853506342910137 54229965845890129757182603)
    ·
      refine ⟨81344948768835194635773905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54229965845890129757182603 81344948768835194635773905)
      ·
        refine ⟨61008711576626395976830429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81344948768835194635773905 61008711576626395976830429)
        ·
          refine ⟨22878266841234898491311411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61008711576626395976830429 22878266841234898491311411)
          ·
            refine ⟨34317400261852347736967117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22878266841234898491311411 34317400261852347736967117)
            ·
              refine ⟨12869025098194630401362669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34317400261852347736967117 12869025098194630401362669)
              ·
                refine ⟨4825884411822986400511001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12869025098194630401362669 4825884411822986400511001)
                ·
                  refine ⟨3619413308867239800383251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4825884411822986400511001 3619413308867239800383251)
                  ·
                    refine ⟨5429119963300859700574877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619413308867239800383251 5429119963300859700574877)
                    ·
                      refine ⟨2035919986237822387715579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429119963300859700574877 2035919986237822387715579)
                      ·
                        rfl

theorem cell23_3964940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_3964940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964940 prefixEnd_3964940 := by exact prefixLift 3964940
  have htrace : WordTrace (prefixWord ++ tailWord_3964940) baseStart_3964940 baseEnd_3964940 := by
    simpa [prefixWord, tailWord_3964940, baseEnd_3964940] using wordTrace_append hprefix tailTrace_3964940
  have hstable : (prefixWord ++ tailWord_3964940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964940).length < 2 ^ (prefixWord ++ tailWord_3964940).sum := by decide
  have hdescent : baseEnd_3964940 < baseStart_3964940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964941 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3964941 : Nat := 118140960795 + 3964941 * 2 ^ 59
def prefixEnd_3964941 : Nat := 4983230072969 + 3 ^ 40 * 3964941 * 2
def baseEnd_3964941 : Nat := 2035920499718476883803075

theorem tailTrace_3964941 : CollatzResearch.WordTrace tailWord_3964941 prefixEnd_3964941 2035920499718476883803075 := by
  unfold tailWord_3964941
  simp only [CollatzResearch.WordTrace]
  refine ⟨144613278728703389856606677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96408852485802259904404451 144613278728703389856606677)
  ·
    refine ⟨3389373720203985699764219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 144613278728703389856606677 3389373720203985699764219)
    ·
      refine ⟨5084060580305978549646329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389373720203985699764219 5084060580305978549646329)
      ·
        refine ⟨3813045435229483912234747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5084060580305978549646329 3813045435229483912234747)
        ·
          refine ⟨5719568152844225868352121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813045435229483912234747 5719568152844225868352121)
          ·
            refine ⟨4289676114633169401264091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719568152844225868352121 4289676114633169401264091)
            ·
              refine ⟨6434514171949754101896137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289676114633169401264091 6434514171949754101896137)
              ·
                refine ⟨4825885628962315576422103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6434514171949754101896137 4825885628962315576422103)
                ·
                  refine ⟨7238828443443473364633155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825885628962315576422103 7238828443443473364633155)
                  ·
                    refine ⟨10858242665165210046949733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7238828443443473364633155 10858242665165210046949733)
                    ·
                      refine ⟨2035920499718476883803075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10858242665165210046949733 2035920499718476883803075)
                      ·
                        rfl

theorem cell23_3964941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3964941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964941 prefixEnd_3964941 := by exact prefixLift 3964941
  have htrace : WordTrace (prefixWord ++ tailWord_3964941) baseStart_3964941 baseEnd_3964941 := by
    simpa [prefixWord, tailWord_3964941, baseEnd_3964941] using wordTrace_append hprefix tailTrace_3964941
  have hstable : (prefixWord ++ tailWord_3964941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964941).length < 2 ^ (prefixWord ++ tailWord_3964941).sum := by decide
  have hdescent : baseEnd_3964941 < baseStart_3964941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964986 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 7]
def baseStart_3964986 : Nat := 118140960795 + 3964986 * 2 ^ 59
def prefixEnd_3964986 : Nat := 4983230072969 + 3 ^ 40 * 3964986 * 2
def baseEnd_3964986 : Nat := 226215956260881023082263

theorem tailTrace_3964986 : CollatzResearch.WordTrace tailWord_3964986 prefixEnd_3964986 226215956260881023082263 := by
  unfold tailWord_3964986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36153730003385090635498703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96409946675693575027996541 36153730003385090635498703)
  ·
    refine ⟨54230595005077635953248055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36153730003385090635498703 54230595005077635953248055)
    ·
      refine ⟨81345892507616453929872083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54230595005077635953248055 81345892507616453929872083)
      ·
        refine ⟨122018838761424680894808125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81345892507616453929872083 122018838761424680894808125)
        ·
          refine ⟨45757064535534255335553047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122018838761424680894808125 45757064535534255335553047)
          ·
            refine ⟨68635596803301383003329571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45757064535534255335553047 68635596803301383003329571)
            ·
              refine ⟨102953395204952074504994357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68635596803301383003329571 102953395204952074504994357)
              ·
                refine ⟨9651880800464256984843221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102953395204952074504994357 9651880800464256984843221)
                ·
                  refine ⟨226215956260881023082263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9651880800464256984843221 226215956260881023082263)
                  ·
                    rfl

theorem cell23_3964986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_3964986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964986 prefixEnd_3964986 := by exact prefixLift 3964986
  have htrace : WordTrace (prefixWord ++ tailWord_3964986) baseStart_3964986 baseEnd_3964986 := by
    simpa [prefixWord, tailWord_3964986, baseEnd_3964986] using wordTrace_append hprefix tailTrace_3964986
  have hstable : (prefixWord ++ tailWord_3964986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964986).length < 2 ^ (prefixWord ++ tailWord_3964986).sum := by decide
  have hdescent : baseEnd_3964986 < baseStart_3964986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964990 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3964990 : Nat := 118140960795 + 3964990 * 2 ^ 59
def prefixEnd_3964990 : Nat := 4983230072969 + 3 ^ 40 * 3964990 * 2
def baseEnd_3964990 : Nat := 678648553423515730696783

theorem tailTrace_3964990 : CollatzResearch.WordTrace tailWord_3964990 prefixEnd_3964990 678648553423515730696783 := by
  unfold tailWord_3964990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076883238190733903142553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96410043937017247483426949 18076883238190733903142553)
  ·
    refine ⟨13557662428643050427356915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18076883238190733903142553 13557662428643050427356915)
    ·
      refine ⟨20336493642964575641035373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13557662428643050427356915 20336493642964575641035373)
      ·
        refine ⟨7626185116111715865388265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20336493642964575641035373 7626185116111715865388265)
        ·
          refine ⟨5719638837083786899041199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7626185116111715865388265 5719638837083786899041199)
          ·
            refine ⟨8579458255625680348561799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719638837083786899041199 8579458255625680348561799)
            ·
              refine ⟨12869187383438520522842699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8579458255625680348561799 12869187383438520522842699)
              ·
                refine ⟨19303781075157780784264049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12869187383438520522842699 19303781075157780784264049)
                ·
                  refine ⟨14477835806368335588198037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19303781075157780784264049 14477835806368335588198037)
                  ·
                    refine ⟨678648553423515730696783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14477835806368335588198037 678648553423515730696783)
                    ·
                      rfl

theorem cell23_3964990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3964990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964990 prefixEnd_3964990 := by exact prefixLift 3964990
  have htrace : WordTrace (prefixWord ++ tailWord_3964990) baseStart_3964990 baseEnd_3964990 := by
    simpa [prefixWord, tailWord_3964990, baseEnd_3964990] using wordTrace_append hprefix tailTrace_3964990
  have hstable : (prefixWord ++ tailWord_3964990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964990).length < 2 ^ (prefixWord ++ tailWord_3964990).sum := by decide
  have hdescent : baseEnd_3964990 < baseStart_3964990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964993 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3964993 : Nat := 118140960795 + 3964993 * 2 ^ 59
def prefixEnd_3964993 : Nat := 4983230072969 + 3 ^ 40 * 3964993 * 2
def baseEnd_3964993 : Nat := 2035947200712510680352835

theorem tailTrace_3964993 : CollatzResearch.WordTrace tailWord_3964993 prefixEnd_3964993 2035947200712510680352835 := by
  unfold tailWord_3964993
  simp only [CollatzResearch.WordTrace]
  refine ⟨144615175324515002737499633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96410116883010001824999755 144615175324515002737499633)
  ·
    refine ⟨108461381493386252053124725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144615175324515002737499633 108461381493386252053124725)
    ·
      refine ⟨10168254515004961129980443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108461381493386252053124725 10168254515004961129980443)
      ·
        refine ⟨15252381772507441694970665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168254515004961129980443 15252381772507441694970665)
        ·
          refine ⟨11439286329380581271227999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15252381772507441694970665 11439286329380581271227999)
          ·
            refine ⟨17158929494070871906841999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439286329380581271227999 17158929494070871906841999)
            ·
              refine ⟨25738394241106307860262999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17158929494070871906841999 25738394241106307860262999)
              ·
                refine ⟨38607591361659461790394499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25738394241106307860262999 38607591361659461790394499)
                ·
                  refine ⟨57911387042489192685591749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38607591361659461790394499 57911387042489192685591749)
                  ·
                    refine ⟨10858385070466723628548453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57911387042489192685591749 10858385070466723628548453)
                    ·
                      refine ⟨2035947200712510680352835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10858385070466723628548453 2035947200712510680352835)
                      ·
                        rfl

theorem cell23_3964993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3964993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3964993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3964993 prefixEnd_3964993 := by exact prefixLift 3964993
  have htrace : WordTrace (prefixWord ++ tailWord_3964993) baseStart_3964993 baseEnd_3964993 := by
    simpa [prefixWord, tailWord_3964993, baseEnd_3964993] using wordTrace_append hprefix tailTrace_3964993
  have hstable : (prefixWord ++ tailWord_3964993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964993).length < 2 ^ (prefixWord ++ tailWord_3964993).sum := by decide
  have hdescent : baseEnd_3964993 < baseStart_3964993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965014 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3965014 : Nat := 118140960795 + 3965014 * 2 ^ 59
def prefixEnd_3965014 : Nat := 4983230072969 + 3 ^ 40 * 3965014 * 2
def baseEnd_3965014 : Nat := 2035957983806255098190239

theorem tailTrace_3965014 : CollatzResearch.WordTrace tailWord_3965014 prefixEnd_3965014 2035957983806255098190239 := by
  unfold tailWord_3965014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038496328589932707750881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96410627504959282216009397 9038496328589932707750881)
  ·
    refine ⟨6778872246442449530813161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9038496328589932707750881 6778872246442449530813161)
    ·
      refine ⟨5084154184831837148109871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6778872246442449530813161 5084154184831837148109871)
      ·
        refine ⟨7626231277247755722164807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084154184831837148109871 7626231277247755722164807)
        ·
          refine ⟨11439346915871633583247211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7626231277247755722164807 11439346915871633583247211)
          ·
            refine ⟨17159020373807450374870817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439346915871633583247211 17159020373807450374870817)
            ·
              refine ⟨12869265280355587781153113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17159020373807450374870817 12869265280355587781153113)
              ·
                refine ⟨9651948960266690835864835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12869265280355587781153113 9651948960266690835864835)
                ·
                  refine ⟨14477923440400036253797253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9651948960266690835864835 14477923440400036253797253)
                  ·
                    refine ⟨2714610645075006797586985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14477923440400036253797253 2714610645075006797586985)
                    ·
                      refine ⟨2035957983806255098190239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714610645075006797586985 2035957983806255098190239)
                      ·
                        rfl

theorem cell23_3965014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3965014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965014 prefixEnd_3965014 := by exact prefixLift 3965014
  have htrace : WordTrace (prefixWord ++ tailWord_3965014) baseStart_3965014 baseEnd_3965014 := by
    simpa [prefixWord, tailWord_3965014, baseEnd_3965014] using wordTrace_append hprefix tailTrace_3965014
  have hstable : (prefixWord ++ tailWord_3965014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965014).length < 2 ^ (prefixWord ++ tailWord_3965014).sum := by decide
  have hdescent : baseEnd_3965014 < baseStart_3965014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965020 : List Nat := [2, 2, 4, 1, 1, 2, 1, 5, 5]
def baseStart_3965020 : Nat := 118140960795 + 3965020 * 2 ^ 59
def prefixEnd_3965020 : Nat := 4983230072969 + 3 ^ 40 * 3965020 * 2
def baseEnd_3965020 : Nat := 226217896076686897190579

theorem tailTrace_3965020 : CollatzResearch.WordTrace tailWord_3965020 prefixEnd_3965020 226217896076686897190579 := by
  unfold tailWord_3965020
  simp only [CollatzResearch.WordTrace]
  refine ⟨72308080047708593174366257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96410773396944790899155009 72308080047708593174366257)
  ·
    refine ⟨54231060035781444880774693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72308080047708593174366257 54231060035781444880774693)
    ·
      refine ⟨10168323756709020915145255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54231060035781444880774693 10168323756709020915145255)
      ·
        refine ⟨15252485635063531372717883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168323756709020915145255 15252485635063531372717883)
        ·
          refine ⟨22878728452595297059076825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15252485635063531372717883 22878728452595297059076825)
          ·
            refine ⟨17159046339446472794307619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22878728452595297059076825 17159046339446472794307619)
            ·
              refine ⟨25738569509169709191461429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17159046339446472794307619 25738569509169709191461429)
              ·
                refine ⟨2412990891484660236699509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25738569509169709191461429 2412990891484660236699509)
                ·
                  refine ⟨226217896076686897190579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2412990891484660236699509 226217896076686897190579)
                  ·
                    rfl

theorem cell23_3965020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_3965020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965020 prefixEnd_3965020 := by exact prefixLift 3965020
  have htrace : WordTrace (prefixWord ++ tailWord_3965020) baseStart_3965020 baseEnd_3965020 := by
    simpa [prefixWord, tailWord_3965020, baseEnd_3965020] using wordTrace_append hprefix tailTrace_3965020
  have hstable : (prefixWord ++ tailWord_3965020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965020).length < 2 ^ (prefixWord ++ tailWord_3965020).sum := by decide
  have hdescent : baseEnd_3965020 < baseStart_3965020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965023 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 7, 2]
def baseStart_3965023 : Nat := 118140960795 + 3965023 * 2 ^ 59
def prefixEnd_3965023 : Nat := 4983230072969 + 3 ^ 40 * 3965023 * 2
def baseEnd_3965023 : Nat := 2035962605132145562977697

theorem tailTrace_3965023 : CollatzResearch.WordTrace tailWord_3965023 prefixEnd_3965023 2035962605132145562977697 := by
  unfold tailWord_3965023
  simp only [CollatzResearch.WordTrace]
  refine ⟨144616269514406317861091723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96410846342937545240727815 144616269514406317861091723)
  ·
    refine ⟨216924404271609476791637585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144616269514406317861091723 216924404271609476791637585)
    ·
      refine ⟨162693303203707107593728189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216924404271609476791637585 162693303203707107593728189)
      ·
        refine ⟨61009988701390165347648071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162693303203707107593728189 61009988701390165347648071)
        ·
          refine ⟨91514983052085248021472107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61009988701390165347648071 91514983052085248021472107)
          ·
            refine ⟨137272474578127872032208161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91514983052085248021472107 137272474578127872032208161)
            ·
              refine ⟨102954355933595904024156121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137272474578127872032208161 102954355933595904024156121)
              ·
                refine ⟨77215766950196928018117091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102954355933595904024156121 77215766950196928018117091)
                ·
                  refine ⟨115823650425295392027175637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77215766950196928018117091 115823650425295392027175637)
                  ·
                    refine ⟨2714616806842860750636929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 115823650425295392027175637 2714616806842860750636929)
                    ·
                      refine ⟨2035962605132145562977697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714616806842860750636929 2035962605132145562977697)
                      ·
                        rfl

theorem cell23_3965023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_3965023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965023 prefixEnd_3965023 := by exact prefixLift 3965023
  have htrace : WordTrace (prefixWord ++ tailWord_3965023) baseStart_3965023 baseEnd_3965023 := by
    simpa [prefixWord, tailWord_3965023, baseEnd_3965023] using wordTrace_append hprefix tailTrace_3965023
  have hstable : (prefixWord ++ tailWord_3965023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965023).length < 2 ^ (prefixWord ++ tailWord_3965023).sum := by decide
  have hdescent : baseEnd_3965023 < baseStart_3965023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965053 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_3965053 : Nat := 118140960795 + 3965053 * 2 ^ 59
def prefixEnd_3965053 : Nat := 4983230072969 + 3 ^ 40 * 3965053 * 2
def baseEnd_3965053 : Nat := 2035978009551780445602559

theorem tailTrace_3965053 : CollatzResearch.WordTrace tailWord_3965053 prefixEnd_3965053 2035978009551780445602559 := by
  unfold tailWord_3965053
  simp only [CollatzResearch.WordTrace]
  refine ⟨144617363704297632984683813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96411575802865088656455875 144617363704297632984683813)
  ·
    refine ⟨27115755694555806184628215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144617363704297632984683813 27115755694555806184628215)
    ·
      refine ⟨40673633541833709276942323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27115755694555806184628215 40673633541833709276942323)
      ·
        refine ⟨61010450312750563915413485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40673633541833709276942323 61010450312750563915413485)
        ·
          refine ⟨22878918867281461468280057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61010450312750563915413485 22878918867281461468280057)
          ·
            refine ⟨17159189150461096101210043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22878918867281461468280057 17159189150461096101210043)
            ·
              refine ⟨25738783725691644151815065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17159189150461096101210043 25738783725691644151815065)
              ·
                refine ⟨19304087794268733113861299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25738783725691644151815065 19304087794268733113861299)
                ·
                  refine ⟨28956131691403099670791949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19304087794268733113861299 28956131691403099670791949)
                  ·
                    refine ⟨10858549384276162376546981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28956131691403099670791949 10858549384276162376546981)
                    ·
                      refine ⟨2035978009551780445602559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10858549384276162376546981 2035978009551780445602559)
                      ·
                        rfl

theorem cell23_3965053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_3965053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965053 prefixEnd_3965053 := by exact prefixLift 3965053
  have htrace : WordTrace (prefixWord ++ tailWord_3965053) baseStart_3965053 baseEnd_3965053 := by
    simpa [prefixWord, tailWord_3965053, baseEnd_3965053] using wordTrace_append hprefix tailTrace_3965053
  have hstable : (prefixWord ++ tailWord_3965053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965053).length < 2 ^ (prefixWord ++ tailWord_3965053).sum := by decide
  have hdescent : baseEnd_3965053 < baseStart_3965053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965073 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_3965073 : Nat := 118140960795 + 3965073 * 2 ^ 59
def prefixEnd_3965073 : Nat := 4983230072969 + 3 ^ 40 * 3965073 * 2
def baseEnd_3965073 : Nat := 2035988279164870367352467

theorem tailTrace_3965073 : CollatzResearch.WordTrace tailWord_3965073 prefixEnd_3965073 2035988279164870367352467 := by
  unfold tailWord_3965073
  simp only [CollatzResearch.WordTrace]
  refine ⟨144618093164225176400411873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96412062109483450933607915 144618093164225176400411873)
  ·
    refine ⟨108463569873168882300308905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144618093164225176400411873 108463569873168882300308905)
    ·
      refine ⟨81347677404876661725231679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108463569873168882300308905 81347677404876661725231679)
      ·
        refine ⟨122021516107314992587847519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81347677404876661725231679 122021516107314992587847519)
        ·
          refine ⟨183032274160972488881771279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122021516107314992587847519 183032274160972488881771279)
          ·
            refine ⟨274548411241458733322656919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183032274160972488881771279 274548411241458733322656919)
            ·
              refine ⟨411822616862188099983985379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274548411241458733322656919 411822616862188099983985379)
              ·
                refine ⟨617733925293282149975978069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411822616862188099983985379 617733925293282149975978069)
                ·
                  refine ⟨7239069437030650195030993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 617733925293282149975978069 7239069437030650195030993)
                  ·
                    refine ⟨5429302077772987646273245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7239069437030650195030993 5429302077772987646273245)
                    ·
                      refine ⟨2035988279164870367352467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429302077772987646273245 2035988279164870367352467)
                      ·
                        rfl

theorem cell23_3965073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_3965073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965073 prefixEnd_3965073 := by exact prefixLift 3965073
  have htrace : WordTrace (prefixWord ++ tailWord_3965073) baseStart_3965073 baseEnd_3965073 := by
    simpa [prefixWord, tailWord_3965073, baseEnd_3965073] using wordTrace_append hprefix tailTrace_3965073
  have hstable : (prefixWord ++ tailWord_3965073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965073).length < 2 ^ (prefixWord ++ tailWord_3965073).sum := by decide
  have hdescent : baseEnd_3965073 < baseStart_3965073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965093 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 6]
def baseStart_3965093 : Nat := 118140960795 + 3965093 * 2 ^ 59
def prefixEnd_3965093 : Nat := 4983230072969 + 3 ^ 40 * 3965093 * 2
def baseEnd_3965093 : Nat := 226222060975328921011375

theorem tailTrace_3965093 : CollatzResearch.WordTrace tailWord_3965093 prefixEnd_3965093 226222060975328921011375 := by
  unfold tailWord_3965093
  simp only [CollatzResearch.WordTrace]
  refine ⟨144618822624152719816139933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96412548416101813210759955 144618822624152719816139933)
  ·
    refine ⟨54232058484057269931052475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144618822624152719816139933 54232058484057269931052475)
    ·
      refine ⟨81348087726085904896578713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54232058484057269931052475 81348087726085904896578713)
      ·
        refine ⟨61011065794564428672434035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81348087726085904896578713 61011065794564428672434035)
        ·
          refine ⟨91516598691846643008651053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61011065794564428672434035 91516598691846643008651053)
          ·
            refine ⟨34318724509442491128244145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91516598691846643008651053 34318724509442491128244145)
            ·
              refine ⟨25739043382081868346183109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34318724509442491128244145 25739043382081868346183109)
              ·
                refine ⟨4826070634140350314909333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25739043382081868346183109 4826070634140350314909333)
                ·
                  refine ⟨226222060975328921011375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4826070634140350314909333 226222060975328921011375)
                  ·
                    rfl

theorem cell23_3965093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_3965093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965093 prefixEnd_3965093 := by exact prefixLift 3965093
  have htrace : WordTrace (prefixWord ++ tailWord_3965093) baseStart_3965093 baseEnd_3965093 := by
    simpa [prefixWord, tailWord_3965093, baseEnd_3965093] using wordTrace_append hprefix tailTrace_3965093
  have hstable : (prefixWord ++ tailWord_3965093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965093).length < 2 ^ (prefixWord ++ tailWord_3965093).sum := by decide
  have hdescent : baseEnd_3965093 < baseStart_3965093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965153 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3965153 : Nat := 118140960795 + 3965153 * 2 ^ 59
def prefixEnd_3965153 : Nat := 4983230072969 + 3 ^ 40 * 3965153 * 2
def baseEnd_3965153 : Nat := 678676452539076684784033

theorem tailTrace_3965153 : CollatzResearch.WordTrace tailWord_3965153 prefixEnd_3965153 678676452539076684784033 := by
  unfold tailWord_3965153
  simp only [CollatzResearch.WordTrace]
  refine ⟨144621011003935350063324113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96414007335956900042216075 144621011003935350063324113)
  ·
    refine ⟨108465758252951512547493085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144621011003935350063324113 108465758252951512547493085)
    ·
      refine ⟨40674659344856817205309907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108465758252951512547493085 40674659344856817205309907)
      ·
        refine ⟨61011989017285225807964861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40674659344856817205309907 61011989017285225807964861)
        ·
          refine ⟨22879495881481959677986823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61011989017285225807964861 22879495881481959677986823)
          ·
            refine ⟨34319243822222939516980235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22879495881481959677986823 34319243822222939516980235)
            ·
              refine ⟨51478865733334409275470353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34319243822222939516980235 51478865733334409275470353)
              ·
                refine ⟨38609149300000806956602765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51478865733334409275470353 38609149300000806956602765)
                ·
                  refine ⟨14478430987500302608726037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38609149300000806956602765 14478430987500302608726037)
                  ·
                    refine ⟨678676452539076684784033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14478430987500302608726037 678676452539076684784033)
                    ·
                      rfl

theorem cell23_3965153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3965153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965153 prefixEnd_3965153 := by exact prefixLift 3965153
  have htrace : WordTrace (prefixWord ++ tailWord_3965153) baseStart_3965153 baseEnd_3965153 := by
    simpa [prefixWord, tailWord_3965153, baseEnd_3965153] using wordTrace_append hprefix tailTrace_3965153
  have hstable : (prefixWord ++ tailWord_3965153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965153).length < 2 ^ (prefixWord ++ tailWord_3965153).sum := by decide
  have hdescent : baseEnd_3965153 < baseStart_3965153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965160 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3965160 : Nat := 118140960795 + 3965160 * 2 ^ 59
def prefixEnd_3965160 : Nat := 4983230072969 + 3 ^ 40 * 3965160 * 2
def baseEnd_3965160 : Nat := 2036032951981811526964567

theorem tailTrace_3965160 : CollatzResearch.WordTrace tailWord_3965160 prefixEnd_3965160 2036032951981811526964567 := by
  unfold tailWord_3965160
  simp only [CollatzResearch.WordTrace]
  refine ⟨72310633157454995129414467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96414177543273326839219289 72310633157454995129414467)
  ·
    refine ⟨108465949736182492694121701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72310633157454995129414467 108465949736182492694121701)
    ·
      refine ⟨20337365575534217380147819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108465949736182492694121701 20337365575534217380147819)
      ·
        refine ⟨30506048363301326070221729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20337365575534217380147819 30506048363301326070221729)
        ·
          refine ⟨22879536272475994552666297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30506048363301326070221729 22879536272475994552666297)
          ·
            refine ⟨17159652204356995914499723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22879536272475994552666297 17159652204356995914499723)
            ·
              refine ⟨25739478306535493871749585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17159652204356995914499723 25739478306535493871749585)
              ·
                refine ⟨19304608729901620403812189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25739478306535493871749585 19304608729901620403812189)
                ·
                  refine ⟨7239228273713107651429571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19304608729901620403812189 7239228273713107651429571)
                  ·
                    refine ⟨10858842410569661477144357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7239228273713107651429571 10858842410569661477144357)
                    ·
                      refine ⟨2036032951981811526964567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10858842410569661477144357 2036032951981811526964567)
                      ·
                        rfl

theorem cell23_3965160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3965160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965160 prefixEnd_3965160 := by exact prefixLift 3965160
  have htrace : WordTrace (prefixWord ++ tailWord_3965160) baseStart_3965160 baseEnd_3965160 := by
    simpa [prefixWord, tailWord_3965160, baseEnd_3965160] using wordTrace_append hprefix tailTrace_3965160
  have hstable : (prefixWord ++ tailWord_3965160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965160).length < 2 ^ (prefixWord ++ tailWord_3965160).sum := by decide
  have hdescent : baseEnd_3965160 < baseStart_3965160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965163 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5]
def baseStart_3965163 : Nat := 118140960795 + 3965163 * 2 ^ 59
def prefixEnd_3965163 : Nat := 4983230072969 + 3 ^ 40 * 3965163 * 2
def baseEnd_3965163 : Nat := 2036034492423775015227053

theorem tailTrace_3965163 : CollatzResearch.WordTrace tailWord_3965163 prefixEnd_3965163 2036034492423775015227053 := by
  unfold tailWord_3965163
  simp only [CollatzResearch.WordTrace]
  refine ⟨144621375733899121771188143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96414250489266081180792095 144621375733899121771188143)
  ·
    refine ⟨216932063600848682656782215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144621375733899121771188143 216932063600848682656782215)
    ·
      refine ⟨325398095401273023985173323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216932063600848682656782215 325398095401273023985173323)
      ·
        refine ⟨488097143101909535977759985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325398095401273023985173323 488097143101909535977759985)
        ·
          refine ⟨366072857326432151983319989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488097143101909535977759985 366072857326432151983319989)
          ·
            refine ⟨34319330374353014248436249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366072857326432151983319989 34319330374353014248436249)
            ·
              refine ⟨25739497780764760686327187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34319330374353014248436249 25739497780764760686327187)
              ·
                refine ⟨38609246671147141029490781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25739497780764760686327187 38609246671147141029490781)
                ·
                  refine ⟨14478467501680177886059043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38609246671147141029490781 14478467501680177886059043)
                  ·
                    refine ⟨21717701252520266829088565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14478467501680177886059043 21717701252520266829088565)
                    ·
                      refine ⟨2036034492423775015227053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21717701252520266829088565 2036034492423775015227053)
                      ·
                        rfl

theorem cell23_3965163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_3965163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965163 prefixEnd_3965163 := by exact prefixLift 3965163
  have htrace : WordTrace (prefixWord ++ tailWord_3965163) baseStart_3965163 baseEnd_3965163 := by
    simpa [prefixWord, tailWord_3965163, baseEnd_3965163] using wordTrace_append hprefix tailTrace_3965163
  have hstable : (prefixWord ++ tailWord_3965163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965163).length < 2 ^ (prefixWord ++ tailWord_3965163).sum := by decide
  have hdescent : baseEnd_3965163 < baseStart_3965163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965170 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_3965170 : Nat := 118140960795 + 3965170 * 2 ^ 59
def prefixEnd_3965170 : Nat := 4983230072969 + 3 ^ 40 * 3965170 * 2
def baseEnd_3965170 : Nat := 678679362262785495946507

theorem tailTrace_3965170 : CollatzResearch.WordTrace tailWord_3965170 prefixEnd_3965170 678679362262785495946507 := by
  unfold tailWord_3965170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36155407761218440491673241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96414420696582507977795309 36155407761218440491673241)
  ·
    refine ⟨27116555820913830368754931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36155407761218440491673241 27116555820913830368754931)
    ·
      refine ⟨40674833731370745553132397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27116555820913830368754931 40674833731370745553132397)
      ·
        refine ⟨15253062649264029582424649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40674833731370745553132397 15253062649264029582424649)
        ·
          refine ⟨11439796986948022186818487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15253062649264029582424649 11439796986948022186818487)
          ·
            refine ⟨17159695480422033280227731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439796986948022186818487 17159695480422033280227731)
            ·
              refine ⟨25739543220633049920341597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17159695480422033280227731 25739543220633049920341597)
              ·
                refine ⟨9652328707737393720128099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25739543220633049920341597 9652328707737393720128099)
                ·
                  refine ⟨14478493061606090580192149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9652328707737393720128099 14478493061606090580192149)
                  ·
                    refine ⟨678679362262785495946507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14478493061606090580192149 678679362262785495946507)
                    ·
                      rfl

theorem cell23_3965170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_3965170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965170 prefixEnd_3965170 := by exact prefixLift 3965170
  have htrace : WordTrace (prefixWord ++ tailWord_3965170) baseStart_3965170 baseEnd_3965170 := by
    simpa [prefixWord, tailWord_3965170, baseEnd_3965170] using wordTrace_append hprefix tailTrace_3965170
  have hstable : (prefixWord ++ tailWord_3965170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965170).length < 2 ^ (prefixWord ++ tailWord_3965170).sum := by decide
  have hdescent : baseEnd_3965170 < baseStart_3965170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965191 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 1, 5]
def baseStart_3965191 : Nat := 118140960795 + 3965191 * 2 ^ 59
def prefixEnd_3965191 : Nat := 4983230072969 + 3 ^ 40 * 3965191 * 2
def baseEnd_3965191 : Nat := 678682956627366968558975

theorem tailTrace_3965191 : CollatzResearch.WordTrace tailWord_3965191 prefixEnd_3965191 678682956627366968558975 := by
  unfold tailWord_3965191
  simp only [CollatzResearch.WordTrace]
  refine ⟨144622396977797682553207427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96414931318531788368804951 144622396977797682553207427)
  ·
    refine ⟨216933595466696523829811141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144622396977797682553207427 216933595466696523829811141)
    ·
      refine ⟨40675049150005598218089589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216933595466696523829811141 40675049150005598218089589)
      ·
        refine ⟨3813285857813024832945899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40675049150005598218089589 3813285857813024832945899)
        ·
          refine ⟨5719928786719537249418849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813285857813024832945899 5719928786719537249418849)
          ·
            refine ⟨4289946590039652937064137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719928786719537249418849 4289946590039652937064137)
            ·
              refine ⟨3217459942529739702798103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4289946590039652937064137 3217459942529739702798103)
              ·
                refine ⟨4826189913794609554197155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217459942529739702798103 4826189913794609554197155)
                ·
                  refine ⟨7239284870691914331295733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826189913794609554197155 7239284870691914331295733)
                  ·
                    refine ⟨678682956627366968558975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7239284870691914331295733 678682956627366968558975)
                    ·
                      rfl

theorem cell23_3965191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_3965191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965191 prefixEnd_3965191 := by exact prefixLift 3965191
  have htrace : WordTrace (prefixWord ++ tailWord_3965191) baseStart_3965191 baseEnd_3965191 := by
    simpa [prefixWord, tailWord_3965191, baseEnd_3965191] using wordTrace_append hprefix tailTrace_3965191
  have hstable : (prefixWord ++ tailWord_3965191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965191).length < 2 ^ (prefixWord ++ tailWord_3965191).sum := by decide
  have hdescent : baseEnd_3965191 < baseStart_3965191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965214 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3965214 : Nat := 118140960795 + 3965214 * 2 ^ 59
def prefixEnd_3965214 : Nat := 4983230072969 + 3 ^ 40 * 3965214 * 2
def baseEnd_3965214 : Nat := 2036060679937154315689319

theorem tailTrace_3965214 : CollatzResearch.WordTrace tailWord_3965214 prefixEnd_3965214 2036060679937154315689319 := by
  unfold tailWord_3965214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18077904482089294685161837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96415490571142904987529797 18077904482089294685161837)
  ·
    refine ⟨6779214180783485506935689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18077904482089294685161837 6779214180783485506935689)
    ·
      refine ⟨5084410635587614130201767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6779214180783485506935689 5084410635587614130201767)
      ·
        refine ⟨7626615953381421195302651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084410635587614130201767 7626615953381421195302651)
        ·
          refine ⟨11439923930072131792953977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7626615953381421195302651 11439923930072131792953977)
          ·
            refine ⟨8579942947554098844715483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11439923930072131792953977 8579942947554098844715483)
            ·
              refine ⟨12869914421331148267073225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8579942947554098844715483 12869914421331148267073225)
              ·
                refine ⟨9652435815998361200304919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12869914421331148267073225 9652435815998361200304919)
                ·
                  refine ⟨14478653723997541800457379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9652435815998361200304919 14478653723997541800457379)
                  ·
                    refine ⟨21717980585996312700686069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14478653723997541800457379 21717980585996312700686069)
                    ·
                      refine ⟨2036060679937154315689319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21717980585996312700686069 2036060679937154315689319)
                      ·
                        rfl

theorem cell23_3965214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3965214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965214 prefixEnd_3965214 := by exact prefixLift 3965214
  have htrace : WordTrace (prefixWord ++ tailWord_3965214) baseStart_3965214 baseEnd_3965214 := by
    simpa [prefixWord, tailWord_3965214, baseEnd_3965214] using wordTrace_append hprefix tailTrace_3965214
  have hstable : (prefixWord ++ tailWord_3965214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965214).length < 2 ^ (prefixWord ++ tailWord_3965214).sum := by decide
  have hdescent : baseEnd_3965214 < baseStart_3965214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965224 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3965224 : Nat := 118140960795 + 3965224 * 2 ^ 59
def prefixEnd_3965224 : Nat := 4983230072969 + 3 ^ 40 * 3965224 * 2
def baseEnd_3965224 : Nat := 2036065814743699276564273

theorem tailTrace_3965224 : CollatzResearch.WordTrace tailWord_3965224 prefixEnd_3965224 2036065814743699276564273 := by
  unfold tailWord_3965224
  simp only [CollatzResearch.WordTrace]
  refine ⟨72311800293339064594579363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96415733724452086126105817 72311800293339064594579363)
  ·
    refine ⟨108467700440008596891869045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72311800293339064594579363 108467700440008596891869045)
    ·
      refine ⟨10168846916250805958612723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108467700440008596891869045 10168846916250805958612723)
      ·
        refine ⟨15253270374376208937919085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168846916250805958612723 15253270374376208937919085)
        ·
          refine ⟨5719976390391078351719657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15253270374376208937919085 5719976390391078351719657)
          ·
            refine ⟨4289982292793308763789743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719976390391078351719657 4289982292793308763789743)
            ·
              refine ⟨6434973439189963145684615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289982292793308763789743 6434973439189963145684615)
              ·
                refine ⟨9652460158784944718526923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434973439189963145684615 9652460158784944718526923)
                ·
                  refine ⟨14478690238177417077790385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9652460158784944718526923 14478690238177417077790385)
                  ·
                    refine ⟨10859017678633062808342789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14478690238177417077790385 10859017678633062808342789)
                    ·
                      refine ⟨2036065814743699276564273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10859017678633062808342789 2036065814743699276564273)
                      ·
                        rfl

theorem cell23_3965224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3965224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965224 prefixEnd_3965224 := by exact prefixLift 3965224
  have htrace : WordTrace (prefixWord ++ tailWord_3965224) baseStart_3965224 baseEnd_3965224 := by
    simpa [prefixWord, tailWord_3965224, baseEnd_3965224] using wordTrace_append hprefix tailTrace_3965224
  have hstable : (prefixWord ++ tailWord_3965224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965224).length < 2 ^ (prefixWord ++ tailWord_3965224).sum := by decide
  have hdescent : baseEnd_3965224 < baseStart_3965224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965234 : List Nat := [3, 2, 1, 1, 6, 1, 2, 7]
def baseStart_3965234 : Nat := 118140960795 + 3965234 * 2 ^ 59
def prefixEnd_3965234 : Nat := 4983230072969 + 3 ^ 40 * 3965234 * 2
def baseEnd_3965234 : Nat := 75410035168527564349601

theorem tailTrace_3965234 : CollatzResearch.WordTrace tailWord_3965234 prefixEnd_3965234 75410035168527564349601 := by
  unfold tailWord_3965234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36155991329160475224255689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96415976877761267264681837 36155991329160475224255689)
  ·
    refine ⟨27116993496870356418191767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36155991329160475224255689 27116993496870356418191767)
    ·
      refine ⟨40675490245305534627287651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27116993496870356418191767 40675490245305534627287651)
      ·
        refine ⟨61013235367958301940931477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40675490245305534627287651 61013235367958301940931477)
        ·
          refine ⟨2859995407873045403481163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61013235367958301940931477 2859995407873045403481163)
          ·
            refine ⟨4289993111809568105221745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859995407873045403481163 4289993111809568105221745)
            ·
              refine ⟨3217494833857176078916309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4289993111809568105221745 3217494833857176078916309)
              ·
                refine ⟨75410035168527564349601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3217494833857176078916309 75410035168527564349601)
                ·
                  rfl

theorem cell23_3965234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 7].length) (baseStart_3965234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965234 prefixEnd_3965234 := by exact prefixLift 3965234
  have htrace : WordTrace (prefixWord ++ tailWord_3965234) baseStart_3965234 baseEnd_3965234 := by
    simpa [prefixWord, tailWord_3965234, baseEnd_3965234] using wordTrace_append hprefix tailTrace_3965234
  have hstable : (prefixWord ++ tailWord_3965234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965234).length < 2 ^ (prefixWord ++ tailWord_3965234).sum := by decide
  have hdescent : baseEnd_3965234 < baseStart_3965234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965263 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_3965263 : Nat := 118140960795 + 3965263 * 2 ^ 59
def prefixEnd_3965263 : Nat := 4983230072969 + 3 ^ 40 * 3965263 * 2
def baseEnd_3965263 : Nat := 2036085840489224623976593

theorem tailTrace_3965263 : CollatzResearch.WordTrace tailWord_3965263 prefixEnd_3965263 2036085840489224623976593 := by
  unfold tailWord_3965263
  simp only [CollatzResearch.WordTrace]
  refine ⟨144625023033536838849828443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96416682022357892566552295 144625023033536838849828443)
  ·
    refine ⟨216937534550305258274742665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144625023033536838849828443 216937534550305258274742665)
    ·
      refine ⟨162703150912728943706056999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216937534550305258274742665 162703150912728943706056999)
      ·
        refine ⟨244054726369093415559085499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162703150912728943706056999 244054726369093415559085499)
        ·
          refine ⟨366082089553640123338628249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244054726369093415559085499 366082089553640123338628249)
          ·
            refine ⟨274561567165230092503971187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366082089553640123338628249 274561567165230092503971187)
            ·
              refine ⟨411842350747845138755956781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274561567165230092503971187 411842350747845138755956781)
              ·
                refine ⟨154440881530441927033483793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411842350747845138755956781 154440881530441927033483793)
                ·
                  refine ⟨115830661147831445275112845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154440881530441927033483793 115830661147831445275112845)
                  ·
                    refine ⟨43436497930436791978167317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115830661147831445275112845 43436497930436791978167317)
                    ·
                      refine ⟨2036085840489224623976593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43436497930436791978167317 2036085840489224623976593)
                      ·
                        rfl

theorem cell23_3965263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_3965263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965263 prefixEnd_3965263 := by exact prefixLift 3965263
  have htrace : WordTrace (prefixWord ++ tailWord_3965263) baseStart_3965263 baseEnd_3965263 := by
    simpa [prefixWord, tailWord_3965263, baseEnd_3965263] using wordTrace_append hprefix tailTrace_3965263
  have hstable : (prefixWord ++ tailWord_3965263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965263).length < 2 ^ (prefixWord ++ tailWord_3965263).sum := by decide
  have hdescent : baseEnd_3965263 < baseStart_3965263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965324 : List Nat := [2, 2, 1, 2, 1, 4, 4, 2, 5]
def baseStart_3965324 : Nat := 118140960795 + 3965324 * 2 ^ 59
def prefixEnd_3965324 : Nat := 4983230072969 + 3 ^ 40 * 3965324 * 2
def baseEnd_3965324 : Nat := 226235240312127653923757

theorem tailTrace_3965324 : CollatzResearch.WordTrace tailWord_3965324 prefixEnd_3965324 226235240312127653923757 := by
  unfold tailWord_3965324
  simp only [CollatzResearch.WordTrace]
  refine ⟨72313623943157923133899513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96418165257543897511866017 72313623943157923133899513)
  ·
    refine ⟨54235217957368442350424635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72313623943157923133899513 54235217957368442350424635)
    ·
      refine ⟨81352826936052663525636953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54235217957368442350424635 81352826936052663525636953)
      ·
        refine ⟨61014620202039497644227715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81352826936052663525636953 61014620202039497644227715)
        ·
          refine ⟨91521930303059246466341573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61014620202039497644227715 91521930303059246466341573)
          ·
            refine ⟨17160361931823608712439045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91521930303059246466341573 17160361931823608712439045)
            ·
              refine ⟨3217567862216926633582321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17160361931823608712439045 3217567862216926633582321)
              ·
                refine ⟨2413175896662694975186741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217567862216926633582321 2413175896662694975186741)
                ·
                  refine ⟨226235240312127653923757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2413175896662694975186741 226235240312127653923757)
                  ·
                    rfl

theorem cell23_3965324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_3965324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965324 prefixEnd_3965324 := by exact prefixLift 3965324
  have htrace : WordTrace (prefixWord ++ tailWord_3965324) baseStart_3965324 baseEnd_3965324 := by
    simpa [prefixWord, tailWord_3965324, baseEnd_3965324] using wordTrace_append hprefix tailTrace_3965324
  have hstable : (prefixWord ++ tailWord_3965324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965324).length < 2 ^ (prefixWord ++ tailWord_3965324).sum := by decide
  have hdescent : baseEnd_3965324 < baseStart_3965324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965370 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_3965370 : Nat := 118140960795 + 3965370 * 2 ^ 59
def prefixEnd_3965370 : Nat := 4983230072969 + 3 ^ 40 * 3965370 * 2
def baseEnd_3965370 : Nat := 2036140782919255705338601

theorem tailTrace_3965370 : CollatzResearch.WordTrace tailWord_3965370 prefixEnd_3965370 2036140782919255705338601 := by
  unfold tailWord_3965370
  simp only [CollatzResearch.WordTrace]
  refine ⟨36157231411037299030993391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96419283762766130749315709 36157231411037299030993391)
  ·
    refine ⟨54235847116555948546490087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36157231411037299030993391 54235847116555948546490087)
    ·
      refine ⟨81353770674833922819735131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54235847116555948546490087 81353770674833922819735131)
      ·
        refine ⟨122030656012250884229602697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81353770674833922819735131 122030656012250884229602697)
        ·
          refine ⟨91522992009188163172202023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122030656012250884229602697 91522992009188163172202023)
          ·
            refine ⟨137284488013782244758303035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91522992009188163172202023 137284488013782244758303035)
            ·
              refine ⟨205926732020673367137454553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137284488013782244758303035 205926732020673367137454553)
              ·
                refine ⟨154445049015505025353090915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205926732020673367137454553 154445049015505025353090915)
                ·
                  refine ⟨231667573523257538029636373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154445049015505025353090915 231667573523257538029636373)
                  ·
                    refine ⟨10859417508902697095139205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231667573523257538029636373 10859417508902697095139205)
                    ·
                      refine ⟨2036140782919255705338601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10859417508902697095139205 2036140782919255705338601)
                      ·
                        rfl

theorem cell23_3965370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_3965370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965370 prefixEnd_3965370 := by exact prefixLift 3965370
  have htrace : WordTrace (prefixWord ++ tailWord_3965370) baseStart_3965370 baseEnd_3965370 := by
    simpa [prefixWord, tailWord_3965370, baseEnd_3965370] using wordTrace_append hprefix tailTrace_3965370
  have hstable : (prefixWord ++ tailWord_3965370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965370).length < 2 ^ (prefixWord ++ tailWord_3965370).sum := by decide
  have hdescent : baseEnd_3965370 < baseStart_3965370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965374 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_3965374 : Nat := 118140960795 + 3965374 * 2 ^ 59
def prefixEnd_3965374 : Nat := 4983230072969 + 3 ^ 40 * 3965374 * 2
def baseEnd_3965374 : Nat := 2036142836841873689688583

theorem tailTrace_3965374 : CollatzResearch.WordTrace tailWord_3965374 prefixEnd_3965374 2036142836841873689688583 := by
  unfold tailWord_3965374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18078633942016838100889897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96419381024089803204746117 18078633942016838100889897)
  ·
    refine ⟨13558975456512628575667423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18078633942016838100889897 13558975456512628575667423)
    ·
      refine ⟨20338463184768942863501135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13558975456512628575667423 20338463184768942863501135)
      ·
        refine ⟨30507694777153414295251703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338463184768942863501135 30507694777153414295251703)
        ·
          refine ⟨45761542165730121442877555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30507694777153414295251703 45761542165730121442877555)
          ·
            refine ⟨68642313248595182164316333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45761542165730121442877555 68642313248595182164316333)
            ·
              refine ⟨25740867468223193311618625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68642313248595182164316333 25740867468223193311618625)
              ·
                refine ⟨19305650601167394983713969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25740867468223193311618625 19305650601167394983713969)
                ·
                  refine ⟨14479237950875546237785477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19305650601167394983713969 14479237950875546237785477)
                  ·
                    refine ⟨2714857115789164919584777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14479237950875546237785477 2714857115789164919584777)
                    ·
                      refine ⟨2036142836841873689688583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714857115789164919584777 2036142836841873689688583)
                      ·
                        rfl

theorem cell23_3965374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_3965374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965374 prefixEnd_3965374 := by exact prefixLift 3965374
  have htrace : WordTrace (prefixWord ++ tailWord_3965374) baseStart_3965374 baseEnd_3965374 := by
    simpa [prefixWord, tailWord_3965374, baseEnd_3965374] using wordTrace_append hprefix tailTrace_3965374
  have hstable : (prefixWord ++ tailWord_3965374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965374).length < 2 ^ (prefixWord ++ tailWord_3965374).sum := by decide
  have hdescent : baseEnd_3965374 < baseStart_3965374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965384 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 3, 4]
def baseStart_3965384 : Nat := 118140960795 + 3965384 * 2 ^ 59
def prefixEnd_3965384 : Nat := 4983230072969 + 3 ^ 40 * 3965384 * 2
def baseEnd_3965384 : Nat := 678715990549472883521179

theorem tailTrace_3965384 : CollatzResearch.WordTrace tailWord_3965384 prefixEnd_3965384 678715990549472883521179 := by
  unfold tailWord_3965384
  simp only [CollatzResearch.WordTrace]
  refine ⟨72314718133049238257491603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96419624177398984343322137 72314718133049238257491603)
  ·
    refine ⟨108472077199573857386237405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72314718133049238257491603 108472077199573857386237405)
    ·
      refine ⟨40677028949840196519839027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108472077199573857386237405 40677028949840196519839027)
      ·
        refine ⟨61015543424760294779758541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40677028949840196519839027 61015543424760294779758541)
        ·
          refine ⟨22880828784285110542409453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61015543424760294779758541 22880828784285110542409453)
          ·
            refine ⟨8580310794106916453403545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22880828784285110542409453 8580310794106916453403545)
            ·
              refine ⟨6435233095580187340052659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8580310794106916453403545 6435233095580187340052659)
              ·
                refine ⟨9652849643370281010078989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435233095580187340052659 9652849643370281010078989)
                ·
                  refine ⟨3619818616263855378779621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9652849643370281010078989 3619818616263855378779621)
                  ·
                    refine ⟨678715990549472883521179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3619818616263855378779621 678715990549472883521179)
                    ·
                      rfl

theorem cell23_3965384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_3965384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965384 prefixEnd_3965384 := by exact prefixLift 3965384
  have htrace : WordTrace (prefixWord ++ tailWord_3965384) baseStart_3965384 baseEnd_3965384 := by
    simpa [prefixWord, tailWord_3965384, baseEnd_3965384] using wordTrace_append hprefix tailTrace_3965384
  have hstable : (prefixWord ++ tailWord_3965384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965384).length < 2 ^ (prefixWord ++ tailWord_3965384).sum := by decide
  have hdescent : baseEnd_3965384 < baseStart_3965384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965400 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_3965400 : Nat := 118140960795 + 3965400 * 2 ^ 59
def prefixEnd_3965400 : Nat := 4983230072969 + 3 ^ 40 * 3965400 * 2
def baseEnd_3965400 : Nat := 2036156187338890587963463

theorem tailTrace_3965400 : CollatzResearch.WordTrace tailWord_3965400 prefixEnd_3965400 2036156187338890587963463 := by
  unfold tailWord_3965400
  simp only [CollatzResearch.WordTrace]
  refine ⟨72315009917020255623782827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96420013222693674165043769 72315009917020255623782827)
  ·
    refine ⟨108472514875530383435674241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72315009917020255623782827 108472514875530383435674241)
    ·
      refine ⟨81354386156647787576755681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108472514875530383435674241 81354386156647787576755681)
      ·
        refine ⟨61015789617485840682566761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81354386156647787576755681 61015789617485840682566761)
        ·
          refine ⟨45761842213114380511925071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61015789617485840682566761 45761842213114380511925071)
          ·
            refine ⟨68642763319671570767887607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45761842213114380511925071 68642763319671570767887607)
            ·
              refine ⟨102964144979507356151831411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68642763319671570767887607 102964144979507356151831411)
              ·
                refine ⟨154446217469261034227747117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102964144979507356151831411 154446217469261034227747117)
                ·
                  refine ⟨57917331550972887835405169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154446217469261034227747117 57917331550972887835405169)
                  ·
                    refine ⟨43437998663229665876553877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57917331550972887835405169 43437998663229665876553877)
                    ·
                      refine ⟨2036156187338890587963463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43437998663229665876553877 2036156187338890587963463)
                      ·
                        rfl

theorem cell23_3965400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_3965400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965400 prefixEnd_3965400 := by exact prefixLift 3965400
  have htrace : WordTrace (prefixWord ++ tailWord_3965400) baseStart_3965400 baseEnd_3965400 := by
    simpa [prefixWord, tailWord_3965400, baseEnd_3965400] using wordTrace_append hprefix tailTrace_3965400
  have hstable : (prefixWord ++ tailWord_3965400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965400).length < 2 ^ (prefixWord ++ tailWord_3965400).sum := by decide
  have hdescent : baseEnd_3965400 < baseStart_3965400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965418 : List Nat := [3, 1, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_3965418 : Nat := 118140960795 + 3965418 * 2 ^ 59
def prefixEnd_3965418 : Nat := 4983230072969 + 3 ^ 40 * 3965418 * 2
def baseEnd_3965418 : Nat := 678721809996890505846127

theorem tailTrace_3965418 : CollatzResearch.WordTrace tailWord_3965418 prefixEnd_3965418 678721809996890505846127 := by
  unfold tailWord_3965418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36157669086993825080430227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96420450898650200214480605 36157669086993825080430227)
  ·
    refine ⟨54236503630490737620645341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36157669086993825080430227 54236503630490737620645341)
    ·
      refine ⟨20338688861434026607742003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54236503630490737620645341 20338688861434026607742003)
      ·
        refine ⟨30508033292151039911613005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338688861434026607742003 30508033292151039911613005)
        ·
          refine ⟨11440512484556639966854877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30508033292151039911613005 11440512484556639966854877)
          ·
            refine ⟨4290192181708739987570579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11440512484556639966854877 4290192181708739987570579)
            ·
              refine ⟨6435288272563109981355869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290192181708739987570579 6435288272563109981355869)
              ·
                refine ⟨2413233102211166243008451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6435288272563109981355869 2413233102211166243008451)
                ·
                  refine ⟨3619849653316749364512677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413233102211166243008451 3619849653316749364512677)
                  ·
                    refine ⟨678721809996890505846127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3619849653316749364512677 678721809996890505846127)
                    ·
                      rfl

theorem cell23_3965418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_3965418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965418 prefixEnd_3965418 := by exact prefixLift 3965418
  have htrace : WordTrace (prefixWord ++ tailWord_3965418) baseStart_3965418 baseEnd_3965418 := by
    simpa [prefixWord, tailWord_3965418, baseEnd_3965418] using wordTrace_append hprefix tailTrace_3965418
  have hstable : (prefixWord ++ tailWord_3965418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965418).length < 2 ^ (prefixWord ++ tailWord_3965418).sum := by decide
  have hdescent : baseEnd_3965418 < baseStart_3965418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965427 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 1, 5]
def baseStart_3965427 : Nat := 118140960795 + 3965427 * 2 ^ 59
def prefixEnd_3965427 : Nat := 4983230072969 + 3 ^ 40 * 3965427 * 2
def baseEnd_3965427 : Nat := 678723350438853994108613

theorem tailTrace_3965427 : CollatzResearch.WordTrace tailWord_3965427 prefixEnd_3965427 678723350438853994108613 := by
  unfold tailWord_3965427
  simp only [CollatzResearch.WordTrace]
  refine ⟨144631004604942694858798535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96420669736628463239199023 144631004604942694858798535)
  ·
    refine ⟨216946506907414042288197803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144631004604942694858798535 216946506907414042288197803)
    ·
      refine ⟨325419760361121063432296705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216946506907414042288197803 325419760361121063432296705)
      ·
        refine ⟨244064820270840797574222529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325419760361121063432296705 244064820270840797574222529)
        ·
          refine ⟨183048615203130598180666897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244064820270840797574222529 183048615203130598180666897)
          ·
            refine ⟨137286461402347948635500173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183048615203130598180666897 137286461402347948635500173)
            ·
              refine ⟨51482423025880480738312565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137286461402347948635500173 51482423025880480738312565)
              ·
                refine ⟨4826477158676295069216803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51482423025880480738312565 4826477158676295069216803)
                ·
                  refine ⟨7239715738014442603825205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826477158676295069216803 7239715738014442603825205)
                  ·
                    refine ⟨678723350438853994108613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7239715738014442603825205 678723350438853994108613)
                    ·
                      rfl

theorem cell23_3965427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 5].length) (baseStart_3965427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965427 prefixEnd_3965427 := by exact prefixLift 3965427
  have htrace : WordTrace (prefixWord ++ tailWord_3965427) baseStart_3965427 baseEnd_3965427 := by
    simpa [prefixWord, tailWord_3965427, baseEnd_3965427] using wordTrace_append hprefix tailTrace_3965427
  have hstable : (prefixWord ++ tailWord_3965427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965427).length < 2 ^ (prefixWord ++ tailWord_3965427).sum := by decide
  have hdescent : baseEnd_3965427 < baseStart_3965427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965441 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_3965441 : Nat := 118140960795 + 3965441 * 2 ^ 59
def prefixEnd_3965441 : Nat := 4983230072969 + 3 ^ 40 * 3965441 * 2
def baseEnd_3965441 : Nat := 2036177240045724927550775

theorem tailTrace_3965441 : CollatzResearch.WordTrace tailWord_3965441 prefixEnd_3965441 2036177240045724927550775 := by
  unfold tailWord_3965441
  simp only [CollatzResearch.WordTrace]
  refine ⟨144631515226891975249808177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96421010151261316833205451 144631515226891975249808177)
  ·
    refine ⟨108473636420168981437356133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144631515226891975249808177 108473636420168981437356133)
    ·
      refine ⟨20338806828781684019504275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108473636420168981437356133 20338806828781684019504275)
      ·
        refine ⟨30508210243172526029256413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338806828781684019504275 30508210243172526029256413)
        ·
          refine ⟨11440578841189697260971155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30508210243172526029256413 11440578841189697260971155)
          ·
            refine ⟨17160868261784545891456733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11440578841189697260971155 17160868261784545891456733)
            ·
              refine ⟨6435325598169204709296275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17160868261784545891456733 6435325598169204709296275)
              ·
                refine ⟨9652988397253807063944413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435325598169204709296275 9652988397253807063944413)
                ·
                  refine ⟨3619870648970177648979155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9652988397253807063944413 3619870648970177648979155)
                  ·
                    refine ⟨5429805973455266473468733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619870648970177648979155 5429805973455266473468733)
                    ·
                      refine ⟨2036177240045724927550775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429805973455266473468733 2036177240045724927550775)
                      ·
                        rfl

theorem cell23_3965441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_3965441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965441 prefixEnd_3965441 := by exact prefixLift 3965441
  have htrace : WordTrace (prefixWord ++ tailWord_3965441) baseStart_3965441 baseEnd_3965441 := by
    simpa [prefixWord, tailWord_3965441, baseEnd_3965441] using wordTrace_append hprefix tailTrace_3965441
  have hstable : (prefixWord ++ tailWord_3965441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965441).length < 2 ^ (prefixWord ++ tailWord_3965441).sum := by decide
  have hdescent : baseEnd_3965441 < baseStart_3965441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965457 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 6, 4]
def baseStart_3965457 : Nat := 118140960795 + 3965457 * 2 ^ 59
def prefixEnd_3965457 : Nat := 4983230072969 + 3 ^ 40 * 3965457 * 2
def baseEnd_3965457 : Nat := 678728485245398954983567

theorem tailTrace_3965457 : CollatzResearch.WordTrace tailWord_3965457 prefixEnd_3965457 678728485245398954983567 := by
  unfold tailWord_3965457
  simp only [CollatzResearch.WordTrace]
  refine ⟨144632098794834009982390625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96421399196556006654927083 144632098794834009982390625)
  ·
    refine ⟨108474074096125507486792969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144632098794834009982390625 108474074096125507486792969)
    ·
      refine ⟨81355555572094130615094727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108474074096125507486792969 81355555572094130615094727)
      ·
        refine ⟨122033333358141195922642091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81355555572094130615094727 122033333358141195922642091)
        ·
          refine ⟨183050000037211793883963137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122033333358141195922642091 183050000037211793883963137)
          ·
            refine ⟨137287500027908845412972353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183050000037211793883963137 137287500027908845412972353)
            ·
              refine ⟨102965625020931634059729265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137287500027908845412972353 102965625020931634059729265)
              ·
                refine ⟨77224218765698725544796949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102965625020931634059729265 77224218765698725544796949)
                ·
                  refine ⟨3619885254642127759912357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77224218765698725544796949 3619885254642127759912357)
                  ·
                    refine ⟨678728485245398954983567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3619885254642127759912357 678728485245398954983567)
                    ·
                      rfl

theorem cell23_3965457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_3965457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965457 prefixEnd_3965457 := by exact prefixLift 3965457
  have htrace : WordTrace (prefixWord ++ tailWord_3965457) baseStart_3965457 baseEnd_3965457 := by
    simpa [prefixWord, tailWord_3965457, baseEnd_3965457] using wordTrace_append hprefix tailTrace_3965457
  have hstable : (prefixWord ++ tailWord_3965457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965457).length < 2 ^ (prefixWord ++ tailWord_3965457).sum := by decide
  have hdescent : baseEnd_3965457 < baseStart_3965457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965464 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3965464 : Nat := 118140960795 + 3965464 * 2 ^ 59
def prefixEnd_3965464 : Nat := 4983230072969 + 3 ^ 40 * 3965464 * 2
def baseEnd_3965464 : Nat := 2036189050100778337563169

theorem tailTrace_3965464 : CollatzResearch.WordTrace tailWord_3965464 prefixEnd_3965464 2036189050100778337563169 := by
  unfold tailWord_3965464
  simp only [CollatzResearch.WordTrace]
  refine ⟨72316177052904325088947723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96421569403872433451930297 72316177052904325088947723)
  ·
    refine ⟨108474265579356487633421585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72316177052904325088947723 108474265579356487633421585)
    ·
      refine ⟨81355699184517365725066189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108474265579356487633421585 81355699184517365725066189)
      ·
        refine ⟨30508387194194012146899821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81355699184517365725066189 30508387194194012146899821)
        ·
          refine ⟨11440645197822754555087433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30508387194194012146899821 11440645197822754555087433)
          ·
            refine ⟨8580483898367065916315575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11440645197822754555087433 8580483898367065916315575)
            ·
              refine ⟨12870725847550598874473363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8580483898367065916315575 12870725847550598874473363)
              ·
                refine ⟨19306088771325898311710045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12870725847550598874473363 19306088771325898311710045)
                ·
                  refine ⟨7239783289247211866891267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19306088771325898311710045 7239783289247211866891267)
                  ·
                    refine ⟨10859674933870817800336901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7239783289247211866891267 10859674933870817800336901)
                    ·
                      refine ⟨2036189050100778337563169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10859674933870817800336901 2036189050100778337563169)
                      ·
                        rfl

theorem cell23_3965464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3965464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965464 prefixEnd_3965464 := by exact prefixLift 3965464
  have htrace : WordTrace (prefixWord ++ tailWord_3965464) baseStart_3965464 baseEnd_3965464 := by
    simpa [prefixWord, tailWord_3965464, baseEnd_3965464] using wordTrace_append hprefix tailTrace_3965464
  have hstable : (prefixWord ++ tailWord_3965464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965464).length < 2 ^ (prefixWord ++ tailWord_3965464).sum := by decide
  have hdescent : baseEnd_3965464 < baseStart_3965464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965477 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3965477 : Nat := 118140960795 + 3965477 * 2 ^ 59
def prefixEnd_3965477 : Nat := 4983230072969 + 3 ^ 40 * 3965477 * 2
def baseEnd_3965477 : Nat := 2036195725349286786700609

theorem tailTrace_3965477 : CollatzResearch.WordTrace tailWord_3965477 prefixEnd_3965477 2036195725349286786700609 := by
  unfold tailWord_3965477
  simp only [CollatzResearch.WordTrace]
  refine ⟨144632828254761553398118685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96421885503174368932079123 144632828254761553398118685)
  ·
    refine ⟨54237310595535582524294507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144632828254761553398118685 54237310595535582524294507)
    ·
      refine ⟨81355965893303373786441761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54237310595535582524294507 81355965893303373786441761)
      ·
        refine ⟨61016974419977530339831321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81355965893303373786441761 61016974419977530339831321)
        ·
          refine ⟨45762730814983147754873491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61016974419977530339831321 45762730814983147754873491)
          ·
            refine ⟨68644096222474721632310237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45762730814983147754873491 68644096222474721632310237)
            ·
              refine ⟨25741536083428020612116339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68644096222474721632310237 25741536083428020612116339)
              ·
                refine ⟨38612304125142030918174509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25741536083428020612116339 38612304125142030918174509)
                ·
                  refine ⟨14479614046928261594315441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38612304125142030918174509 14479614046928261594315441)
                  ·
                    refine ⟨10859710535196196195736581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14479614046928261594315441 10859710535196196195736581)
                    ·
                      refine ⟨2036195725349286786700609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10859710535196196195736581 2036195725349286786700609)
                      ·
                        rfl

theorem cell23_3965477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3965477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965477 prefixEnd_3965477 := by exact prefixLift 3965477
  have htrace : WordTrace (prefixWord ++ tailWord_3965477) baseStart_3965477 baseEnd_3965477 := by
    simpa [prefixWord, tailWord_3965477, baseEnd_3965477] using wordTrace_append hprefix tailTrace_3965477
  have hstable : (prefixWord ++ tailWord_3965477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965477).length < 2 ^ (prefixWord ++ tailWord_3965477).sum := by decide
  have hdescent : baseEnd_3965477 < baseStart_3965477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965484 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_3965484 : Nat := 118140960795 + 3965484 * 2 ^ 59
def prefixEnd_3965484 : Nat := 4983230072969 + 3 ^ 40 * 3965484 * 2
def baseEnd_3965484 : Nat := 2036199319713868259313077

theorem tailTrace_3965484 : CollatzResearch.WordTrace tailWord_3965484 prefixEnd_3965484 2036199319713868259313077 := by
  unfold tailWord_3965484
  simp only [CollatzResearch.WordTrace]
  refine ⟨72316541782868096796811753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96422055710490795729082337 72316541782868096796811753)
  ·
    refine ⟨54237406337151072597608815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72316541782868096796811753 54237406337151072597608815)
    ·
      refine ⟨81356109505726608896413223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54237406337151072597608815 81356109505726608896413223)
      ·
        refine ⟨122034164258589913344619835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81356109505726608896413223 122034164258589913344619835)
        ·
          refine ⟨183051246387884870016929753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122034164258589913344619835 183051246387884870016929753)
          ·
            refine ⟨137288434790913652512697315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183051246387884870016929753 137288434790913652512697315)
            ·
              refine ⟨205932652186370478769045973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137288434790913652512697315 205932652186370478769045973)
              ·
                refine ⟨4826546535618058096149515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 205932652186370478769045973 4826546535618058096149515)
                ·
                  refine ⟨7239819803427087144224273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826546535618058096149515 7239819803427087144224273)
                  ·
                    refine ⟨5429864852570315358168205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7239819803427087144224273 5429864852570315358168205)
                    ·
                      refine ⟨2036199319713868259313077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429864852570315358168205 2036199319713868259313077)
                      ·
                        rfl

theorem cell23_3965484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_3965484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965484 prefixEnd_3965484 := by exact prefixLift 3965484
  have htrace : WordTrace (prefixWord ++ tailWord_3965484) baseStart_3965484 baseEnd_3965484 := by
    simpa [prefixWord, tailWord_3965484, baseEnd_3965484] using wordTrace_append hprefix tailTrace_3965484
  have hstable : (prefixWord ++ tailWord_3965484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965484).length < 2 ^ (prefixWord ++ tailWord_3965484).sum := by decide
  have hdescent : baseEnd_3965484 < baseStart_3965484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965492 : List Nat := [2, 5, 1, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3965492 : Nat := 118140960795 + 3965492 * 2 ^ 59
def prefixEnd_3965492 : Nat := 4983230072969 + 3 ^ 40 * 3965492 * 2
def baseEnd_3965492 : Nat := 2036203427559104228013041

theorem tailTrace_3965492 : CollatzResearch.WordTrace tailWord_3965492 prefixEnd_3965492 2036203427559104228013041 := by
  unfold tailWord_3965492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72316687674853605479957365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96422250233138140639943153 72316687674853605479957365)
  ·
    refine ⟨6779689469517525513746003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72316687674853605479957365 6779689469517525513746003)
    ·
      refine ⟨10169534204276288270619005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6779689469517525513746003 10169534204276288270619005)
      ·
        refine ⟨3813575326603608101482127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10169534204276288270619005 3813575326603608101482127)
        ·
          refine ⟨5720362989905412152223191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813575326603608101482127 5720362989905412152223191)
          ·
            refine ⟨8580544484858118228334787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720362989905412152223191 8580544484858118228334787)
            ·
              refine ⟨12870816727287177342502181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8580544484858118228334787 12870816727287177342502181)
              ·
                refine ⟨2413278136366345751719159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12870816727287177342502181 2413278136366345751719159)
                ·
                  refine ⟨3619917204549518627578739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413278136366345751719159 3619917204549518627578739)
                  ·
                    refine ⟨5429875806824277941368109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619917204549518627578739 5429875806824277941368109)
                    ·
                      refine ⟨2036203427559104228013041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429875806824277941368109 2036203427559104228013041)
                      ·
                        rfl

theorem cell23_3965492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3965492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965492 prefixEnd_3965492 := by exact prefixLift 3965492
  have htrace : WordTrace (prefixWord ++ tailWord_3965492) baseStart_3965492 baseEnd_3965492 := by
    simpa [prefixWord, tailWord_3965492, baseEnd_3965492] using wordTrace_append hprefix tailTrace_3965492
  have hstable : (prefixWord ++ tailWord_3965492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965492).length < 2 ^ (prefixWord ++ tailWord_3965492).sum := by decide
  have hdescent : baseEnd_3965492 < baseStart_3965492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965514 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_3965514 : Nat := 118140960795 + 3965514 * 2 ^ 59
def prefixEnd_3965514 : Nat := 4983230072969 + 3 ^ 40 * 3965514 * 2
def baseEnd_3965514 : Nat := 2036214724133503141937939

theorem tailTrace_3965514 : CollatzResearch.WordTrace tailWord_3965514 prefixEnd_3965514 2036214724133503141937939 := by
  unfold tailWord_3965514
  simp only [CollatzResearch.WordTrace]
  refine ⟨36158544438906877179303899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96422785170418339144810397 36158544438906877179303899)
  ·
    refine ⟨54237816658360315768955849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36158544438906877179303899 54237816658360315768955849)
    ·
      refine ⟨40678362493770236826716887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54237816658360315768955849 40678362493770236826716887)
      ·
        refine ⟨61017543740655355240075331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40678362493770236826716887 61017543740655355240075331)
        ·
          refine ⟨91526315610983032860112997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61017543740655355240075331 91526315610983032860112997)
          ·
            refine ⟨17161184177059318661271187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91526315610983032860112997 17161184177059318661271187)
            ·
              refine ⟨25741776265588977991906781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17161184177059318661271187 25741776265588977991906781)
              ·
                refine ⟨9653166099595866746965043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25741776265588977991906781 9653166099595866746965043)
                ·
                  refine ⟨14479749149393800120447565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9653166099595866746965043 14479749149393800120447565)
                  ·
                    refine ⟨5429905931022675045167837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14479749149393800120447565 5429905931022675045167837)
                    ·
                      refine ⟨2036214724133503141937939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429905931022675045167837 2036214724133503141937939)
                      ·
                        rfl

theorem cell23_3965514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_3965514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965514 prefixEnd_3965514 := by exact prefixLift 3965514
  have htrace : WordTrace (prefixWord ++ tailWord_3965514) baseStart_3965514 baseEnd_3965514 := by
    simpa [prefixWord, tailWord_3965514, baseEnd_3965514] using wordTrace_append hprefix tailTrace_3965514
  have hstable : (prefixWord ++ tailWord_3965514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965514).length < 2 ^ (prefixWord ++ tailWord_3965514).sum := by decide
  have hdescent : baseEnd_3965514 < baseStart_3965514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965527 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3965527 : Nat := 118140960795 + 3965527 * 2 ^ 59
def prefixEnd_3965527 : Nat := 4983230072969 + 3 ^ 40 * 3965527 * 2
def baseEnd_3965527 : Nat := 2036221399382011591075379

theorem tailTrace_3965527 : CollatzResearch.WordTrace tailWord_3965527 prefixEnd_3965527 2036221399382011591075379 := by
  unfold tailWord_3965527
  simp only [CollatzResearch.WordTrace]
  refine ⟨144634651904580411937438835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96423101269720274624959223 144634651904580411937438835)
  ·
    refine ⟨216951977856870617906158253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144634651904580411937438835 216951977856870617906158253)
    ·
      refine ⟨81356991696326481714809345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216951977856870617906158253 81356991696326481714809345)
      ·
        refine ⟨61017743772244861286107009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81356991696326481714809345 61017743772244861286107009)
        ·
          refine ⟨45763307829183645964580257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61017743772244861286107009 45763307829183645964580257)
          ·
            refine ⟨34322480871887734473435193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45763307829183645964580257 34322480871887734473435193)
            ·
              refine ⟨25741860653915800855076395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34322480871887734473435193 25741860653915800855076395)
              ·
                refine ⟨38612790980873701282614593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25741860653915800855076395 38612790980873701282614593)
                ·
                  refine ⟨28959593235655275961960945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38612790980873701282614593 28959593235655275961960945)
                  ·
                    refine ⟨21719694926741456971470709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28959593235655275961960945 21719694926741456971470709)
                    ·
                      refine ⟨2036221399382011591075379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21719694926741456971470709 2036221399382011591075379)
                      ·
                        rfl

theorem cell23_3965527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3965527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965527 prefixEnd_3965527 := by exact prefixLift 3965527
  have htrace : WordTrace (prefixWord ++ tailWord_3965527) baseStart_3965527 baseEnd_3965527 := by
    simpa [prefixWord, tailWord_3965527, baseEnd_3965527] using wordTrace_append hprefix tailTrace_3965527
  have hstable : (prefixWord ++ tailWord_3965527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965527).length < 2 ^ (prefixWord ++ tailWord_3965527).sum := by decide
  have hdescent : baseEnd_3965527 < baseStart_3965527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965532 : List Nat := [2, 2, 4, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3965532 : Nat := 118140960795 + 3965532 * 2 ^ 59
def prefixEnd_3965532 : Nat := 4983230072969 + 3 ^ 40 * 3965532 * 2
def baseEnd_3965532 : Nat := 2036223966785284071512857

theorem tailTrace_3965532 : CollatzResearch.WordTrace tailWord_3965532 prefixEnd_3965532 2036223966785284071512857 := by
  unfold tailWord_3965532
  simp only [CollatzResearch.WordTrace]
  refine ⟨72317417134781148895685425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96423222846374865194247233 72317417134781148895685425)
  ·
    refine ⟨54238062851085861671764069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72317417134781148895685425 54238062851085861671764069)
    ·
      refine ⟨10169636784578599063455763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54238062851085861671764069 10169636784578599063455763)
      ·
        refine ⟨15254455176867898595183645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169636784578599063455763 15254455176867898595183645)
        ·
          refine ⟨5720420691325461973193867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15254455176867898595183645 5720420691325461973193867)
          ·
            refine ⟨8580631036988192959790801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720420691325461973193867 8580631036988192959790801)
            ·
              refine ⟨6435473277741144719843101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8580631036988192959790801 6435473277741144719843101)
              ·
                refine ⟨2413302479152929269941163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6435473277741144719843101 2413302479152929269941163)
                ·
                  refine ⟨3619953718729393904911745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413302479152929269941163 3619953718729393904911745)
                  ·
                    refine ⟨2714965289047045428683809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3619953718729393904911745 2714965289047045428683809)
                    ·
                      refine ⟨2036223966785284071512857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714965289047045428683809 2036223966785284071512857)
                      ·
                        rfl

theorem cell23_3965532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3965532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965532 prefixEnd_3965532 := by exact prefixLift 3965532
  have htrace : WordTrace (prefixWord ++ tailWord_3965532) baseStart_3965532 baseEnd_3965532 := by
    simpa [prefixWord, tailWord_3965532, baseEnd_3965532] using wordTrace_append hprefix tailTrace_3965532
  have hstable : (prefixWord ++ tailWord_3965532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965532).length < 2 ^ (prefixWord ++ tailWord_3965532).sum := by decide
  have hdescent : baseEnd_3965532 < baseStart_3965532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965565 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_3965565 : Nat := 118140960795 + 3965565 * 2 ^ 59
def prefixEnd_3965565 : Nat := 4983230072969 + 3 ^ 40 * 3965565 * 2
def baseEnd_3965565 : Nat := 2036240911646882442400205

theorem tailTrace_3965565 : CollatzResearch.WordTrace tailWord_3965565 prefixEnd_3965565 2036240911646882442400205 := by
  unfold tailWord_3965565
  simp only [CollatzResearch.WordTrace]
  refine ⟨144636037878442744427322149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96424025252295162951548099 144636037878442744427322149)
  ·
    refine ⟨27119257102208014580122903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144636037878442744427322149 27119257102208014580122903)
    ·
      refine ⟨40678885653312021870184355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27119257102208014580122903 40678885653312021870184355)
      ·
        refine ⟨61018328479968032805276533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40678885653312021870184355 61018328479968032805276533)
        ·
          refine ⟨5720468294997003075494675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61018328479968032805276533 5720468294997003075494675)
          ·
            refine ⟨8580702442495504613242013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720468294997003075494675 8580702442495504613242013)
            ·
              refine ⟨3217763415935814229965755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8580702442495504613242013 3217763415935814229965755)
              ·
                refine ⟨4826645123903721344948633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217763415935814229965755 4826645123903721344948633)
                ·
                  refine ⟨3619983842927791008711475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4826645123903721344948633 3619983842927791008711475)
                  ·
                    refine ⟨5429975764391686513067213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619983842927791008711475 5429975764391686513067213)
                    ·
                      refine ⟨2036240911646882442400205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5429975764391686513067213 2036240911646882442400205)
                      ·
                        rfl

theorem cell23_3965565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_3965565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965565 prefixEnd_3965565 := by exact prefixLift 3965565
  have htrace : WordTrace (prefixWord ++ tailWord_3965565) baseStart_3965565 baseEnd_3965565 := by
    simpa [prefixWord, tailWord_3965565, baseEnd_3965565] using wordTrace_append hprefix tailTrace_3965565
  have hstable : (prefixWord ++ tailWord_3965565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965565).length < 2 ^ (prefixWord ++ tailWord_3965565).sum := by decide
  have hdescent : baseEnd_3965565 < baseStart_3965565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965567 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_3965567 : Nat := 118140960795 + 3965567 * 2 ^ 59
def prefixEnd_3965567 : Nat := 4983230072969 + 3 ^ 40 * 3965567 * 2
def baseEnd_3965567 : Nat := 2036241938608191434575195

theorem tailTrace_3965567 : CollatzResearch.WordTrace tailWord_3965567 prefixEnd_3965567 2036241938608191434575195 := by
  unfold tailWord_3965567
  simp only [CollatzResearch.WordTrace]
  refine ⟨144636110824435498768894955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96424073882956999179263303 144636110824435498768894955)
  ·
    refine ⟨216954166236653248153342433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144636110824435498768894955 216954166236653248153342433)
    ·
      refine ⟨162715624677489936115006825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216954166236653248153342433 162715624677489936115006825)
      ·
        refine ⟨122036718508117452086255119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162715624677489936115006825 122036718508117452086255119)
        ·
          refine ⟨183055077762176178129382679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122036718508117452086255119 183055077762176178129382679)
          ·
            refine ⟨274582616643264267194074019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183055077762176178129382679 274582616643264267194074019)
            ·
              refine ⟨411873924964896400791111029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274582616643264267194074019 411873924964896400791111029)
              ·
                refine ⟨38613180465459037574166659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411873924964896400791111029 38613180465459037574166659)
                ·
                  refine ⟨57919770698188556361249989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38613180465459037574166659 57919770698188556361249989)
                  ·
                    refine ⟨10859957005910354317734373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57919770698188556361249989 10859957005910354317734373)
                    ·
                      refine ⟨2036241938608191434575195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10859957005910354317734373 2036241938608191434575195)
                      ·
                        rfl

theorem cell23_3965567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_3965567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965567 prefixEnd_3965567 := by exact prefixLift 3965567
  have htrace : WordTrace (prefixWord ++ tailWord_3965567) baseStart_3965567 baseEnd_3965567 := by
    simpa [prefixWord, tailWord_3965567, baseEnd_3965567] using wordTrace_append hprefix tailTrace_3965567
  have hstable : (prefixWord ++ tailWord_3965567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965567).length < 2 ^ (prefixWord ++ tailWord_3965567).sum := by decide
  have hdescent : baseEnd_3965567 < baseStart_3965567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965571 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 1, 4, 2]
def baseStart_3965571 : Nat := 118140960795 + 3965571 * 2 ^ 59
def prefixEnd_3965571 : Nat := 4983230072969 + 3 ^ 40 * 3965571 * 2
def baseEnd_3965571 : Nat := 2036243992530809418925177

theorem tailTrace_3965571 : CollatzResearch.WordTrace tailWord_3965571 prefixEnd_3965571 2036243992530809418925177 := by
  unfold tailWord_3965571
  simp only [CollatzResearch.WordTrace]
  refine ⟨144636256716421007452040567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96424171144280671634693711 144636256716421007452040567)
  ·
    refine ⟨216954385074631511178060851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144636256716421007452040567 216954385074631511178060851)
    ·
      refine ⟨325431577611947266767091277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216954385074631511178060851 325431577611947266767091277)
      ·
        refine ⟨122036841604480225037659229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325431577611947266767091277 122036841604480225037659229)
        ·
          refine ⟨45763815601680084389122211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122036841604480225037659229 45763815601680084389122211)
          ·
            refine ⟨68645723402520126583683317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45763815601680084389122211 68645723402520126583683317)
            ·
              refine ⟨6435536568986261867220311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68645723402520126583683317 6435536568986261867220311)
              ·
                refine ⟨9653304853479392800830467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435536568986261867220311 9653304853479392800830467)
                ·
                  refine ⟨14479957280219089201245701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9653304853479392800830467 14479957280219089201245701)
                  ·
                    refine ⟨2714991990041079225233569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14479957280219089201245701 2714991990041079225233569)
                    ·
                      refine ⟨2036243992530809418925177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2714991990041079225233569 2036243992530809418925177)
                      ·
                        rfl

theorem cell23_3965571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_3965571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965571 prefixEnd_3965571 := by exact prefixLift 3965571
  have htrace : WordTrace (prefixWord ++ tailWord_3965571) baseStart_3965571 baseEnd_3965571 := by
    simpa [prefixWord, tailWord_3965571, baseEnd_3965571] using wordTrace_append hprefix tailTrace_3965571
  have hstable : (prefixWord ++ tailWord_3965571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965571).length < 2 ^ (prefixWord ++ tailWord_3965571).sum := by decide
  have hdescent : baseEnd_3965571 < baseStart_3965571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965647 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_3965647 : Nat := 118140960795 + 3965647 * 2 ^ 59
def prefixEnd_3965647 : Nat := 4983230072969 + 3 ^ 40 * 3965647 * 2
def baseEnd_3965647 : Nat := 2036283017060551121574827

theorem tailTrace_3965647 : CollatzResearch.WordTrace tailWord_3965647 prefixEnd_3965647 2036283017060551121574827 := by
  unfold tailWord_3965647
  simp only [CollatzResearch.WordTrace]
  refine ⟨144639028664145672431807195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96426019109430448287871463 144639028664145672431807195)
  ·
    refine ⟨216958542996218508647710793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144639028664145672431807195 216958542996218508647710793)
    ·
      refine ⟨162718907247163881485783095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216958542996218508647710793 162718907247163881485783095)
      ·
        refine ⟨244078360870745822228674643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162718907247163881485783095 244078360870745822228674643)
        ·
          refine ⟨366117541306118733343011965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244078360870745822228674643 366117541306118733343011965)
          ·
            refine ⟨137294077989794525003629487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366117541306118733343011965 137294077989794525003629487)
            ·
              refine ⟨205941116984691787505444231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137294077989794525003629487 205941116984691787505444231)
              ·
                refine ⟨308911675477037681258166347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205941116984691787505444231 308911675477037681258166347)
                ·
                  refine ⟨463367513215556521887249521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308911675477037681258166347 463367513215556521887249521)
                  ·
                    refine ⟨347525634911667391415437141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 463367513215556521887249521 347525634911667391415437141)
                    ·
                      refine ⟨2036283017060551121574827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 347525634911667391415437141 2036283017060551121574827)
                      ·
                        rfl

theorem cell23_3965647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_3965647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965647 prefixEnd_3965647 := by exact prefixLift 3965647
  have htrace : WordTrace (prefixWord ++ tailWord_3965647) baseStart_3965647 baseEnd_3965647 := by
    simpa [prefixWord, tailWord_3965647, baseEnd_3965647] using wordTrace_append hprefix tailTrace_3965647
  have hstable : (prefixWord ++ tailWord_3965647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965647).length < 2 ^ (prefixWord ++ tailWord_3965647).sum := by decide
  have hdescent : baseEnd_3965647 < baseStart_3965647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965664 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3]
def baseStart_3965664 : Nat := 118140960795 + 3965664 * 2 ^ 59
def prefixEnd_3965664 : Nat := 4983230072969 + 3 ^ 40 * 3965664 * 2
def baseEnd_3965664 : Nat := 2036291746231677555062249

theorem tailTrace_3965664 : CollatzResearch.WordTrace tailWord_3965664 prefixEnd_3965664 2036291746231677555062249 := by
  unfold tailWord_3965664
  simp only [CollatzResearch.WordTrace]
  refine ⟨72319824352542042167588023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96426432470056056223450697 72319824352542042167588023)
  ·
    refine ⟨108479736528813063251382035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72319824352542042167588023 108479736528813063251382035)
    ·
      refine ⟨162719604793219594877073053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108479736528813063251382035 162719604793219594877073053)
      ·
        refine ⟨61019851797457348078902395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162719604793219594877073053 61019851797457348078902395)
        ·
          refine ⟨91529777696186022118353593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61019851797457348078902395 91529777696186022118353593)
          ·
            refine ⟨68647333272139516588765195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91529777696186022118353593 68647333272139516588765195)
            ·
              refine ⟨102970999908209274883147793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68647333272139516588765195 102970999908209274883147793)
              ·
                refine ⟨77228249931156956162360845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102970999908209274883147793 77228249931156956162360845)
                ·
                  refine ⟨28960593724183858560885317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77228249931156956162360845 28960593724183858560885317)
                  ·
                    refine ⟨5430111323284473480165997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28960593724183858560885317 5430111323284473480165997)
                    ·
                      refine ⟨2036291746231677555062249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430111323284473480165997 2036291746231677555062249)
                      ·
                        rfl

theorem cell23_3965664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_3965664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965664 prefixEnd_3965664 := by exact prefixLift 3965664
  have htrace : WordTrace (prefixWord ++ tailWord_3965664) baseStart_3965664 baseEnd_3965664 := by
    simpa [prefixWord, tailWord_3965664, baseEnd_3965664] using wordTrace_append hprefix tailTrace_3965664
  have hstable : (prefixWord ++ tailWord_3965664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965664).length < 2 ^ (prefixWord ++ tailWord_3965664).sum := by decide
  have hdescent : baseEnd_3965664 < baseStart_3965664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965674 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3965674 : Nat := 118140960795 + 3965674 * 2 ^ 59
def prefixEnd_3965674 : Nat := 4983230072969 + 3 ^ 40 * 3965674 * 2
def baseEnd_3965674 : Nat := 2036296881038222515937203

theorem tailTrace_3965674 : CollatzResearch.WordTrace tailWord_3965674 prefixEnd_3965674 2036296881038222515937203 := by
  unfold tailWord_3965674
  simp only [CollatzResearch.WordTrace]
  refine ⟨36160003358761964010760019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96426675623365237362026717 36160003358761964010760019)
  ·
    refine ⟨54240005038142946016140029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36160003358761964010760019 54240005038142946016140029)
    ·
      refine ⟨20340001889303604756052511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54240005038142946016140029 20340001889303604756052511)
      ·
        refine ⟨30510002833955407134078767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20340001889303604756052511 30510002833955407134078767)
        ·
          refine ⟨45765004250933110701118151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30510002833955407134078767 45765004250933110701118151)
          ·
            refine ⟨68647506376399666051677227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45765004250933110701118151 68647506376399666051677227)
            ·
              refine ⟨102971259564599499077515841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68647506376399666051677227 102971259564599499077515841)
              ·
                refine ⟨77228444673449624308136881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102971259564599499077515841 77228444673449624308136881)
                ·
                  refine ⟨57921333505087218231102661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77228444673449624308136881 57921333505087218231102661)
                  ·
                    refine ⟨10860250032203853418331749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57921333505087218231102661 10860250032203853418331749)
                    ·
                      refine ⟨2036296881038222515937203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10860250032203853418331749 2036296881038222515937203)
                      ·
                        rfl

theorem cell23_3965674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3965674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965674 prefixEnd_3965674 := by exact prefixLift 3965674
  have htrace : WordTrace (prefixWord ++ tailWord_3965674) baseStart_3965674 baseEnd_3965674 := by
    simpa [prefixWord, tailWord_3965674, baseEnd_3965674] using wordTrace_append hprefix tailTrace_3965674
  have hstable : (prefixWord ++ tailWord_3965674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965674).length < 2 ^ (prefixWord ++ tailWord_3965674).sum := by decide
  have hdescent : baseEnd_3965674 < baseStart_3965674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965678 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_3965678 : Nat := 118140960795 + 3965678 * 2 ^ 59
def prefixEnd_3965678 : Nat := 4983230072969 + 3 ^ 40 * 3965678 * 2
def baseEnd_3965678 : Nat := 2036298934960840500287185

theorem tailTrace_3965678 : CollatzResearch.WordTrace tailWord_3965678 prefixEnd_3965678 2036298934960840500287185 := by
  unfold tailWord_3965678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18080019915879170590773211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96426772884688909817457125 18080019915879170590773211)
  ·
    refine ⟨27120029873818755886159817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18080019915879170590773211 27120029873818755886159817)
    ·
      refine ⟨20340022405364066914619863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27120029873818755886159817 20340022405364066914619863)
      ·
        refine ⟨30510033608046100371929795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20340022405364066914619863 30510033608046100371929795)
        ·
          refine ⟨45765050412069150557894693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30510033608046100371929795 45765050412069150557894693)
          ·
            refine ⟨8580946952262965729605255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45765050412069150557894693 8580946952262965729605255)
            ·
              refine ⟨12871420428394448594407883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8580946952262965729605255 12871420428394448594407883)
              ·
                refine ⟨19307130642591672891611825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12871420428394448594407883 19307130642591672891611825)
                ·
                  refine ⟨14480347981943754668708869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19307130642591672891611825 14480347981943754668708869)
                  ·
                    refine ⟨2715065246614454000382913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14480347981943754668708869 2715065246614454000382913)
                    ·
                      refine ⟨2036298934960840500287185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715065246614454000382913 2036298934960840500287185)
                      ·
                        rfl

theorem cell23_3965678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_3965678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965678 prefixEnd_3965678 := by exact prefixLift 3965678
  have htrace : WordTrace (prefixWord ++ tailWord_3965678) baseStart_3965678 baseEnd_3965678 := by
    simpa [prefixWord, tailWord_3965678, baseEnd_3965678] using wordTrace_append hprefix tailTrace_3965678
  have hstable : (prefixWord ++ tailWord_3965678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965678).length < 2 ^ (prefixWord ++ tailWord_3965678).sum := by decide
  have hdescent : baseEnd_3965678 < baseStart_3965678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965698 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_3965698 : Nat := 118140960795 + 3965698 * 2 ^ 59
def prefixEnd_3965698 : Nat := 4983230072969 + 3 ^ 40 * 3965698 * 2
def baseEnd_3965698 : Nat := 2036309204573930422037093

theorem tailTrace_3965698 : CollatzResearch.WordTrace tailWord_3965698 prefixEnd_3965698 2036309204573930422037093 := by
  unfold tailWord_3965698
  simp only [CollatzResearch.WordTrace]
  refine ⟨36160222196740227035478437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96427259191307272094609165 36160222196740227035478437)
  ·
    refine ⟨6780041661888792569152207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36160222196740227035478437 6780041661888792569152207)
    ·
      refine ⟨10170062492833188853728311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780041661888792569152207 10170062492833188853728311)
      ·
        refine ⟨15255093739249783280592467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10170062492833188853728311 15255093739249783280592467)
        ·
          refine ⟨22882640608874674920888701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15255093739249783280592467 22882640608874674920888701)
          ·
            refine ⟨8580990228328003095333263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22882640608874674920888701 8580990228328003095333263)
            ·
              refine ⟨12871485342492004642999895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8580990228328003095333263 12871485342492004642999895)
              ·
                refine ⟨19307228013738006964499843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12871485342492004642999895 19307228013738006964499843)
                ·
                  refine ⟨28960842020607010446749765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19307228013738006964499843 28960842020607010446749765)
                  ·
                    refine ⟨5430157878863814458765581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28960842020607010446749765 5430157878863814458765581)
                    ·
                      refine ⟨2036309204573930422037093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430157878863814458765581 2036309204573930422037093)
                      ·
                        rfl

theorem cell23_3965698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_3965698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965698 prefixEnd_3965698 := by exact prefixLift 3965698
  have htrace : WordTrace (prefixWord ++ tailWord_3965698) baseStart_3965698 baseEnd_3965698 := by
    simpa [prefixWord, tailWord_3965698, baseEnd_3965698] using wordTrace_append hprefix tailTrace_3965698
  have hstable : (prefixWord ++ tailWord_3965698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965698).length < 2 ^ (prefixWord ++ tailWord_3965698).sum := by decide
  have hdescent : baseEnd_3965698 < baseStart_3965698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965711 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 3]
def baseStart_3965711 : Nat := 118140960795 + 3965711 * 2 ^ 59
def prefixEnd_3965711 : Nat := 4983230072969 + 3 ^ 40 * 3965711 * 2
def baseEnd_3965711 : Nat := 2036315879822438871174533

theorem tailTrace_3965711 : CollatzResearch.WordTrace tailWord_3965711 prefixEnd_3965711 2036315879822438871174533 := by
  unfold tailWord_3965711
  simp only [CollatzResearch.WordTrace]
  refine ⟨144641362935913811362136987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96427575290609207574757991 144641362935913811362136987)
  ·
    refine ⟨216962044403870717043205481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144641362935913811362136987 216962044403870717043205481)
    ·
      refine ⟨162721533302903037782404111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216962044403870717043205481 162721533302903037782404111)
      ·
        refine ⟨244082299954354556673606167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162721533302903037782404111 244082299954354556673606167)
        ·
          refine ⟨366123449931531835010409251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244082299954354556673606167 366123449931531835010409251)
          ·
            refine ⟨549185174897297752515613877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366123449931531835010409251 549185174897297752515613877)
            ·
              refine ⟨51486110146621664298338801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 549185174897297752515613877 51486110146621664298338801)
              ·
                refine ⟨38614582609966248223754101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51486110146621664298338801 38614582609966248223754101)
                ·
                  refine ⟨3620117119684335770976947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38614582609966248223754101 3620117119684335770976947)
                  ·
                    refine ⟨5430175679526503656465421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3620117119684335770976947 5430175679526503656465421)
                    ·
                      refine ⟨2036315879822438871174533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430175679526503656465421 2036315879822438871174533)
                      ·
                        rfl

theorem cell23_3965711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 3].length) (baseStart_3965711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965711 prefixEnd_3965711 := by exact prefixLift 3965711
  have htrace : WordTrace (prefixWord ++ tailWord_3965711) baseStart_3965711 baseEnd_3965711 := by
    simpa [prefixWord, tailWord_3965711, baseEnd_3965711] using wordTrace_append hprefix tailTrace_3965711
  have hstable : (prefixWord ++ tailWord_3965711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965711).length < 2 ^ (prefixWord ++ tailWord_3965711).sum := by decide
  have hdescent : baseEnd_3965711 < baseStart_3965711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965728 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3965728 : Nat := 118140960795 + 3965728 * 2 ^ 59
def prefixEnd_3965728 : Nat := 4983230072969 + 3 ^ 40 * 3965728 * 2
def baseEnd_3965728 : Nat := 2036324608993565304661955

theorem tailTrace_3965728 : CollatzResearch.WordTrace tailWord_3965728 prefixEnd_3965728 2036324608993565304661955 := by
  unfold tailWord_3965728
  simp only [CollatzResearch.WordTrace]
  refine ⟨72320991488426111632752919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96427988651234815510337225 72320991488426111632752919)
  ·
    refine ⟨108481487232639167449129379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72320991488426111632752919 108481487232639167449129379)
    ·
      refine ⟨162722230848958751173694069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108481487232639167449129379 162722230848958751173694069)
      ·
        refine ⟨15255209142089882922533819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162722230848958751173694069 15255209142089882922533819)
        ·
          refine ⟨22882813713134824383800729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15255209142089882922533819 22882813713134824383800729)
          ·
            refine ⟨17162110284851118287850547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22882813713134824383800729 17162110284851118287850547)
            ·
              refine ⟨25743165427276677431775821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17162110284851118287850547 25743165427276677431775821)
              ·
                refine ⟨9653687035228754036915933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25743165427276677431775821 9653687035228754036915933)
                ·
                  refine ⟨3620132638210782763843475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9653687035228754036915933 3620132638210782763843475)
                  ·
                    refine ⟨5430198957316174145765213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3620132638210782763843475 5430198957316174145765213)
                    ·
                      refine ⟨2036324608993565304661955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430198957316174145765213 2036324608993565304661955)
                      ·
                        rfl

theorem cell23_3965728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3965728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965728 prefixEnd_3965728 := by exact prefixLift 3965728
  have htrace : WordTrace (prefixWord ++ tailWord_3965728) baseStart_3965728 baseEnd_3965728 := by
    simpa [prefixWord, tailWord_3965728, baseEnd_3965728] using wordTrace_append hprefix tailTrace_3965728
  have hstable : (prefixWord ++ tailWord_3965728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965728).length < 2 ^ (prefixWord ++ tailWord_3965728).sum := by decide
  have hdescent : baseEnd_3965728 < baseStart_3965728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965751 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 2, 6, 2]
def baseStart_3965751 : Nat := 118140960795 + 3965751 * 2 ^ 59
def prefixEnd_3965751 : Nat := 4983230072969 + 3 ^ 40 * 3965751 * 2
def baseEnd_3965751 : Nat := 2036336419048618714674349

theorem tailTrace_3965751 : CollatzResearch.WordTrace tailWord_3965751 prefixEnd_3965751 2036336419048618714674349 := by
  unfold tailWord_3965751
  simp only [CollatzResearch.WordTrace]
  refine ⟨144642821855768898193593107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96428547903845932129062071 144642821855768898193593107)
  ·
    refine ⟨216964232783653347290389661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144642821855768898193593107 216964232783653347290389661)
    ·
      refine ⟨81361587293870005233896123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216964232783653347290389661 81361587293870005233896123)
      ·
        refine ⟨122042380940805007850844185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81361587293870005233896123 122042380940805007850844185)
        ·
          refine ⟨91531785705603755888133139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122042380940805007850844185 91531785705603755888133139)
          ·
            refine ⟨137297678558405633832199709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91531785705603755888133139 137297678558405633832199709)
            ·
              refine ⟨51486629459402112687074891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137297678558405633832199709 51486629459402112687074891)
              ·
                refine ⟨77229944189103169030612337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51486629459402112687074891 77229944189103169030612337)
                ·
                  refine ⟨57922458141827376772959253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77229944189103169030612337 57922458141827376772959253)
                  ·
                    refine ⟨2715115225398158286232465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57922458141827376772959253 2715115225398158286232465)
                    ·
                      refine ⟨2036336419048618714674349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715115225398158286232465 2036336419048618714674349)
                      ·
                        rfl

theorem cell23_3965751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_3965751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965751 prefixEnd_3965751 := by exact prefixLift 3965751
  have htrace : WordTrace (prefixWord ++ tailWord_3965751) baseStart_3965751 baseEnd_3965751 := by
    simpa [prefixWord, tailWord_3965751, baseEnd_3965751] using wordTrace_append hprefix tailTrace_3965751
  have hstable : (prefixWord ++ tailWord_3965751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965751).length < 2 ^ (prefixWord ++ tailWord_3965751).sum := by decide
  have hdescent : baseEnd_3965751 < baseStart_3965751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965778 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3965778 : Nat := 118140960795 + 3965778 * 2 ^ 59
def prefixEnd_3965778 : Nat := 4983230072969 + 3 ^ 40 * 3965778 * 2
def baseEnd_3965778 : Nat := 678783427675430036345575

theorem tailTrace_3965778 : CollatzResearch.WordTrace tailWord_3965778 prefixEnd_3965778 678783427675430036345575 := by
  unfold tailWord_3965778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36160951656667770451206497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96429204417780721203217325 36160951656667770451206497)
  ·
    refine ⟨27120713742500827838404873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36160951656667770451206497 27120713742500827838404873)
    ·
      refine ⟨20340535306875620878803655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27120713742500827838404873 20340535306875620878803655)
      ·
        refine ⟨30510802960313431318205483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20340535306875620878803655 30510802960313431318205483)
        ·
          refine ⟨45766204440470146977308225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30510802960313431318205483 45766204440470146977308225)
          ·
            refine ⟨34324653330352610232981169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45766204440470146977308225 34324653330352610232981169)
            ·
              refine ⟨25743489997764457674735877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34324653330352610232981169 25743489997764457674735877)
              ·
                refine ⟨4826904374580835814012977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25743489997764457674735877 4826904374580835814012977)
                ·
                  refine ⟨3620178280935626860509733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4826904374580835814012977 3620178280935626860509733)
                  ·
                    refine ⟨678783427675430036345575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3620178280935626860509733 678783427675430036345575)
                    ·
                      rfl

theorem cell23_3965778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3965778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965778 prefixEnd_3965778 := by exact prefixLift 3965778
  have htrace : WordTrace (prefixWord ++ tailWord_3965778) baseStart_3965778 baseEnd_3965778 := by
    simpa [prefixWord, tailWord_3965778, baseEnd_3965778] using wordTrace_append hprefix tailTrace_3965778
  have hstable : (prefixWord ++ tailWord_3965778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965778).length < 2 ^ (prefixWord ++ tailWord_3965778).sum := by decide
  have hdescent : baseEnd_3965778 < baseStart_3965778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965785 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 3, 2, 2]
def baseStart_3965785 : Nat := 118140960795 + 3965785 * 2 ^ 59
def prefixEnd_3965785 : Nat := 4983230072969 + 3 ^ 40 * 3965785 * 2
def baseEnd_3965785 : Nat := 2036353877390871581649193

theorem tailTrace_3965785 : CollatzResearch.WordTrace tailWord_3965785 prefixEnd_3965785 2036353877390871581649193 := by
  unfold tailWord_3965785
  simp only [CollatzResearch.WordTrace]
  refine ⟨144644061937645722000330809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96429374625097148000220539 144644061937645722000330809)
  ·
    refine ⟨108483046453234291500248107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144644061937645722000330809 108483046453234291500248107)
    ·
      refine ⟨162724569679851437250372161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108483046453234291500248107 162724569679851437250372161)
      ·
        refine ⟨122043427259888577937779121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162724569679851437250372161 122043427259888577937779121)
        ·
          refine ⟨91532570444916433453334341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122043427259888577937779121 91532570444916433453334341)
          ·
            refine ⟨17162356958421831272500189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91532570444916433453334341 17162356958421831272500189)
            ·
              refine ⟨6435883859408186727187571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17162356958421831272500189 6435883859408186727187571)
              ·
                refine ⟨9653825789112280090781357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435883859408186727187571 9653825789112280090781357)
                ·
                  refine ⟨3620184670917105034043009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9653825789112280090781357 3620184670917105034043009)
                  ·
                    refine ⟨2715138503187828775532257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3620184670917105034043009 2715138503187828775532257)
                    ·
                      refine ⟨2036353877390871581649193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715138503187828775532257 2036353877390871581649193)
                      ·
                        rfl

theorem cell23_3965785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_3965785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965785 prefixEnd_3965785 := by exact prefixLift 3965785
  have htrace : WordTrace (prefixWord ++ tailWord_3965785) baseStart_3965785 baseEnd_3965785 := by
    simpa [prefixWord, tailWord_3965785, baseEnd_3965785] using wordTrace_append hprefix tailTrace_3965785
  have hstable : (prefixWord ++ tailWord_3965785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965785).length < 2 ^ (prefixWord ++ tailWord_3965785).sum := by decide
  have hdescent : baseEnd_3965785 < baseStart_3965785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965788 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3965788 : Nat := 118140960795 + 3965788 * 2 ^ 59
def prefixEnd_3965788 : Nat := 4983230072969 + 3 ^ 40 * 3965788 * 2
def baseEnd_3965788 : Nat := 2036355417832835069911679

theorem tailTrace_3965788 : CollatzResearch.WordTrace tailWord_3965788 prefixEnd_3965788 2036355417832835069911679 := by
  unfold tailWord_3965788
  simp only [CollatzResearch.WordTrace]
  refine ⟨72322085678317426756345009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96429447571089902341793345 72322085678317426756345009)
  ·
    refine ⟨54241564258738070067258757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72322085678317426756345009 54241564258738070067258757)
    ·
      refine ⟨10170293298513388137611017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54241564258738070067258757 10170293298513388137611017)
      ·
        refine ⟨7627719973885041103208263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10170293298513388137611017 7627719973885041103208263)
        ·
          refine ⟨11441579960827561654812395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627719973885041103208263 11441579960827561654812395)
          ·
            refine ⟨17162369941241342482218593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441579960827561654812395 17162369941241342482218593)
            ·
              refine ⟨12871777455931006861663945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17162369941241342482218593 12871777455931006861663945)
              ·
                refine ⟨9653833091948255146247959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12871777455931006861663945 9653833091948255146247959)
                ·
                  refine ⟨14480749637922382719371939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9653833091948255146247959 14480749637922382719371939)
                  ·
                    refine ⟨21721124456883574079057909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14480749637922382719371939 21721124456883574079057909)
                    ·
                      refine ⟨2036355417832835069911679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21721124456883574079057909 2036355417832835069911679)
                      ·
                        rfl

theorem cell23_3965788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3965788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965788 prefixEnd_3965788 := by exact prefixLift 3965788
  have htrace : WordTrace (prefixWord ++ tailWord_3965788) baseStart_3965788 baseEnd_3965788 := by
    simpa [prefixWord, tailWord_3965788, baseEnd_3965788] using wordTrace_append hprefix tailTrace_3965788
  have hstable : (prefixWord ++ tailWord_3965788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965788).length < 2 ^ (prefixWord ++ tailWord_3965788).sum := by decide
  have hdescent : baseEnd_3965788 < baseStart_3965788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965795 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 2, 4]
def baseStart_3965795 : Nat := 118140960795 + 3965795 * 2 ^ 59
def prefixEnd_3965795 : Nat := 4983230072969 + 3 ^ 40 * 3965795 * 2
def baseEnd_3965795 : Nat := 678786337399138847508049

theorem tailTrace_3965795 : CollatzResearch.WordTrace tailWord_3965795 prefixEnd_3965795 678786337399138847508049 := by
  unfold tailWord_3965795
  simp only [CollatzResearch.WordTrace]
  refine ⟨144644426667609493708194839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96429617778406329138796559 144644426667609493708194839)
  ·
    refine ⟨216966640001414240562292259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144644426667609493708194839 216966640001414240562292259)
    ·
      refine ⟨325449960002121360843438389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216966640001414240562292259 325449960002121360843438389)
      ·
        refine ⟨30510933750198877579072349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325449960002121360843438389 30510933750198877579072349)
        ·
          refine ⟨11441600156324579092152131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30510933750198877579072349 11441600156324579092152131)
          ·
            refine ⟨17162400234486868638228197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441600156324579092152131 17162400234486868638228197)
            ·
              refine ⟨3217950043966287869667787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17162400234486868638228197 3217950043966287869667787)
              ·
                refine ⟨4826925065949431804501681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217950043966287869667787 4826925065949431804501681)
                ·
                  refine ⟨3620193799462073853376261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4826925065949431804501681 3620193799462073853376261)
                  ·
                    refine ⟨678786337399138847508049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3620193799462073853376261 678786337399138847508049)
                    ·
                      rfl

theorem cell23_3965795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 4].length) (baseStart_3965795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965795 prefixEnd_3965795 := by exact prefixLift 3965795
  have htrace : WordTrace (prefixWord ++ tailWord_3965795) baseStart_3965795 baseEnd_3965795 := by
    simpa [prefixWord, tailWord_3965795, baseEnd_3965795] using wordTrace_append hprefix tailTrace_3965795
  have hstable : (prefixWord ++ tailWord_3965795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965795).length < 2 ^ (prefixWord ++ tailWord_3965795).sum := by decide
  have hdescent : baseEnd_3965795 < baseStart_3965795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965822 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3965822 : Nat := 118140960795 + 3965822 * 2 ^ 59
def prefixEnd_3965822 : Nat := 4983230072969 + 3 ^ 40 * 3965822 * 2
def baseEnd_3965822 : Nat := 2036372876175087936886523

theorem tailTrace_3965822 : CollatzResearch.WordTrace tailWord_3965822 prefixEnd_3965822 2036372876175087936886523 := by
  unfold tailWord_3965822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18080676429813959664928465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96430274292341118212951813 18080676429813959664928465)
  ·
    refine ⟨13560507322360469748696349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18080676429813959664928465 13560507322360469748696349)
    ·
      refine ⟨5085190245885176155761131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13560507322360469748696349 5085190245885176155761131)
      ·
        refine ⟨7627785368827764233641697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085190245885176155761131 7627785368827764233641697)
        ·
          refine ⟨5720839026620823175231273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7627785368827764233641697 5720839026620823175231273)
          ·
            refine ⟨4290629269965617381423455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5720839026620823175231273 4290629269965617381423455)
            ·
              refine ⟨6435943904948426072135183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290629269965617381423455 6435943904948426072135183)
              ·
                refine ⟨9653915857422639108202775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435943904948426072135183 9653915857422639108202775)
                ·
                  refine ⟨14480873786133958662304163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9653915857422639108202775 14480873786133958662304163)
                  ·
                    refine ⟨21721310679200937993456245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14480873786133958662304163 21721310679200937993456245)
                    ·
                      refine ⟨2036372876175087936886523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21721310679200937993456245 2036372876175087936886523)
                      ·
                        rfl

theorem cell23_3965822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3965822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965822 prefixEnd_3965822 := by exact prefixLift 3965822
  have htrace : WordTrace (prefixWord ++ tailWord_3965822) baseStart_3965822 baseEnd_3965822 := by
    simpa [prefixWord, tailWord_3965822, baseEnd_3965822] using wordTrace_append hprefix tailTrace_3965822
  have hstable : (prefixWord ++ tailWord_3965822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965822).length < 2 ^ (prefixWord ++ tailWord_3965822).sum := by decide
  have hdescent : baseEnd_3965822 < baseStart_3965822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965891 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 3]
def baseStart_3965891 : Nat := 118140960795 + 3965891 * 2 ^ 59
def prefixEnd_3965891 : Nat := 4983230072969 + 3 ^ 40 * 3965891 * 2
def baseEnd_3965891 : Nat := 2036408306340248166923705

theorem tailTrace_3965891 : CollatzResearch.WordTrace tailWord_3965891 prefixEnd_3965891 2036408306340248166923705 := by
  unfold tailWord_3965891
  simp only [CollatzResearch.WordTrace]
  refine ⟨144647928075261702103689527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96431952050174468069126351 144647928075261702103689527)
  ·
    refine ⟨216971892112892553155534291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144647928075261702103689527 216971892112892553155534291)
    ·
      refine ⟨325457838169338829733301437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216971892112892553155534291 325457838169338829733301437)
      ·
        refine ⟨122046689313502061149988039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325457838169338829733301437 122046689313502061149988039)
        ·
          refine ⟨183070033970253091724982059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122046689313502061149988039 183070033970253091724982059)
          ·
            refine ⟨274605050955379637587473089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183070033970253091724982059 274605050955379637587473089)
            ·
              refine ⟨205953788216534728190604817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274605050955379637587473089 205953788216534728190604817)
              ·
                refine ⟨154465341162401046142953613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205953788216534728190604817 154465341162401046142953613)
                ·
                  refine ⟨57924502935900392303607605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154465341162401046142953613 57924502935900392303607605)
                  ·
                    refine ⟨5430422150240661778463213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57924502935900392303607605 5430422150240661778463213)
                    ·
                      refine ⟨2036408306340248166923705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430422150240661778463213 2036408306340248166923705)
                      ·
                        rfl

theorem cell23_3965891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_3965891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965891 prefixEnd_3965891 := by exact prefixLift 3965891
  have htrace : WordTrace (prefixWord ++ tailWord_3965891) baseStart_3965891 baseEnd_3965891 := by
    simpa [prefixWord, tailWord_3965891, baseEnd_3965891] using wordTrace_append hprefix tailTrace_3965891
  have hstable : (prefixWord ++ tailWord_3965891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965891).length < 2 ^ (prefixWord ++ tailWord_3965891).sum := by decide
  have hdescent : baseEnd_3965891 < baseStart_3965891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965909 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3965909 : Nat := 118140960795 + 3965909 * 2 ^ 59
def prefixEnd_3965909 : Nat := 4983230072969 + 3 ^ 40 * 3965909 * 2
def baseEnd_3965909 : Nat := 2036417548992029096498623

theorem tailTrace_3965909 : CollatzResearch.WordTrace tailWord_3965909 prefixEnd_3965909 2036417548992029096498623 := by
  unfold tailWord_3965909
  simp only [CollatzResearch.WordTrace]
  refine ⟨144648584589196491177844781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96432389726130994118563187 144648584589196491177844781)
  ·
    refine ⟨54243219220948684191691793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144648584589196491177844781 54243219220948684191691793)
    ·
      refine ⟨40682414415711513143768845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54243219220948684191691793 40682414415711513143768845)
      ·
        refine ⟨15255905405891817428913317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40682414415711513143768845 15255905405891817428913317)
        ·
          refine ⟨2860482263604715767921247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15255905405891817428913317 2860482263604715767921247)
          ·
            refine ⟨4290723395407073651881871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860482263604715767921247 4290723395407073651881871)
            ·
              refine ⟨6436085093110610477822807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290723395407073651881871 6436085093110610477822807)
              ·
                refine ⟨9654127639665915716734211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436085093110610477822807 9654127639665915716734211)
                ·
                  refine ⟨14481191459498873575101317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9654127639665915716734211 14481191459498873575101317)
                  ·
                    refine ⟨2715223398656038795331497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14481191459498873575101317 2715223398656038795331497)
                    ·
                      refine ⟨2036417548992029096498623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715223398656038795331497 2036417548992029096498623)
                      ·
                        rfl

theorem cell23_3965909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3965909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965909 prefixEnd_3965909 := by exact prefixLift 3965909
  have htrace : WordTrace (prefixWord ++ tailWord_3965909) baseStart_3965909 baseEnd_3965909 := by
    simpa [prefixWord, tailWord_3965909, baseEnd_3965909] using wordTrace_append hprefix tailTrace_3965909
  have hstable : (prefixWord ++ tailWord_3965909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965909).length < 2 ^ (prefixWord ++ tailWord_3965909).sum := by decide
  have hdescent : baseEnd_3965909 < baseStart_3965909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965911 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 6, 5]
def baseStart_3965911 : Nat := 118140960795 + 3965911 * 2 ^ 59
def prefixEnd_3965911 : Nat := 4983230072969 + 3 ^ 40 * 3965911 * 2
def baseEnd_3965911 : Nat := 678806191984446029557871

theorem tailTrace_3965911 : CollatzResearch.WordTrace tailWord_3965911 prefixEnd_3965911 678806191984446029557871 := by
  unfold tailWord_3965911
  simp only [CollatzResearch.WordTrace]
  refine ⟨144648657535189245519417587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96432438356792830346278391 144648657535189245519417587)
  ·
    refine ⟨216972986302783868279126381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144648657535189245519417587 216972986302783868279126381)
    ·
      refine ⟨81364869863543950604672393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216972986302783868279126381 81364869863543950604672393)
      ·
        refine ⟨61023652397657962953504295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81364869863543950604672393 61023652397657962953504295)
        ·
          refine ⟨91535478596486944430256443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61023652397657962953504295 91535478596486944430256443)
          ·
            refine ⟨137303217894730416645384665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91535478596486944430256443 137303217894730416645384665)
            ·
              refine ⟨102977413421047812484038499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137303217894730416645384665 102977413421047812484038499)
              ·
                refine ⟨154466120131571718726057749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102977413421047812484038499 154466120131571718726057749)
                ·
                  refine ⟨7240599381167424315283957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154466120131571718726057749 7240599381167424315283957)
                  ·
                    refine ⟨678806191984446029557871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7240599381167424315283957 678806191984446029557871)
                    ·
                      rfl

theorem cell23_3965911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_3965911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965911 prefixEnd_3965911 := by exact prefixLift 3965911
  have htrace : WordTrace (prefixWord ++ tailWord_3965911) baseStart_3965911 baseEnd_3965911 := by
    simpa [prefixWord, tailWord_3965911, baseEnd_3965911] using wordTrace_append hprefix tailTrace_3965911
  have hstable : (prefixWord ++ tailWord_3965911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965911).length < 2 ^ (prefixWord ++ tailWord_3965911).sum := by decide
  have hdescent : baseEnd_3965911 < baseStart_3965911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965921 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3965921 : Nat := 118140960795 + 3965921 * 2 ^ 59
def prefixEnd_3965921 : Nat := 4983230072969 + 3 ^ 40 * 3965921 * 2
def baseEnd_3965921 : Nat := 2036423710759883049548567

theorem tailTrace_3965921 : CollatzResearch.WordTrace tailWord_3965921 prefixEnd_3965921 2036423710759883049548567 := by
  unfold tailWord_3965921
  simp only [CollatzResearch.WordTrace]
  refine ⟨144649022265153017227281617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96432681510102011484854411 144649022265153017227281617)
  ·
    refine ⟨108486766698864762920461213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144649022265153017227281617 108486766698864762920461213)
    ·
      refine ⟨40682537512074286095172955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108486766698864762920461213 40682537512074286095172955)
      ·
        refine ⟨61023806268111429142759433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40682537512074286095172955 61023806268111429142759433)
        ·
          refine ⟨45767854701083571857069575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61023806268111429142759433 45767854701083571857069575)
          ·
            refine ⟨68651782051625357785604363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45767854701083571857069575 68651782051625357785604363)
            ·
              refine ⟨102977673077438036678406545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68651782051625357785604363 102977673077438036678406545)
              ·
                refine ⟨77233254808078527508804909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102977673077438036678406545 77233254808078527508804909)
                ·
                  refine ⟨28962470553029447815801841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77233254808078527508804909 28962470553029447815801841)
                  ·
                    refine ⟨21721852914772085861851381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28962470553029447815801841 21721852914772085861851381)
                    ·
                      refine ⟨2036423710759883049548567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21721852914772085861851381 2036423710759883049548567)
                      ·
                        rfl

theorem cell23_3965921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3965921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965921 prefixEnd_3965921 := by exact prefixLift 3965921
  have htrace : WordTrace (prefixWord ++ tailWord_3965921) baseStart_3965921 baseEnd_3965921 := by
    simpa [prefixWord, tailWord_3965921, baseEnd_3965921] using wordTrace_append hprefix tailTrace_3965921
  have hstable : (prefixWord ++ tailWord_3965921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965921).length < 2 ^ (prefixWord ++ tailWord_3965921).sum := by decide
  have hdescent : baseEnd_3965921 < baseStart_3965921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965948 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_3965948 : Nat := 118140960795 + 3965948 * 2 ^ 59
def prefixEnd_3965948 : Nat := 4983230072969 + 3 ^ 40 * 3965948 * 2
def baseEnd_3965948 : Nat := 2036437574737554443910943

theorem tailTrace_3965948 : CollatzResearch.WordTrace tailWord_3965948 prefixEnd_3965948 2036437574737554443910943 := by
  unfold tailWord_3965948
  simp only [CollatzResearch.WordTrace]
  refine ⟨72325003518027600419257249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96433338024036800559009665 72325003518027600419257249)
  ·
    refine ⟨54243752638520700314442937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72325003518027600419257249 54243752638520700314442937)
    ·
      refine ⟨40682814478890525235832203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54243752638520700314442937 40682814478890525235832203)
      ·
        refine ⟨61024221718335787853748305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40682814478890525235832203 61024221718335787853748305)
        ·
          refine ⟨45768166288751840890311229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61024221718335787853748305 45768166288751840890311229)
          ·
            refine ⟨17163062358281940333866711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45768166288751840890311229 17163062358281940333866711)
            ·
              refine ⟨25744593537422910500800067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17163062358281940333866711 25744593537422910500800067)
              ·
                refine ⟨38616890306134365751200101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25744593537422910500800067 38616890306134365751200101)
                ·
                  refine ⟨7240666932400193578350019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38616890306134365751200101 7240666932400193578350019)
                  ·
                    refine ⟨10861000398600290367525029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7240666932400193578350019 10861000398600290367525029)
                    ·
                      refine ⟨2036437574737554443910943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10861000398600290367525029 2036437574737554443910943)
                      ·
                        rfl

theorem cell23_3965948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_3965948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965948 prefixEnd_3965948 := by exact prefixLift 3965948
  have htrace : WordTrace (prefixWord ++ tailWord_3965948) baseStart_3965948 baseEnd_3965948 := by
    simpa [prefixWord, tailWord_3965948, baseEnd_3965948] using wordTrace_append hprefix tailTrace_3965948
  have hstable : (prefixWord ++ tailWord_3965948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965948).length < 2 ^ (prefixWord ++ tailWord_3965948).sum := by decide
  have hdescent : baseEnd_3965948 < baseStart_3965948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965961 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_3965961 : Nat := 118140960795 + 3965961 * 2 ^ 59
def prefixEnd_3965961 : Nat := 4983230072969 + 3 ^ 40 * 3965961 * 2
def baseEnd_3965961 : Nat := 2036444249986062893048383

theorem tailTrace_3965961 : CollatzResearch.WordTrace tailWord_3965961 prefixEnd_3965961 2036444249986062893048383 := by
  unfold tailWord_3965961
  simp only [CollatzResearch.WordTrace]
  refine ⟨144650481185008104058737737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96433654123338736039158491 144650481185008104058737737)
  ·
    refine ⟨108487860888756078044053303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144650481185008104058737737 108487860888756078044053303)
    ·
      refine ⟨162731791333134117066079955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108487860888756078044053303 162731791333134117066079955)
      ·
        refine ⟨244097686999701175599119933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162731791333134117066079955 244097686999701175599119933)
        ·
          refine ⟨91536632624887940849669975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244097686999701175599119933 91536632624887940849669975)
          ·
            refine ⟨137304948937331911274504963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91536632624887940849669975 137304948937331911274504963)
            ·
              refine ⟨205957423405997866911757445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137304948937331911274504963 205957423405997866911757445)
              ·
                refine ⟨38617016888624600045954521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205957423405997866911757445 38617016888624600045954521)
                ·
                  refine ⟨28962762666468450034465891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38617016888624600045954521 28962762666468450034465891)
                  ·
                    refine ⟨43444143999702675051698837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28962762666468450034465891 43444143999702675051698837)
                    ·
                      refine ⟨2036444249986062893048383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43444143999702675051698837 2036444249986062893048383)
                      ·
                        rfl

theorem cell23_3965961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_3965961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965961 prefixEnd_3965961 := by exact prefixLift 3965961
  have htrace : WordTrace (prefixWord ++ tailWord_3965961) baseStart_3965961 baseEnd_3965961 := by
    simpa [prefixWord, tailWord_3965961, baseEnd_3965961] using wordTrace_append hprefix tailTrace_3965961
  have hstable : (prefixWord ++ tailWord_3965961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965961).length < 2 ^ (prefixWord ++ tailWord_3965961).sum := by decide
  have hdescent : baseEnd_3965961 < baseStart_3965961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965985 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3965985 : Nat := 118140960795 + 3965985 * 2 ^ 59
def prefixEnd_3965985 : Nat := 4983230072969 + 3 ^ 40 * 3965985 * 2
def baseEnd_3965985 : Nat := 2036456573521770799148273

theorem tailTrace_3965985 : CollatzResearch.WordTrace tailWord_3965985 prefixEnd_3965985 2036456573521770799148273 := by
  unfold tailWord_3965985
  simp only [CollatzResearch.WordTrace]
  refine ⟨144651356536921156157611409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96434237691280770771740939 144651356536921156157611409)
  ·
    refine ⟨108488517402690867118208557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144651356536921156157611409 108488517402690867118208557)
    ·
      refine ⟨40683194026009075169328209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108488517402690867118208557 40683194026009075169328209)
      ·
        refine ⟨30512395519506806376996157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40683194026009075169328209 30512395519506806376996157)
        ·
          refine ⟨11442148319815052391373559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30512395519506806376996157 11442148319815052391373559)
          ·
            refine ⟨17163222479722578587060339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11442148319815052391373559 17163222479722578587060339)
            ·
              refine ⟨25744833719583867880590509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17163222479722578587060339 25744833719583867880590509)
              ·
                refine ⟨9654312644843950455221441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25744833719583867880590509 9654312644843950455221441)
                ·
                  refine ⟨7240734483632962841416081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9654312644843950455221441 7240734483632962841416081)
                  ·
                    refine ⟨5430550862724722131062061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7240734483632962841416081 5430550862724722131062061)
                    ·
                      refine ⟨2036456573521770799148273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430550862724722131062061 2036456573521770799148273)
                      ·
                        rfl

theorem cell23_3965985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3965985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3965985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3965985 prefixEnd_3965985 := by exact prefixLift 3965985
  have htrace : WordTrace (prefixWord ++ tailWord_3965985) baseStart_3965985 baseEnd_3965985 := by
    simpa [prefixWord, tailWord_3965985, baseEnd_3965985] using wordTrace_append hprefix tailTrace_3965985
  have hstable : (prefixWord ++ tailWord_3965985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965985).length < 2 ^ (prefixWord ++ tailWord_3965985).sum := by decide
  have hdescent : baseEnd_3965985 < baseStart_3965985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966009 : List Nat := [1, 2, 1, 5, 2, 1, 4, 2, 1, 4]
def baseStart_3966009 : Nat := 118140960795 + 3966009 * 2 ^ 59
def prefixEnd_3966009 : Nat := 4983230072969 + 3 ^ 40 * 3966009 * 2
def baseEnd_3966009 : Nat := 678822965685826235082721

theorem tailTrace_3966009 : CollatzResearch.WordTrace tailWord_3966009 prefixEnd_3966009 678822965685826235082721 := by
  unfold tailWord_3966009
  simp only [CollatzResearch.WordTrace]
  refine ⟨144652231888834208256485081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96434821259222805504323387 144652231888834208256485081)
  ·
    refine ⟨108489173916625656192363811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144652231888834208256485081 108489173916625656192363811)
    ·
      refine ⟨162733760874938484288545717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108489173916625656192363811 162733760874938484288545717)
      ·
        refine ⟨15256290082025482902051161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162733760874938484288545717 15256290082025482902051161)
        ·
          refine ⟨11442217561519112176538371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15256290082025482902051161 11442217561519112176538371)
          ·
            refine ⟨17163326342278668264807557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11442217561519112176538371 17163326342278668264807557)
            ·
              refine ⟨3218123689177250299651417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17163326342278668264807557 3218123689177250299651417)
              ·
                refine ⟨2413592766882937724738563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218123689177250299651417 2413592766882937724738563)
                ·
                  refine ⟨3620389150324406587107845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413592766882937724738563 3620389150324406587107845)
                  ·
                    refine ⟨678822965685826235082721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3620389150324406587107845 678822965685826235082721)
                    ·
                      rfl

theorem cell23_3966009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 4].length) (baseStart_3966009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966009 prefixEnd_3966009 := by exact prefixLift 3966009
  have htrace : WordTrace (prefixWord ++ tailWord_3966009) baseStart_3966009 baseEnd_3966009 := by
    simpa [prefixWord, tailWord_3966009, baseEnd_3966009] using wordTrace_append hprefix tailTrace_3966009
  have hstable : (prefixWord ++ tailWord_3966009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966009).length < 2 ^ (prefixWord ++ tailWord_3966009).sum := by decide
  have hdescent : baseEnd_3966009 < baseStart_3966009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966011 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7]
def baseStart_3966011 : Nat := 118140960795 + 3966011 * 2 ^ 59
def prefixEnd_3966011 : Nat := 4983230072969 + 3 ^ 40 * 3966011 * 2
def baseEnd_3966011 : Nat := 2036469924018787697423153

theorem tailTrace_3966011 : CollatzResearch.WordTrace tailWord_3966011 prefixEnd_3966011 2036469924018787697423153 := by
  unfold tailWord_3966011
  simp only [CollatzResearch.WordTrace]
  refine ⟨144652304834826962598057887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96434869889884641732038591 144652304834826962598057887)
  ·
    refine ⟨216978457252240443897086831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144652304834826962598057887 216978457252240443897086831)
    ·
      refine ⟨325467685878360665845630247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216978457252240443897086831 325467685878360665845630247)
      ·
        refine ⟨488201528817540998768445371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325467685878360665845630247 488201528817540998768445371)
        ·
          refine ⟨732302293226311498152668057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488201528817540998768445371 732302293226311498152668057)
          ·
            refine ⟨549226719919733623614501043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732302293226311498152668057 549226719919733623614501043)
            ·
              refine ⟨823840079879600435421751565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549226719919733623614501043 823840079879600435421751565)
              ·
                refine ⟨308940029954850163283156837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823840079879600435421751565 308940029954850163283156837)
                ·
                  refine ⟨57926255616534405615591907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308940029954850163283156837 57926255616534405615591907)
                  ·
                    refine ⟨86889383424801608423387861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57926255616534405615591907 86889383424801608423387861)
                    ·
                      refine ⟨2036469924018787697423153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86889383424801608423387861 2036469924018787697423153)
                      ·
                        rfl

theorem cell23_3966011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_3966011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966011 prefixEnd_3966011 := by exact prefixLift 3966011
  have htrace : WordTrace (prefixWord ++ tailWord_3966011) baseStart_3966011 baseEnd_3966011 := by
    simpa [prefixWord, tailWord_3966011, baseEnd_3966011] using wordTrace_append hprefix tailTrace_3966011
  have hstable : (prefixWord ++ tailWord_3966011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966011).length < 2 ^ (prefixWord ++ tailWord_3966011).sum := by decide
  have hdescent : baseEnd_3966011 < baseStart_3966011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966015 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 3]
def baseStart_3966015 : Nat := 118140960795 + 3966015 * 2 ^ 59
def prefixEnd_3966015 : Nat := 4983230072969 + 3 ^ 40 * 3966015 * 2
def baseEnd_3966015 : Nat := 2036471977941405681773135

theorem tailTrace_3966015 : CollatzResearch.WordTrace tailWord_3966015 prefixEnd_3966015 2036471977941405681773135 := by
  unfold tailWord_3966015
  simp only [CollatzResearch.WordTrace]
  refine ⟨144652450726812471281203499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96434967151208314187468999 144652450726812471281203499)
  ·
    refine ⟨216978676090218706921805249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144652450726812471281203499 216978676090218706921805249)
    ·
      refine ⟨162734007067664030191353937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216978676090218706921805249 162734007067664030191353937)
      ·
        refine ⟨122050505300748022643515453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162734007067664030191353937 122050505300748022643515453)
        ·
          refine ⟨45768939487780508491318295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122050505300748022643515453 45768939487780508491318295)
          ·
            refine ⟨68653409231670762736977443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45768939487780508491318295 68653409231670762736977443)
            ·
              refine ⟨102980113847506144105466165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68653409231670762736977443 102980113847506144105466165)
              ·
                refine ⟨9654385673203701009887453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102980113847506144105466165 9654385673203701009887453)
                ·
                  refine ⟨3620394627451387878707795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9654385673203701009887453 3620394627451387878707795)
                  ·
                    refine ⟨5430591941177081818061693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3620394627451387878707795 5430591941177081818061693)
                    ·
                      refine ⟨2036471977941405681773135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430591941177081818061693 2036471977941405681773135)
                      ·
                        rfl

theorem cell23_3966015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_3966015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966015 prefixEnd_3966015 := by exact prefixLift 3966015
  have htrace : WordTrace (prefixWord ++ tailWord_3966015) baseStart_3966015 baseEnd_3966015 := by
    simpa [prefixWord, tailWord_3966015, baseEnd_3966015] using wordTrace_append hprefix tailTrace_3966015
  have hstable : (prefixWord ++ tailWord_3966015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966015).length < 2 ^ (prefixWord ++ tailWord_3966015).sum := by decide
  have hdescent : baseEnd_3966015 < baseStart_3966015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966022 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_3966022 : Nat := 118140960795 + 3966022 * 2 ^ 59
def prefixEnd_3966022 : Nat := 4983230072969 + 3 ^ 40 * 3966022 * 2
def baseEnd_3966022 : Nat := 226275063589554128265067

theorem tailTrace_3966022 : CollatzResearch.WordTrace tailWord_3966022 prefixEnd_3966022 226275063589554128265067 := by
  unfold tailWord_3966022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520397063680847233647135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96435137358524740984472213 4520397063680847233647135)
  ·
    refine ⟨6780595595521270850470703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4520397063680847233647135 6780595595521270850470703)
    ·
      refine ⟨10170893393281906275706055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780595595521270850470703 10170893393281906275706055)
      ·
        refine ⟨15256340089922859413559083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10170893393281906275706055 15256340089922859413559083)
        ·
          refine ⟨22884510134884289120338625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15256340089922859413559083 22884510134884289120338625)
          ·
            refine ⟨17163382601163216840253969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22884510134884289120338625 17163382601163216840253969)
            ·
              refine ⟨12872536950872412630190477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17163382601163216840253969 12872536950872412630190477)
              ·
                refine ⟨4827201356577154736321429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12872536950872412630190477 4827201356577154736321429)
                ·
                  refine ⟨226275063589554128265067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4827201356577154736321429 226275063589554128265067)
                  ·
                    rfl

theorem cell23_3966022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_3966022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966022 prefixEnd_3966022 := by exact prefixLift 3966022
  have htrace : WordTrace (prefixWord ++ tailWord_3966022) baseStart_3966022 baseEnd_3966022 := by
    simpa [prefixWord, tailWord_3966022, baseEnd_3966022] using wordTrace_append hprefix tailTrace_3966022
  have hstable : (prefixWord ++ tailWord_3966022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966022).length < 2 ^ (prefixWord ++ tailWord_3966022).sum := by decide
  have hdescent : baseEnd_3966022 < baseStart_3966022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966048 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 1, 6]
def baseStart_3966048 : Nat := 118140960795 + 3966048 * 2 ^ 59
def prefixEnd_3966048 : Nat := 4983230072969 + 3 ^ 40 * 3966048 * 2
def baseEnd_3966048 : Nat := 678829640934334684220161

theorem tailTrace_3966048 : CollatzResearch.WordTrace tailWord_3966048 prefixEnd_3966048 678829640934334684220161 := by
  unfold tailWord_3966048
  simp only [CollatzResearch.WordTrace]
  refine ⟨72326827167846458958577399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96435769557128611944769865 72326827167846458958577399)
  ·
    refine ⟨108490240751769688437866099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72326827167846458958577399 108490240751769688437866099)
    ·
      refine ⟨162735361127654532656799149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108490240751769688437866099 162735361127654532656799149)
      ·
        refine ⟨61025760422870449746299681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162735361127654532656799149 61025760422870449746299681)
        ·
          refine ⟨45769320317152837309724761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61025760422870449746299681 45769320317152837309724761)
          ·
            refine ⟨34326990237864627982293571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45769320317152837309724761 34326990237864627982293571)
            ·
              refine ⟨51490485356796941973440357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34326990237864627982293571 51490485356796941973440357)
              ·
                refine ⟨9654466004399426620020067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51490485356796941973440357 9654466004399426620020067)
                ·
                  refine ⟨14481699006599139930030101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9654466004399426620020067 14481699006599139930030101)
                  ·
                    refine ⟨678829640934334684220161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14481699006599139930030101 678829640934334684220161)
                    ·
                      rfl

theorem cell23_3966048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_3966048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966048 prefixEnd_3966048 := by exact prefixLift 3966048
  have htrace : WordTrace (prefixWord ++ tailWord_3966048) baseStart_3966048 baseEnd_3966048 := by
    simpa [prefixWord, tailWord_3966048, baseEnd_3966048] using wordTrace_append hprefix tailTrace_3966048
  have hstable : (prefixWord ++ tailWord_3966048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966048).length < 2 ^ (prefixWord ++ tailWord_3966048).sum := by decide
  have hdescent : baseEnd_3966048 < baseStart_3966048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966065 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 2, 4]
def baseStart_3966065 : Nat := 118140960795 + 3966065 * 2 ^ 59
def prefixEnd_3966065 : Nat := 4983230072969 + 3 ^ 40 * 3966065 * 2
def baseEnd_3966065 : Nat := 678832550658043495382635

theorem tailTrace_3966065 : CollatzResearch.WordTrace tailWord_3966065 prefixEnd_3966065 678832550658043495382635 := by
  unfold tailWord_3966065
  simp only [CollatzResearch.WordTrace]
  refine ⟨144654274376631329820523649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96436182917754219880349099 144654274376631329820523649)
  ·
    refine ⟨108490705782473497365392737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144654274376631329820523649 108490705782473497365392737)
    ·
      refine ⟨81368029336855123024044553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108490705782473497365392737 81368029336855123024044553)
      ·
        refine ⟨61026022002641342268033415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81368029336855123024044553 61026022002641342268033415)
        ·
          refine ⟨91539033003962013402050123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61026022002641342268033415 91539033003962013402050123)
          ·
            refine ⟨137308549505943020103075185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91539033003962013402050123 137308549505943020103075185)
            ·
              refine ⟨102981412129457265077306389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137308549505943020103075185 102981412129457265077306389)
              ·
                refine ⟨4827253693568309300498737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102981412129457265077306389 4827253693568309300498737)
                ·
                  refine ⟨3620440270176231975374053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4827253693568309300498737 3620440270176231975374053)
                  ·
                    refine ⟨678832550658043495382635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3620440270176231975374053 678832550658043495382635)
                    ·
                      rfl

theorem cell23_3966065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_3966065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966065 prefixEnd_3966065 := by exact prefixLift 3966065
  have htrace : WordTrace (prefixWord ++ tailWord_3966065) baseStart_3966065 baseEnd_3966065 := by
    simpa [prefixWord, tailWord_3966065, baseEnd_3966065] using wordTrace_append hprefix tailTrace_3966065
  have hstable : (prefixWord ++ tailWord_3966065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966065).length < 2 ^ (prefixWord ++ tailWord_3966065).sum := by decide
  have hdescent : baseEnd_3966065 < baseStart_3966065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966072 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 3, 2, 2]
def baseStart_3966072 : Nat := 118140960795 + 3966072 * 2 ^ 59
def prefixEnd_3966072 : Nat := 4983230072969 + 3 ^ 40 * 3966072 * 2
def baseEnd_3966072 : Nat := 2036501246338711958760373

theorem tailTrace_3966072 : CollatzResearch.WordTrace tailWord_3966072 prefixEnd_3966072 2036501246338711958760373 := by
  unfold tailWord_3966072
  simp only [CollatzResearch.WordTrace]
  refine ⟨72327264843802985008014235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96436353125070646677352313 72327264843802985008014235)
  ·
    refine ⟨108490897265704477512021353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72327264843802985008014235 108490897265704477512021353)
    ·
      refine ⟨81368172949278358134016015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108490897265704477512021353 81368172949278358134016015)
      ·
        refine ⟨122052259423917537201024023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81368172949278358134016015 122052259423917537201024023)
        ·
          refine ⟨183078389135876305801536035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122052259423917537201024023 183078389135876305801536035)
          ·
            refine ⟨274617583703814458702304053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183078389135876305801536035 274617583703814458702304053)
            ·
              refine ⟨25745398472232605503341005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274617583703814458702304053 25745398472232605503341005)
              ·
                refine ⟨9654524427087227063752877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25745398472232605503341005 9654524427087227063752877)
                ·
                  refine ⟨3620446660157710148907329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9654524427087227063752877 3620446660157710148907329)
                  ·
                    refine ⟨2715334995118282611680497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3620446660157710148907329 2715334995118282611680497)
                    ·
                      refine ⟨2036501246338711958760373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715334995118282611680497 2036501246338711958760373)
                      ·
                        rfl

theorem cell23_3966072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_3966072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966072 prefixEnd_3966072 := by exact prefixLift 3966072
  have htrace : WordTrace (prefixWord ++ tailWord_3966072) baseStart_3966072 baseEnd_3966072 := by
    simpa [prefixWord, tailWord_3966072, baseEnd_3966072] using wordTrace_append hprefix tailTrace_3966072
  have hstable : (prefixWord ++ tailWord_3966072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966072).length < 2 ^ (prefixWord ++ tailWord_3966072).sum := by decide
  have hdescent : baseEnd_3966072 < baseStart_3966072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966085 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_3966085 : Nat := 118140960795 + 3966085 * 2 ^ 59
def prefixEnd_3966085 : Nat := 4983230072969 + 3 ^ 40 * 3966085 * 2
def baseEnd_3966085 : Nat := 2036507921587220407897813

theorem tailTrace_3966085 : CollatzResearch.WordTrace tailWord_3966085 prefixEnd_3966085 2036507921587220407897813 := by
  unfold tailWord_3966085
  simp only [CollatzResearch.WordTrace]
  refine ⟨144655003836558873236251709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96436669224372582157501139 144655003836558873236251709)
  ·
    refine ⟨54245626438709577463594391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144655003836558873236251709 54245626438709577463594391)
    ·
      refine ⟨81368439658064366195391587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54245626438709577463594391 81368439658064366195391587)
      ·
        refine ⟨122052659487096549293087381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81368439658064366195391587 122052659487096549293087381)
        ·
          refine ⟨5721218413457650748113471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122052659487096549293087381 5721218413457650748113471)
          ·
            refine ⟨8581827620186476122170207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721218413457650748113471 8581827620186476122170207)
            ·
              refine ⟨12872741430279714183255311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581827620186476122170207 12872741430279714183255311)
              ·
                refine ⟨19309112145419571274882967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12872741430279714183255311 19309112145419571274882967)
                ·
                  refine ⟨28963668218129356912324451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19309112145419571274882967 28963668218129356912324451)
                  ·
                    refine ⟨43445502327194035368486677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28963668218129356912324451 43445502327194035368486677)
                    ·
                      refine ⟨2036507921587220407897813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43445502327194035368486677 2036507921587220407897813)
                      ·
                        rfl

theorem cell23_3966085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_3966085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966085 prefixEnd_3966085 := by exact prefixLift 3966085
  have htrace : WordTrace (prefixWord ++ tailWord_3966085) baseStart_3966085 baseEnd_3966085 := by
    simpa [prefixWord, tailWord_3966085, baseEnd_3966085] using wordTrace_append hprefix tailTrace_3966085
  have hstable : (prefixWord ++ tailWord_3966085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966085).length < 2 ^ (prefixWord ++ tailWord_3966085).sum := by decide
  have hdescent : baseEnd_3966085 < baseStart_3966085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966128 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_3966128 : Nat := 118140960795 + 3966128 * 2 ^ 59
def prefixEnd_3966128 : Nat := 4983230072969 + 3 ^ 40 * 3966128 * 2
def baseEnd_3966128 : Nat := 2036530001255363739660115

theorem tailTrace_3966128 : CollatzResearch.WordTrace tailWord_3966128 prefixEnd_3966128 2036530001255363739660115 := by
  unfold tailWord_3966128
  simp only [CollatzResearch.WordTrace]
  refine ⟨72328286087701545790033519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96437714783602061053378025 72328286087701545790033519)
  ·
    refine ⟨108492429131552318685050279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72328286087701545790033519 108492429131552318685050279)
    ·
      refine ⟨162738643697328478027575419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108492429131552318685050279 162738643697328478027575419)
      ·
        refine ⟨244107965545992717041363129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162738643697328478027575419 244107965545992717041363129)
        ·
          refine ⟨183080974159494537781022347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244107965545992717041363129 183080974159494537781022347)
          ·
            refine ⟨274621461239241806671533521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183080974159494537781022347 274621461239241806671533521)
            ·
              refine ⟨205966095929431355003650141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274621461239241806671533521 205966095929431355003650141)
              ·
                refine ⟨77237285973536758126368803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205966095929431355003650141 77237285973536758126368803)
                ·
                  refine ⟨115855928960305137189553205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77237285973536758126368803 115855928960305137189553205)
                  ·
                    refine ⟨10861493340028606611520613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115855928960305137189553205 10861493340028606611520613)
                    ·
                      refine ⟨2036530001255363739660115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10861493340028606611520613 2036530001255363739660115)
                      ·
                        rfl

theorem cell23_3966128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_3966128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966128 prefixEnd_3966128 := by exact prefixLift 3966128
  have htrace : WordTrace (prefixWord ++ tailWord_3966128) baseStart_3966128 baseEnd_3966128 := by
    simpa [prefixWord, tailWord_3966128, baseEnd_3966128] using wordTrace_append hprefix tailTrace_3966128
  have hstable : (prefixWord ++ tailWord_3966128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966128).length < 2 ^ (prefixWord ++ tailWord_3966128).sum := by decide
  have hdescent : baseEnd_3966128 < baseStart_3966128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966138 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_3966138 : Nat := 118140960795 + 3966138 * 2 ^ 59
def prefixEnd_3966138 : Nat := 4983230072969 + 3 ^ 40 * 3966138 * 2
def baseEnd_3966138 : Nat := 678845045353969566845023

theorem tailTrace_3966138 : CollatzResearch.WordTrace tailWord_3966138 prefixEnd_3966138 678845045353969566845023 := by
  unfold tailWord_3966138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36164234226341715821982767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96437957936911242191954045 36164234226341715821982767)
  ·
    refine ⟨54246351339512573732974151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36164234226341715821982767 54246351339512573732974151)
    ·
      refine ⟨81369527009268860599461227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54246351339512573732974151 81369527009268860599461227)
      ·
        refine ⟨122054290513903290899191841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81369527009268860599461227 122054290513903290899191841)
        ·
          refine ⟨91540717885427468174393881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122054290513903290899191841 91540717885427468174393881)
          ·
            refine ⟨68655538414070601130795411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91540717885427468174393881 68655538414070601130795411)
            ·
              refine ⟨102983307621105901696193117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68655538414070601130795411 102983307621105901696193117)
              ·
                refine ⟨38618740357914713136072419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102983307621105901696193117 38618740357914713136072419)
                ·
                  refine ⟨57928110536872069704108629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38618740357914713136072419 57928110536872069704108629)
                  ·
                    refine ⟨678845045353969566845023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57928110536872069704108629 678845045353969566845023)
                    ·
                      rfl

theorem cell23_3966138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_3966138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966138 prefixEnd_3966138 := by exact prefixLift 3966138
  have htrace : WordTrace (prefixWord ++ tailWord_3966138) baseStart_3966138 baseEnd_3966138 := by
    simpa [prefixWord, tailWord_3966138, baseEnd_3966138] using wordTrace_append hprefix tailTrace_3966138
  have hstable : (prefixWord ++ tailWord_3966138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966138).length < 2 ^ (prefixWord ++ tailWord_3966138).sum := by decide
  have hdescent : baseEnd_3966138 < baseStart_3966138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966195 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 3]
def baseStart_3966195 : Nat := 118140960795 + 3966195 * 2 ^ 59
def prefixEnd_3966195 : Nat := 4983230072969 + 3 ^ 40 * 3966195 * 2
def baseEnd_3966195 : Nat := 2036564404459214977522307

theorem tailTrace_3966195 : CollatzResearch.WordTrace tailWord_3966195 prefixEnd_3966195 2036564404459214977522307 := by
  unfold tailWord_3966195
  simp only [CollatzResearch.WordTrace]
  refine ⟨144659015866160362022756039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96439343910773574681837359 144659015866160362022756039)
  ·
    refine ⟨216988523799240543034134059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144659015866160362022756039 216988523799240543034134059)
    ·
      refine ⟨325482785698860814551201089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216988523799240543034134059 325482785698860814551201089)
      ·
        refine ⟨244112089274145610913400817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325482785698860814551201089 244112089274145610913400817)
        ·
          refine ⟨183084066955609208185050613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244112089274145610913400817 183084066955609208185050613)
          ·
            refine ⟨17164131277088363267348495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183084066955609208185050613 17164131277088363267348495)
            ·
              refine ⟨25746196915632544901022743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17164131277088363267348495 25746196915632544901022743)
              ·
                refine ⟨38619295373448817351534115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25746196915632544901022743 38619295373448817351534115)
                ·
                  refine ⟨57928943060173226027301173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38619295373448817351534115 57928943060173226027301173)
                  ·
                    refine ⟨5430838411891239940059485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57928943060173226027301173 5430838411891239940059485)
                    ·
                      refine ⟨2036564404459214977522307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430838411891239940059485 2036564404459214977522307)
                      ·
                        rfl

theorem cell23_3966195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_3966195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966195 prefixEnd_3966195 := by exact prefixLift 3966195
  have htrace : WordTrace (prefixWord ++ tailWord_3966195) baseStart_3966195 baseEnd_3966195 := by
    simpa [prefixWord, tailWord_3966195, baseEnd_3966195] using wordTrace_append hprefix tailTrace_3966195
  have hstable : (prefixWord ++ tailWord_3966195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966195).length < 2 ^ (prefixWord ++ tailWord_3966195).sum := by decide
  have hdescent : baseEnd_3966195 < baseStart_3966195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966235 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 4]
def baseStart_3966235 : Nat := 118140960795 + 3966235 * 2 ^ 59
def prefixEnd_3966235 : Nat := 4983230072969 + 3 ^ 40 * 3966235 * 2
def baseEnd_3966235 : Nat := 2036584943685394821022123

theorem tailTrace_3966235 : CollatzResearch.WordTrace tailWord_3966235 prefixEnd_3966235 2036584943685394821022123 := by
  unfold tailWord_3966235
  simp only [CollatzResearch.WordTrace]
  refine ⟨144660474786015448854212159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96440316524010299236141439 144660474786015448854212159)
  ·
    refine ⟨216990712179023173281318239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144660474786015448854212159 216990712179023173281318239)
    ·
      refine ⟨325486068268534759921977359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216990712179023173281318239 325486068268534759921977359)
      ·
        refine ⟨488229102402802139882966039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325486068268534759921977359 488229102402802139882966039)
        ·
          refine ⟨732343653604203209824449059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488229102402802139882966039 732343653604203209824449059)
          ·
            refine ⟨1098515480406304814736673589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732343653604203209824449059 1098515480406304814736673589)
            ·
              refine ⟨102985826288091076381563149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1098515480406304814736673589 102985826288091076381563149)
              ·
                refine ⟨38619684858034153643086181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102985826288091076381563149 38619684858034153643086181)
                ·
                  refine ⟨7241190910881403808078659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38619684858034153643086181 7241190910881403808078659)
                  ·
                    refine ⟨10861786366322105712117989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7241190910881403808078659 10861786366322105712117989)
                    ·
                      refine ⟨2036584943685394821022123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10861786366322105712117989 2036584943685394821022123)
                      ·
                        rfl

theorem cell23_3966235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 4].length) (baseStart_3966235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966235 prefixEnd_3966235 := by exact prefixLift 3966235
  have htrace : WordTrace (prefixWord ++ tailWord_3966235) baseStart_3966235 baseEnd_3966235 := by
    simpa [prefixWord, tailWord_3966235, baseEnd_3966235] using wordTrace_append hprefix tailTrace_3966235
  have hstable : (prefixWord ++ tailWord_3966235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966235).length < 2 ^ (prefixWord ++ tailWord_3966235).sum := by decide
  have hdescent : baseEnd_3966235 < baseStart_3966235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966272 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3]
def baseStart_3966272 : Nat := 118140960795 + 3966272 * 2 ^ 59
def prefixEnd_3966272 : Nat := 4983230072969 + 3 ^ 40 * 3966272 * 2
def baseEnd_3966272 : Nat := 2036603942469611176259453

theorem tailTrace_3966272 : CollatzResearch.WordTrace tailWord_3966272 prefixEnd_3966272 2036603942469611176259453 := by
  unfold tailWord_3966272
  simp only [CollatzResearch.WordTrace]
  refine ⟨72330912143440702086654535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96441216191254269448872713 72330912143440702086654535)
  ·
    refine ⟨108496368215161053129981803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72330912143440702086654535 108496368215161053129981803)
    ·
      refine ⟨162744552322741579694972705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108496368215161053129981803 162744552322741579694972705)
      ·
        refine ⟨122058414242056184771229529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162744552322741579694972705 122058414242056184771229529)
        ·
          refine ⟨91543810681542138578422147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122058414242056184771229529 91543810681542138578422147)
          ·
            refine ⟨137315716022313207867633221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91543810681542138578422147 137315716022313207867633221)
            ·
              refine ⟨25746696754183726475181229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137315716022313207867633221 25746696754183726475181229)
              ·
                refine ⟨9655011282818897428192961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25746696754183726475181229 9655011282818897428192961)
                ·
                  refine ⟨7241258462114173071144721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9655011282818897428192961 7241258462114173071144721)
                  ·
                    refine ⟨5430943846585629803358541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7241258462114173071144721 5430943846585629803358541)
                    ·
                      refine ⟨2036603942469611176259453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5430943846585629803358541 2036603942469611176259453)
                      ·
                        rfl

theorem cell23_3966272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_3966272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966272 prefixEnd_3966272 := by exact prefixLift 3966272
  have htrace : WordTrace (prefixWord ++ tailWord_3966272) baseStart_3966272 baseEnd_3966272 := by
    simpa [prefixWord, tailWord_3966272, baseEnd_3966272] using wordTrace_append hprefix tailTrace_3966272
  have hstable : (prefixWord ++ tailWord_3966272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966272).length < 2 ^ (prefixWord ++ tailWord_3966272).sum := by decide
  have hdescent : baseEnd_3966272 < baseStart_3966272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966292 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 6]
def baseStart_3966292 : Nat := 118140960795 + 3966292 * 2 ^ 59
def prefixEnd_3966292 : Nat := 4983230072969 + 3 ^ 40 * 3966292 * 2
def baseEnd_3966292 : Nat := 226290468009189010889929

theorem tailTrace_3966292 : CollatzResearch.WordTrace tailWord_3966292 prefixEnd_3966292 226290468009189010889929 := by
  unfold tailWord_3966292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72331276873404473794518565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96441702497872631726024753 72331276873404473794518565)
  ·
    refine ⟨13562114413763338836472231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72331276873404473794518565 13562114413763338836472231)
    ·
      refine ⟨20343171620645008254708347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13562114413763338836472231 20343171620645008254708347)
      ·
        refine ⟨30514757430967512382062521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20343171620645008254708347 30514757430967512382062521)
        ·
          refine ⟨22886068073225634286546891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30514757430967512382062521 22886068073225634286546891)
          ·
            refine ⟨34329102109838451429820337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22886068073225634286546891 34329102109838451429820337)
            ·
              refine ⟨25746826582378838572365253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34329102109838451429820337 25746826582378838572365253)
              ·
                refine ⟨4827529984196032232318485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25746826582378838572365253 4827529984196032232318485)
                ·
                  refine ⟨226290468009189010889929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4827529984196032232318485 226290468009189010889929)
                  ·
                    rfl

theorem cell23_3966292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_3966292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966292 prefixEnd_3966292 := by exact prefixLift 3966292
  have htrace : WordTrace (prefixWord ++ tailWord_3966292) baseStart_3966292 baseEnd_3966292 := by
    simpa [prefixWord, tailWord_3966292, baseEnd_3966292] using wordTrace_append hprefix tailTrace_3966292
  have hstable : (prefixWord ++ tailWord_3966292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966292).length < 2 ^ (prefixWord ++ tailWord_3966292).sum := by decide
  have hdescent : baseEnd_3966292 < baseStart_3966292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966296 : List Nat := [2, 1, 2, 2, 1, 1, 7, 2, 1, 4]
def baseStart_3966296 : Nat := 118140960795 + 3966296 * 2 ^ 59
def prefixEnd_3966296 : Nat := 4983230072969 + 3 ^ 40 * 3966296 * 2
def baseEnd_3966296 : Nat := 678872088668439694119781

theorem tailTrace_3966296 : CollatzResearch.WordTrace tailWord_3966296 prefixEnd_3966296 678872088668439694119781 := by
  unfold tailWord_3966296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72331349819397228136091371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96441799759196304181455161 72331349819397228136091371)
  ·
    refine ⟨108497024729095842204137057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72331349819397228136091371 108497024729095842204137057)
    ·
      refine ⟨81372768546821881653102793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108497024729095842204137057 81372768546821881653102793)
      ·
        refine ⟨61029576410116411239827095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81372768546821881653102793 61029576410116411239827095)
        ·
          refine ⟨91544364615174616859740643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61029576410116411239827095 91544364615174616859740643)
          ·
            refine ⟨137316546922761925289610965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91544364615174616859740643 137316546922761925289610965)
            ·
              refine ⟨3218356568502232623975257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 137316546922761925289610965 3218356568502232623975257)
              ·
                refine ⟨2413767426376674467981443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218356568502232623975257 2413767426376674467981443)
                ·
                  refine ⟨3620651139565011701972165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413767426376674467981443 3620651139565011701972165)
                  ·
                    refine ⟨678872088668439694119781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3620651139565011701972165 678872088668439694119781)
                    ·
                      rfl

theorem cell23_3966296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_3966296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966296 prefixEnd_3966296 := by exact prefixLift 3966296
  have htrace : WordTrace (prefixWord ++ tailWord_3966296) baseStart_3966296 baseEnd_3966296 := by
    simpa [prefixWord, tailWord_3966296, baseEnd_3966296] using wordTrace_append hprefix tailTrace_3966296
  have hstable : (prefixWord ++ tailWord_3966296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966296).length < 2 ^ (prefixWord ++ tailWord_3966296).sum := by decide
  have hdescent : baseEnd_3966296 < baseStart_3966296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966322 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_3966322 : Nat := 118140960795 + 3966322 * 2 ^ 59
def prefixEnd_3966322 : Nat := 4983230072969 + 3 ^ 40 * 3966322 * 2
def baseEnd_3966322 : Nat := 678876538834111993544741

theorem tailTrace_3966322 : CollatzResearch.WordTrace tailWord_3966322 prefixEnd_3966322 678876538834111993544741 := by
  unfold tailWord_3966322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36165911984175065678157305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96442431957800175141752813 36165911984175065678157305)
  ·
    refine ⟨27124433988131299258617979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36165911984175065678157305 27124433988131299258617979)
    ·
      refine ⟨40686650982196948887926969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27124433988131299258617979 40686650982196948887926969)
      ·
        refine ⟨30514988236647711665945227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40686650982196948887926969 30514988236647711665945227)
        ·
          refine ⟨45772482354971567498917841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30514988236647711665945227 45772482354971567498917841)
          ·
            refine ⟨34329361766228675624188381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45772482354971567498917841 34329361766228675624188381)
            ·
              refine ⟨12873510662335753359070643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34329361766228675624188381 12873510662335753359070643)
              ·
                refine ⟨19310265993503630038605965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12873510662335753359070643 19310265993503630038605965)
                ·
                  refine ⟨7241349747563861264477237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19310265993503630038605965 7241349747563861264477237)
                  ·
                    refine ⟨678876538834111993544741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7241349747563861264477237 678876538834111993544741)
                    ·
                      rfl

theorem cell23_3966322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_3966322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966322 prefixEnd_3966322 := by exact prefixLift 3966322
  have htrace : WordTrace (prefixWord ++ tailWord_3966322) baseStart_3966322 baseEnd_3966322 := by
    simpa [prefixWord, tailWord_3966322, baseEnd_3966322] using wordTrace_append hprefix tailTrace_3966322
  have hstable : (prefixWord ++ tailWord_3966322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966322).length < 2 ^ (prefixWord ++ tailWord_3966322).sum := by decide
  have hdescent : baseEnd_3966322 < baseStart_3966322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966329 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 2, 3, 2]
def baseStart_3966329 : Nat := 118140960795 + 3966329 * 2 ^ 59
def prefixEnd_3966329 : Nat := 4983230072969 + 3 ^ 40 * 3966329 * 2
def baseEnd_3966329 : Nat := 2036633210866917453246691

theorem tailTrace_3966329 : CollatzResearch.WordTrace tailWord_3966329 prefixEnd_3966329 2036633210866917453246691 := by
  unfold tailWord_3966329
  simp only [CollatzResearch.WordTrace]
  refine ⟨144663903247674902908134041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96442602165116601938756027 144663903247674902908134041)
  ·
    refine ⟨108497927435756177181100531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144663903247674902908134041 108497927435756177181100531)
    ·
      refine ⟨162746891153634265771650797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108497927435756177181100531 162746891153634265771650797)
      ·
        refine ⟨61030084182612849664369049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162746891153634265771650797 61030084182612849664369049)
        ·
          refine ⟨45772563136959637248276787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61030084182612849664369049 45772563136959637248276787)
          ·
            refine ⟨68658844705439455872415181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45772563136959637248276787 68658844705439455872415181)
            ·
              refine ⟨25747066764539795952155693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68658844705439455872415181 25747066764539795952155693)
              ·
                refine ⟨9655150036702423482058385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25747066764539795952155693 9655150036702423482058385)
                ·
                  refine ⟨7241362527526817611543789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9655150036702423482058385 7241362527526817611543789)
                  ·
                    refine ⟨2715510947822556604328921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7241362527526817611543789 2715510947822556604328921)
                    ·
                      refine ⟨2036633210866917453246691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715510947822556604328921 2036633210866917453246691)
                      ·
                        rfl

theorem cell23_3966329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_3966329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966329 prefixEnd_3966329 := by exact prefixLift 3966329
  have htrace : WordTrace (prefixWord ++ tailWord_3966329) baseStart_3966329 baseEnd_3966329 := by
    simpa [prefixWord, tailWord_3966329, baseEnd_3966329] using wordTrace_append hprefix tailTrace_3966329
  have hstable : (prefixWord ++ tailWord_3966329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966329).length < 2 ^ (prefixWord ++ tailWord_3966329).sum := by decide
  have hdescent : baseEnd_3966329 < baseStart_3966329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966362 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3966362 : Nat := 118140960795 + 3966362 * 2 ^ 59
def prefixEnd_3966362 : Nat := 4983230072969 + 3 ^ 40 * 3966362 * 2
def baseEnd_3966362 : Nat := 2036650155728515824134039

theorem tailTrace_3966362 : CollatzResearch.WordTrace tailWord_3966362 prefixEnd_3966362 2036650155728515824134039 := by
  unfold tailWord_3966362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36166276714138837386021335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96443404571036899696056893 36166276714138837386021335)
  ·
    refine ⟨54249415071208256079032003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36166276714138837386021335 54249415071208256079032003)
    ·
      refine ⟨81374122606812384118548005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54249415071208256079032003 81374122606812384118548005)
      ·
        refine ⟨15257647988777322022227751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81374122606812384118548005 15257647988777322022227751)
        ·
          refine ⟨22886471983165983033341627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15257647988777322022227751 22886471983165983033341627)
          ·
            refine ⟨34329707974748974550012441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22886471983165983033341627 34329707974748974550012441)
            ·
              refine ⟨25747280981061730912509331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34329707974748974550012441 25747280981061730912509331)
              ·
                refine ⟨38620921471592596368763997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25747280981061730912509331 38620921471592596368763997)
                ·
                  refine ⟨14482845551847223638286499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38620921471592596368763997 14482845551847223638286499)
                  ·
                    refine ⟨21724268327770835457429749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14482845551847223638286499 21724268327770835457429749)
                    ·
                      refine ⟨2036650155728515824134039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21724268327770835457429749 2036650155728515824134039)
                      ·
                        rfl

theorem cell23_3966362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3966362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966362 prefixEnd_3966362 := by exact prefixLift 3966362
  have htrace : WordTrace (prefixWord ++ tailWord_3966362) baseStart_3966362 baseEnd_3966362 := by
    simpa [prefixWord, tailWord_3966362, baseEnd_3966362] using wordTrace_append hprefix tailTrace_3966362
  have hstable : (prefixWord ++ tailWord_3966362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966362).length < 2 ^ (prefixWord ++ tailWord_3966362).sum := by decide
  have hdescent : baseEnd_3966362 < baseStart_3966362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966389 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3966389 : Nat := 118140960795 + 3966389 * 2 ^ 59
def prefixEnd_3966389 : Nat := 4983230072969 + 3 ^ 40 * 3966389 * 2
def baseEnd_3966389 : Nat := 2036664019706187218496415

theorem tailTrace_3966389 : CollatzResearch.WordTrace tailWord_3966389 prefixEnd_3966389 2036664019706187218496415 := by
  unfold tailWord_3966389
  simp only [CollatzResearch.WordTrace]
  refine ⟨144666091627457533155318221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96444061084971688770212147 144666091627457533155318221)
  ·
    refine ⟨54249784360296574933244333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144666091627457533155318221 54249784360296574933244333)
    ·
      refine ⟨20343669135111215599966625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54249784360296574933244333 20343669135111215599966625)
      ·
        refine ⟨15257751851333411699974969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20343669135111215599966625 15257751851333411699974969)
        ·
          refine ⟨11443313888500058774981227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15257751851333411699974969 11443313888500058774981227)
          ·
            refine ⟨17164970832750088162471841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11443313888500058774981227 17164970832750088162471841)
            ·
              refine ⟨12873728124562566121853881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17164970832750088162471841 12873728124562566121853881)
              ·
                refine ⟨9655296093421924591390411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12873728124562566121853881 9655296093421924591390411)
                ·
                  refine ⟨14482944140132886887085617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9655296093421924591390411 14482944140132886887085617)
                  ·
                    refine ⟨10862208105099665165314213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14482944140132886887085617 10862208105099665165314213)
                    ·
                      refine ⟨2036664019706187218496415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10862208105099665165314213 2036664019706187218496415)
                      ·
                        rfl

theorem cell23_3966389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3966389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966389 prefixEnd_3966389 := by exact prefixLift 3966389
  have htrace : WordTrace (prefixWord ++ tailWord_3966389) baseStart_3966389 baseEnd_3966389 := by
    simpa [prefixWord, tailWord_3966389, baseEnd_3966389] using wordTrace_append hprefix tailTrace_3966389
  have hstable : (prefixWord ++ tailWord_3966389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966389).length < 2 ^ (prefixWord ++ tailWord_3966389).sum := by decide
  have hdescent : baseEnd_3966389 < baseStart_3966389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966393 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 1, 1, 4]
def baseStart_3966393 : Nat := 118140960795 + 3966393 * 2 ^ 59
def prefixEnd_3966393 : Nat := 4983230072969 + 3 ^ 40 * 3966393 * 2
def baseEnd_3966393 : Nat := 2036666073628805202846397

theorem tailTrace_3966393 : CollatzResearch.WordTrace tailWord_3966393 prefixEnd_3966393 2036666073628805202846397 := by
  unfold tailWord_3966393
  simp only [CollatzResearch.WordTrace]
  refine ⟨144666237519443041838463833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96444158346295361225642555 144666237519443041838463833)
  ·
    refine ⟨108499678139582281378847875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144666237519443041838463833 108499678139582281378847875)
    ·
      refine ⟨162749517209373422068271813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108499678139582281378847875 162749517209373422068271813)
      ·
        refine ⟨30515534476757516637800965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162749517209373422068271813 30515534476757516637800965)
        ·
          refine ⟨5721662714392034369587681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30515534476757516637800965 5721662714392034369587681)
          ·
            refine ⟨4291247035794025777190761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5721662714392034369587681 4291247035794025777190761)
            ·
              refine ⟨3218435276845519332893071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291247035794025777190761 3218435276845519332893071)
              ·
                refine ⟨4827652915268278999339607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218435276845519332893071 4827652915268278999339607)
                ·
                  refine ⟨7241479372902418499009411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827652915268278999339607 7241479372902418499009411)
                  ·
                    refine ⟨10862219059353627748514117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7241479372902418499009411 10862219059353627748514117)
                    ·
                      refine ⟨2036666073628805202846397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10862219059353627748514117 2036666073628805202846397)
                      ·
                        rfl

theorem cell23_3966393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_3966393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966393 prefixEnd_3966393 := by exact prefixLift 3966393
  have htrace : WordTrace (prefixWord ++ tailWord_3966393) baseStart_3966393 baseEnd_3966393 := by
    simpa [prefixWord, tailWord_3966393, baseEnd_3966393] using wordTrace_append hprefix tailTrace_3966393
  have hstable : (prefixWord ++ tailWord_3966393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966393).length < 2 ^ (prefixWord ++ tailWord_3966393).sum := by decide
  have hdescent : baseEnd_3966393 < baseStart_3966393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966426 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_3966426 : Nat := 118140960795 + 3966426 * 2 ^ 59
def prefixEnd_3966426 : Nat := 4983230072969 + 3 ^ 40 * 3966426 * 2
def baseEnd_3966426 : Nat := 2036683018490403573733745

theorem tailTrace_3966426 : CollatzResearch.WordTrace tailWord_3966426 prefixEnd_3966426 2036683018490403573733745 := by
  unfold tailWord_3966426
  simp only [CollatzResearch.WordTrace]
  refine ⟨36166860282080872118603783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96444960752215658982943421 36166860282080872118603783)
  ·
    refine ⟨54250290423121308177905675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36166860282080872118603783 54250290423121308177905675)
    ·
      refine ⟨81375435634681962266858513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54250290423121308177905675 81375435634681962266858513)
      ·
        refine ⟨61031576726011471700143885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81375435634681962266858513 61031576726011471700143885)
        ·
          refine ⟨22886841272254301887553957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61031576726011471700143885 22886841272254301887553957)
          ·
            refine ⟨4291282738547681603916367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22886841272254301887553957 4291282738547681603916367)
            ·
              refine ⟨6436924107821522405874551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291282738547681603916367 6436924107821522405874551)
              ·
                refine ⟨9655386161732283608811827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436924107821522405874551 9655386161732283608811827)
                ·
                  refine ⟨14483079242598425413217741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9655386161732283608811827 14483079242598425413217741)
                  ·
                    refine ⟨5431154715974409529956653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14483079242598425413217741 5431154715974409529956653)
                    ·
                      refine ⟨2036683018490403573733745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5431154715974409529956653 2036683018490403573733745)
                      ·
                        rfl

theorem cell23_3966426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_3966426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966426 prefixEnd_3966426 := by exact prefixLift 3966426
  have htrace : WordTrace (prefixWord ++ tailWord_3966426) baseStart_3966426 baseEnd_3966426 := by
    simpa [prefixWord, tailWord_3966426, baseEnd_3966426] using wordTrace_append hprefix tailTrace_3966426
  have hstable : (prefixWord ++ tailWord_3966426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966426).length < 2 ^ (prefixWord ++ tailWord_3966426).sum := by decide
  have hdescent : baseEnd_3966426 < baseStart_3966426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966477 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3966477 : Nat := 118140960795 + 3966477 * 2 ^ 59
def prefixEnd_3966477 : Nat := 4983230072969 + 3 ^ 40 * 3966477 * 2
def baseEnd_3966477 : Nat := 2036709206003782874196011

theorem tailTrace_3966477 : CollatzResearch.WordTrace tailWord_3966477 prefixEnd_3966477 2036709206003782874196011 := by
  unfold tailWord_3966477
  simp only [CollatzResearch.WordTrace]
  refine ⟨144669301251138724184521685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96446200834092482789681123 144669301251138724184521685)
  ·
    refine ⟨3390686748073563848074727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 144669301251138724184521685 3390686748073563848074727)
    ·
      refine ⟨5086030122110345772112091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3390686748073563848074727 5086030122110345772112091)
      ·
        refine ⟨7629045183165518658168137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5086030122110345772112091 7629045183165518658168137)
        ·
          refine ⟨5721783887374138993626103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7629045183165518658168137 5721783887374138993626103)
          ·
            refine ⟨8582675831061208490439155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721783887374138993626103 8582675831061208490439155)
            ·
              refine ⟨12874013746591812735658733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8582675831061208490439155 12874013746591812735658733)
              ·
                refine ⟨4827755154971929775872025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12874013746591812735658733 4827755154971929775872025)
                ·
                  refine ⟨3620816366228947331904019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4827755154971929775872025 3620816366228947331904019)
                  ·
                    refine ⟨5431224549343420997856029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3620816366228947331904019 5431224549343420997856029)
                    ·
                      refine ⟨2036709206003782874196011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5431224549343420997856029 2036709206003782874196011)
                      ·
                        rfl

theorem cell23_3966477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3966477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966477 prefixEnd_3966477 := by exact prefixLift 3966477
  have htrace : WordTrace (prefixWord ++ tailWord_3966477) baseStart_3966477 baseEnd_3966477 := by
    simpa [prefixWord, tailWord_3966477, baseEnd_3966477] using wordTrace_append hprefix tailTrace_3966477
  have hstable : (prefixWord ++ tailWord_3966477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966477).length < 2 ^ (prefixWord ++ tailWord_3966477).sum := by decide
  have hdescent : baseEnd_3966477 < baseStart_3966477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966483 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 2, 2, 2]
def baseStart_3966483 : Nat := 118140960795 + 3966483 * 2 ^ 59
def prefixEnd_3966483 : Nat := 4983230072969 + 3 ^ 40 * 3966483 * 2
def baseEnd_3966483 : Nat := 2036712286887709850720983

theorem tailTrace_3966483 : CollatzResearch.WordTrace tailWord_3966483 prefixEnd_3966483 2036712286887709850720983 := by
  unfold tailWord_3966483
  simp only [CollatzResearch.WordTrace]
  refine ⟨144669520089116987209240103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96446346726077991472826735 144669520089116987209240103)
  ·
    refine ⟨217004280133675480813860155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144669520089116987209240103 217004280133675480813860155)
    ·
      refine ⟨325506420200513221220790233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217004280133675480813860155 325506420200513221220790233)
      ·
        refine ⟨244129815150384915915592675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325506420200513221220790233 244129815150384915915592675)
        ·
          refine ⟨366194722725577373873389013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244129815150384915915592675 366194722725577373873389013)
          ·
            refine ⟨8582688813880719700157555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 366194722725577373873389013 8582688813880719700157555)
            ·
              refine ⟨12874033220821079550236333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8582688813880719700157555 12874033220821079550236333)
              ·
                refine ⟨4827762457807904831338625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12874033220821079550236333 4827762457807904831338625)
                ·
                  refine ⟨3620821843355928623503969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4827762457807904831338625 3620821843355928623503969)
                  ·
                    refine ⟨2715616382516946467627977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3620821843355928623503969 2715616382516946467627977)
                    ·
                      refine ⟨2036712286887709850720983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715616382516946467627977 2036712286887709850720983)
                      ·
                        rfl

theorem cell23_3966483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 2, 2].length) (baseStart_3966483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966483 prefixEnd_3966483 := by exact prefixLift 3966483
  have htrace : WordTrace (prefixWord ++ tailWord_3966483) baseStart_3966483 baseEnd_3966483 := by
    simpa [prefixWord, tailWord_3966483, baseEnd_3966483] using wordTrace_append hprefix tailTrace_3966483
  have hstable : (prefixWord ++ tailWord_3966483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966483).length < 2 ^ (prefixWord ++ tailWord_3966483).sum := by decide
  have hdescent : baseEnd_3966483 < baseStart_3966483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966506 : List Nat := [3, 1, 4, 1, 1, 1, 2, 5, 5]
def baseStart_3966506 : Nat := 118140960795 + 3966506 * 2 ^ 59
def prefixEnd_3966506 : Nat := 4983230072969 + 3 ^ 40 * 3966506 * 2
def baseEnd_3966506 : Nat := 226302677438084806748153

theorem tailTrace_3966506 : CollatzResearch.WordTrace tailWord_3966506 prefixEnd_3966506 226302677438084806748153 := by
  unfold tailWord_3966506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36167589742008415534331843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96446905978689108091551581 36167589742008415534331843)
  ·
    refine ⟨54251384613012623301497765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36167589742008415534331843 54251384613012623301497765)
    ·
      refine ⟨10172134614939866869030831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54251384613012623301497765 10172134614939866869030831)
      ·
        refine ⟨15258201922409800303546247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10172134614939866869030831 15258201922409800303546247)
        ·
          refine ⟨22887302883614700455319371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15258201922409800303546247 22887302883614700455319371)
          ·
            refine ⟨34330954325422050682979057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22887302883614700455319371 34330954325422050682979057)
            ·
              refine ⟨25748215744066538012234293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34330954325422050682979057 25748215744066538012234293)
              ·
                refine ⟨2413895226006237938646965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25748215744066538012234293 2413895226006237938646965)
                ·
                  refine ⟨226302677438084806748153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2413895226006237938646965 226302677438084806748153)
                  ·
                    rfl

theorem cell23_3966506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_3966506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966506 prefixEnd_3966506 := by exact prefixLift 3966506
  have htrace : WordTrace (prefixWord ++ tailWord_3966506) baseStart_3966506 baseEnd_3966506 := by
    simpa [prefixWord, tailWord_3966506, baseEnd_3966506] using wordTrace_append hprefix tailTrace_3966506
  have hstable : (prefixWord ++ tailWord_3966506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966506).length < 2 ^ (prefixWord ++ tailWord_3966506).sum := by decide
  have hdescent : baseEnd_3966506 < baseStart_3966506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966519 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 2, 5]
def baseStart_3966519 : Nat := 118140960795 + 3966519 * 2 ^ 59
def prefixEnd_3966519 : Nat := 4983230072969 + 3 ^ 40 * 3966519 * 2
def baseEnd_3966519 : Nat := 678910257397090569956939

theorem tailTrace_3966519 : CollatzResearch.WordTrace tailWord_3966519 prefixEnd_3966519 678910257397090569956939 := by
  unfold tailWord_3966519
  simp only [CollatzResearch.WordTrace]
  refine ⟨144670833116986565357550611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96447222077991043571700407 144670833116986565357550611)
  ·
    refine ⟨217006249675479848036325917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144670833116986565357550611 217006249675479848036325917)
    ·
      refine ⟨81377343628304943013622219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217006249675479848036325917 81377343628304943013622219)
      ·
        refine ⟨122066015442457414520433329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81377343628304943013622219 122066015442457414520433329)
        ·
          refine ⟨91549511581843060890324997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122066015442457414520433329 91549511581843060890324997)
          ·
            refine ⟨17165533421595573916935937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91549511581843060890324997 17165533421595573916935937)
            ·
              refine ⟨12874150066196680437701953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17165533421595573916935937 12874150066196680437701953)
              ·
                refine ⟨9655612549647510328276465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12874150066196680437701953 9655612549647510328276465)
                ·
                  refine ⟨7241709412235632746207349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9655612549647510328276465 7241709412235632746207349)
                  ·
                    refine ⟨678910257397090569956939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7241709412235632746207349 678910257397090569956939)
                    ·
                      rfl

theorem cell23_3966519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_3966519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966519 prefixEnd_3966519 := by exact prefixLift 3966519
  have htrace : WordTrace (prefixWord ++ tailWord_3966519) baseStart_3966519 baseEnd_3966519 := by
    simpa [prefixWord, tailWord_3966519, baseEnd_3966519] using wordTrace_append hprefix tailTrace_3966519
  have hstable : (prefixWord ++ tailWord_3966519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966519).length < 2 ^ (prefixWord ++ tailWord_3966519).sum := by decide
  have hdescent : baseEnd_3966519 < baseStart_3966519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966529 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3966529 : Nat := 118140960795 + 3966529 * 2 ^ 59
def prefixEnd_3966529 : Nat := 4983230072969 + 3 ^ 40 * 3966529 * 2
def baseEnd_3966529 : Nat := 2036735906997816670745771

theorem tailTrace_3966529 : CollatzResearch.WordTrace tailWord_3966529 prefixEnd_3966529 2036735906997816670745771 := by
  unfold tailWord_3966529
  simp only [CollatzResearch.WordTrace]
  refine ⟨144671197846950337065414641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96447465231300224710276427 144671197846950337065414641)
  ·
    refine ⟨108503398385212752799060981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144671197846950337065414641 108503398385212752799060981)
    ·
      refine ⟨10172193598613695574911967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108503398385212752799060981 10172193598613695574911967)
      ·
        refine ⟨15258290397920543362367951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10172193598613695574911967 15258290397920543362367951)
        ·
          refine ⟨22887435596880815043551927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15258290397920543362367951 22887435596880815043551927)
          ·
            refine ⟨34331153395321222565327891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22887435596880815043551927 34331153395321222565327891)
            ·
              refine ⟨51496730092981833847991837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34331153395321222565327891 51496730092981833847991837)
              ·
                refine ⟨19311273784868187692996939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51496730092981833847991837 19311273784868187692996939)
                ·
                  refine ⟨28966910677302281539495409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19311273784868187692996939 28966910677302281539495409)
                  ·
                    refine ⟨21725183007976711154621557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28966910677302281539495409 21725183007976711154621557)
                    ·
                      refine ⟨2036735906997816670745771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21725183007976711154621557 2036735906997816670745771)
                      ·
                        rfl

theorem cell23_3966529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3966529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966529 prefixEnd_3966529 := by exact prefixLift 3966529
  have htrace : WordTrace (prefixWord ++ tailWord_3966529) baseStart_3966529 baseEnd_3966529 := by
    simpa [prefixWord, tailWord_3966529, baseEnd_3966529] using wordTrace_append hprefix tailTrace_3966529
  have hstable : (prefixWord ++ tailWord_3966529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966529).length < 2 ^ (prefixWord ++ tailWord_3966529).sum := by decide
  have hdescent : baseEnd_3966529 < baseStart_3966529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966556 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3966556 : Nat := 118140960795 + 3966556 * 2 ^ 59
def prefixEnd_3966556 : Nat := 4983230072969 + 3 ^ 40 * 3966556 * 2
def baseEnd_3966556 : Nat := 2036749770975488065108147

theorem tailTrace_3966556 : CollatzResearch.WordTrace tailWord_3966556 prefixEnd_3966556 2036749770975488065108147 := by
  unfold tailWord_3966556
  simp only [CollatzResearch.WordTrace]
  refine ⟨72336091308926260338323761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96448121745235013784431681 72336091308926260338323761)
  ·
    refine ⟨54252068481694695253742821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72336091308926260338323761 54252068481694695253742821)
    ·
      refine ⟨10172262840317755360076779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54252068481694695253742821 10172262840317755360076779)
      ·
        refine ⟨15258394260476633040115169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10172262840317755360076779 15258394260476633040115169)
        ·
          refine ⟨11443795695357474780086377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15258394260476633040115169 11443795695357474780086377)
          ·
            refine ⟨8582846771518106085064783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11443795695357474780086377 8582846771518106085064783)
            ·
              refine ⟨12874270157277159127597175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8582846771518106085064783 12874270157277159127597175)
              ·
                refine ⟨19311405235915738691395763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12874270157277159127597175 19311405235915738691395763)
                ·
                  refine ⟨28967107853873608037093645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19311405235915738691395763 28967107853873608037093645)
                  ·
                    refine ⟨10862665445202603013910117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28967107853873608037093645 10862665445202603013910117)
                    ·
                      refine ⟨2036749770975488065108147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10862665445202603013910117 2036749770975488065108147)
                      ·
                        rfl

theorem cell23_3966556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3966556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966556 prefixEnd_3966556 := by exact prefixLift 3966556
  have htrace : WordTrace (prefixWord ++ tailWord_3966556) baseStart_3966556 baseEnd_3966556 := by
    simpa [prefixWord, tailWord_3966556, baseEnd_3966556] using wordTrace_append hprefix tailTrace_3966556
  have hstable : (prefixWord ++ tailWord_3966556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966556).length < 2 ^ (prefixWord ++ tailWord_3966556).sum := by decide
  have hdescent : baseEnd_3966556 < baseStart_3966556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966659 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4]
def baseStart_3966659 : Nat := 118140960795 + 3966659 * 2 ^ 59
def prefixEnd_3966659 : Nat := 4983230072969 + 3 ^ 40 * 3966659 * 2
def baseEnd_3966659 : Nat := 2036802659482901162120173

theorem tailTrace_3966659 : CollatzResearch.WordTrace tailWord_3966659 prefixEnd_3966659 2036802659482901162120173 := by
  unfold tailWord_3966659
  simp only [CollatzResearch.WordTrace]
  refine ⟨144675939336479369267647031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96450626224319579511764687 144675939336479369267647031)
  ·
    refine ⟨217013909004719053901470547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144675939336479369267647031 217013909004719053901470547)
    ·
      refine ⟨325520863507078580852205821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217013909004719053901470547 325520863507078580852205821)
      ·
        refine ⟨122070323815154467819577183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325520863507078580852205821 122070323815154467819577183)
        ·
          refine ⟨183105485722731701729365775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122070323815154467819577183 183105485722731701729365775)
          ·
            refine ⟨274658228584097552594048663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183105485722731701729365775 274658228584097552594048663)
            ·
              refine ⟨411987342876146328891072995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274658228584097552594048663 411987342876146328891072995)
              ·
                refine ⟨617981014314219493336609493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411987342876146328891072995 617981014314219493336609493)
                ·
                  refine ⟨14483930022989519375076785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 617981014314219493336609493 14483930022989519375076785)
                  ·
                    refine ⟨10862947517242139531307589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14483930022989519375076785 10862947517242139531307589)
                    ·
                      refine ⟨2036802659482901162120173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10862947517242139531307589 2036802659482901162120173)
                      ·
                        rfl

theorem cell23_3966659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_3966659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966659 prefixEnd_3966659 := by exact prefixLift 3966659
  have htrace : WordTrace (prefixWord ++ tailWord_3966659) baseStart_3966659 baseEnd_3966659 := by
    simpa [prefixWord, tailWord_3966659, baseEnd_3966659] using wordTrace_append hprefix tailTrace_3966659
  have hstable : (prefixWord ++ tailWord_3966659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966659).length < 2 ^ (prefixWord ++ tailWord_3966659).sum := by decide
  have hdescent : baseEnd_3966659 < baseStart_3966659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966663 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_3966663 : Nat := 118140960795 + 3966663 * 2 ^ 59
def prefixEnd_3966663 : Nat := 4983230072969 + 3 ^ 40 * 3966663 * 2
def baseEnd_3966663 : Nat := 2036804713405519146470155

theorem tailTrace_3966663 : CollatzResearch.WordTrace tailWord_3966663 prefixEnd_3966663 2036804713405519146470155 := by
  unfold tailWord_3966663
  simp only [CollatzResearch.WordTrace]
  refine ⟨144676085228464877950792643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96450723485643251967195095 144676085228464877950792643)
  ·
    refine ⟨217014127842697316926188965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144676085228464877950792643 217014127842697316926188965)
    ·
      refine ⟨40690148970505746923660431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217014127842697316926188965 40690148970505746923660431)
      ·
        refine ⟨61035223455758620385490647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40690148970505746923660431 61035223455758620385490647)
        ·
          refine ⟨91552835183637930578235971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61035223455758620385490647 91552835183637930578235971)
          ·
            refine ⟨137329252775456895867353957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91552835183637930578235971 137329252775456895867353957)
            ·
              refine ⟨25749234895398167975128867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137329252775456895867353957 25749234895398167975128867)
              ·
                refine ⟨38623852343097251962693301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25749234895398167975128867 38623852343097251962693301)
                ·
                  refine ⟨3620986157165367371502497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38623852343097251962693301 3620986157165367371502497)
                  ·
                    refine ⟨2715739617874025528626873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3620986157165367371502497 2715739617874025528626873)
                    ·
                      refine ⟨2036804713405519146470155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715739617874025528626873 2036804713405519146470155)
                      ·
                        rfl

theorem cell23_3966663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_3966663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966663 prefixEnd_3966663 := by exact prefixLift 3966663
  have htrace : WordTrace (prefixWord ++ tailWord_3966663) baseStart_3966663 baseEnd_3966663 := by
    simpa [prefixWord, tailWord_3966663, baseEnd_3966663] using wordTrace_append hprefix tailTrace_3966663
  have hstable : (prefixWord ++ tailWord_3966663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966663).length < 2 ^ (prefixWord ++ tailWord_3966663).sum := by decide
  have hdescent : baseEnd_3966663 < baseStart_3966663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966691 : List Nat := [1, 1, 1, 7, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3966691 : Nat := 118140960795 + 3966691 * 2 ^ 59
def prefixEnd_3966691 : Nat := 4983230072969 + 3 ^ 40 * 3966691 * 2
def baseEnd_3966691 : Nat := 2036819090863845036920027

theorem tailTrace_3966691 : CollatzResearch.WordTrace tailWord_3966691 prefixEnd_3966691 2036819090863845036920027 := by
  unfold tailWord_3966691
  simp only [CollatzResearch.WordTrace]
  refine ⟨144677106472363438732811927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96451404314908959155207951 144677106472363438732811927)
  ·
    refine ⟨217015659708545158099217891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144677106472363438732811927 217015659708545158099217891)
    ·
      refine ⟨325523489562817737148826837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217015659708545158099217891 325523489562817737148826837)
      ·
        refine ⟨7629456786628540714425629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 325523489562817737148826837 7629456786628540714425629)
        ·
          refine ⟨2861046294985702767909611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7629456786628540714425629 2861046294985702767909611)
          ·
            refine ⟨4291569442478554151864417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861046294985702767909611 4291569442478554151864417)
            ·
              refine ⟨3218677081858915613898313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291569442478554151864417 3218677081858915613898313)
              ·
                refine ⟨2414007811394186710423735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218677081858915613898313 2414007811394186710423735)
                ·
                  refine ⟨3621011717091280065635603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414007811394186710423735 3621011717091280065635603)
                  ·
                    refine ⟨5431517575636920098453405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3621011717091280065635603 5431517575636920098453405)
                    ·
                      refine ⟨2036819090863845036920027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5431517575636920098453405 2036819090863845036920027)
                      ·
                        rfl

theorem cell23_3966691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3966691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966691 prefixEnd_3966691 := by exact prefixLift 3966691
  have htrace : WordTrace (prefixWord ++ tailWord_3966691) baseStart_3966691 baseEnd_3966691 := by
    simpa [prefixWord, tailWord_3966691, baseEnd_3966691] using wordTrace_append hprefix tailTrace_3966691
  have hstable : (prefixWord ++ tailWord_3966691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966691).length < 2 ^ (prefixWord ++ tailWord_3966691).sum := by decide
  have hdescent : baseEnd_3966691 < baseStart_3966691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966699 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 2, 7]
def baseStart_3966699 : Nat := 118140960795 + 3966699 * 2 ^ 59
def prefixEnd_3966699 : Nat := 4983230072969 + 3 ^ 40 * 3966699 * 2
def baseEnd_3966699 : Nat := 678941066236360335206663

theorem tailTrace_3966699 : CollatzResearch.WordTrace tailWord_3966699 prefixEnd_3966699 678941066236360335206663 := by
  unfold tailWord_3966699
  simp only [CollatzResearch.WordTrace]
  refine ⟨144677398256334456099103151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96451598837556304066068767 144677398256334456099103151)
  ·
    refine ⟨217016097384501684148654727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144677398256334456099103151 217016097384501684148654727)
    ·
      refine ⟨325524146076752526222982091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217016097384501684148654727 325524146076752526222982091)
      ·
        refine ⟨488286219115128789334473137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325524146076752526222982091 488286219115128789334473137)
        ·
          refine ⟨366214664336346592000854853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488286219115128789334473137 366214664336346592000854853)
          ·
            refine ⟨68665249563064986000160285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366214664336346592000854853 68665249563064986000160285)
            ·
              refine ⟨25749468586149369750060107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68665249563064986000160285 25749468586149369750060107)
              ·
                refine ⟨38624202879224054625090161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25749468586149369750060107 38624202879224054625090161)
                ·
                  refine ⟨28968152159418040968817621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38624202879224054625090161 28968152159418040968817621)
                  ·
                    refine ⟨678941066236360335206663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28968152159418040968817621 678941066236360335206663)
                    ·
                      rfl

theorem cell23_3966699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_3966699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966699 prefixEnd_3966699 := by exact prefixLift 3966699
  have htrace : WordTrace (prefixWord ++ tailWord_3966699) baseStart_3966699 baseEnd_3966699 := by
    simpa [prefixWord, tailWord_3966699, baseEnd_3966699] using wordTrace_append hprefix tailTrace_3966699
  have hstable : (prefixWord ++ tailWord_3966699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966699).length < 2 ^ (prefixWord ++ tailWord_3966699).sum := by decide
  have hdescent : baseEnd_3966699 < baseStart_3966699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966723 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 3, 3, 2]
def baseStart_3966723 : Nat := 118140960795 + 3966723 * 2 ^ 59
def prefixEnd_3966723 : Nat := 4983230072969 + 3 ^ 40 * 3966723 * 2
def baseEnd_3966723 : Nat := 2036835522244788911719879

theorem tailTrace_3966723 : CollatzResearch.WordTrace tailWord_3966723 prefixEnd_3966723 2036835522244788911719879 := by
  unfold tailWord_3966723
  simp only [CollatzResearch.WordTrace]
  refine ⟨144678273608247508197976823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96452182405498338798651215 144678273608247508197976823)
  ·
    refine ⟨217017410412371262296965235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144678273608247508197976823 217017410412371262296965235)
    ·
      refine ⟨325526115618556893445447853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217017410412371262296965235 325526115618556893445447853)
      ·
        refine ⟨122072293356958835042042945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325526115618556893445447853 122072293356958835042042945)
        ·
          refine ⟨91554220017719126281532209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122072293356958835042042945 91554220017719126281532209)
          ·
            refine ⟨68665665013289344711149157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91554220017719126281532209 68665665013289344711149157)
            ·
              refine ⟨12874812189991752133340467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68665665013289344711149157 12874812189991752133340467)
              ·
                refine ⟨19312218284987628200010701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12874812189991752133340467 19312218284987628200010701)
                ·
                  refine ⟨7242081856870360575004013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19312218284987628200010701 7242081856870360575004013)
                  ·
                    refine ⟨2715780696326385215626505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7242081856870360575004013 2715780696326385215626505)
                    ·
                      refine ⟨2036835522244788911719879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715780696326385215626505 2036835522244788911719879)
                      ·
                        rfl

theorem cell23_3966723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_3966723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966723 prefixEnd_3966723 := by exact prefixLift 3966723
  have htrace : WordTrace (prefixWord ++ tailWord_3966723) baseStart_3966723 baseEnd_3966723 := by
    simpa [prefixWord, tailWord_3966723, baseEnd_3966723] using wordTrace_append hprefix tailTrace_3966723
  have hstable : (prefixWord ++ tailWord_3966723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966723).length < 2 ^ (prefixWord ++ tailWord_3966723).sum := by decide
  have hdescent : baseEnd_3966723 < baseStart_3966723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966729 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 3, 8]
def baseStart_3966729 : Nat := 118140960795 + 3966729 * 2 ^ 59
def prefixEnd_3966729 : Nat := 4983230072969 + 3 ^ 40 * 3966729 * 2
def baseEnd_3966729 : Nat := 678946201042905296081617

theorem tailTrace_3966729 : CollatzResearch.WordTrace tailWord_3966729 prefixEnd_3966729 678946201042905296081617 := by
  unfold tailWord_3966729
  simp only [CollatzResearch.WordTrace]
  refine ⟨144678492446225771222695241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96452328297483847481796827 144678492446225771222695241)
  ·
    refine ⟨108508869334669328417021431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144678492446225771222695241 108508869334669328417021431)
    ·
      refine ⟨162763304002003992625532147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108508869334669328417021431 162763304002003992625532147)
      ·
        refine ⟨244144956003005988938298221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162763304002003992625532147 244144956003005988938298221)
        ·
          refine ⟨91554358501127245851861833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244144956003005988938298221 91554358501127245851861833)
          ·
            refine ⟨68665768875845434388896375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91554358501127245851861833 68665768875845434388896375)
            ·
              refine ⟨102998653313768151583344563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68665768875845434388896375 102998653313768151583344563)
              ·
                refine ⟨154497979970652227375016845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102998653313768151583344563 154497979970652227375016845)
                ·
                  refine ⟨57936742488994585265631317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154497979970652227375016845 57936742488994585265631317)
                  ·
                    refine ⟨678946201042905296081617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57936742488994585265631317 678946201042905296081617)
                    ·
                      rfl

theorem cell23_3966729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_3966729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966729 prefixEnd_3966729 := by exact prefixLift 3966729
  have htrace : WordTrace (prefixWord ++ tailWord_3966729) baseStart_3966729 baseEnd_3966729 := by
    simpa [prefixWord, tailWord_3966729, baseEnd_3966729] using wordTrace_append hprefix tailTrace_3966729
  have hstable : (prefixWord ++ tailWord_3966729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966729).length < 2 ^ (prefixWord ++ tailWord_3966729).sum := by decide
  have hdescent : baseEnd_3966729 < baseStart_3966729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966746 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_3966746 : Nat := 118140960795 + 3966746 * 2 ^ 59
def prefixEnd_3966746 : Nat := 4983230072969 + 3 ^ 40 * 3966746 * 2
def baseEnd_3966746 : Nat := 678949110766614107244091

theorem tailTrace_3966746 : CollatzResearch.WordTrace tailWord_3966746 prefixEnd_3966746 678949110766614107244091 := by
  unfold tailWord_3966746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36169778121791045781516023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96452741658109455417376061 36169778121791045781516023)
  ·
    refine ⟨54254667182686568672274035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36169778121791045781516023 54254667182686568672274035)
    ·
      refine ⟨81382000774029853008411053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54254667182686568672274035 81382000774029853008411053)
      ·
        refine ⟨30518250290261194878154145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81382000774029853008411053 30518250290261194878154145)
        ·
          refine ⟨22888687717695896158615609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30518250290261194878154145 22888687717695896158615609)
          ·
            refine ⟨17166515788271922118961707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22888687717695896158615609 17166515788271922118961707)
            ·
              refine ⟨25749773682407883178442561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17166515788271922118961707 25749773682407883178442561)
              ·
                refine ⟨19312330261805912383831921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25749773682407883178442561 19312330261805912383831921)
                ·
                  refine ⟨14484247696354434287873941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19312330261805912383831921 14484247696354434287873941)
                  ·
                    refine ⟨678949110766614107244091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14484247696354434287873941 678949110766614107244091)
                    ·
                      rfl

theorem cell23_3966746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_3966746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966746 prefixEnd_3966746 := by exact prefixLift 3966746
  have htrace : WordTrace (prefixWord ++ tailWord_3966746) baseStart_3966746 baseEnd_3966746 := by
    simpa [prefixWord, tailWord_3966746, baseEnd_3966746] using wordTrace_append hprefix tailTrace_3966746
  have hstable : (prefixWord ++ tailWord_3966746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966746).length < 2 ^ (prefixWord ++ tailWord_3966746).sum := by decide
  have hdescent : baseEnd_3966746 < baseStart_3966746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966770 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_3966770 : Nat := 118140960795 + 3966770 * 2 ^ 59
def prefixEnd_3966770 : Nat := 4983230072969 + 3 ^ 40 * 3966770 * 2
def baseEnd_3966770 : Nat := 2036859655835550227832163

theorem tailTrace_3966770 : CollatzResearch.WordTrace tailWord_3966770 prefixEnd_3966770 2036859655835550227832163 := by
  unfold tailWord_3966770
  simp only [CollatzResearch.WordTrace]
  refine ⟨36169996959769308806234441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96453325226051490149958509 36169996959769308806234441)
  ·
    refine ⟨27127497719826981604675831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36169996959769308806234441 27127497719826981604675831)
    ·
      refine ⟨40691246579740472407013747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27127497719826981604675831 40691246579740472407013747)
      ·
        refine ⟨61036869869610708610520621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40691246579740472407013747 61036869869610708610520621)
        ·
          refine ⟨22888826201104015728945233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61036869869610708610520621 22888826201104015728945233)
          ·
            refine ⟨17166619650828011796708925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22888826201104015728945233 17166619650828011796708925)
            ·
              refine ⟨6437482369060504423765847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17166619650828011796708925 6437482369060504423765847)
              ·
                refine ⟨9656223553590756635648771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437482369060504423765847 9656223553590756635648771)
                ·
                  refine ⟨14484335330386134953473157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9656223553590756635648771 14484335330386134953473157)
                  ·
                    refine ⟨2715812874447400303776217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14484335330386134953473157 2715812874447400303776217)
                    ·
                      refine ⟨2036859655835550227832163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715812874447400303776217 2036859655835550227832163)
                      ·
                        rfl

theorem cell23_3966770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_3966770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966770 prefixEnd_3966770 := by exact prefixLift 3966770
  have htrace : WordTrace (prefixWord ++ tailWord_3966770) baseStart_3966770 baseEnd_3966770 := by
    simpa [prefixWord, tailWord_3966770, baseEnd_3966770] using wordTrace_append hprefix tailTrace_3966770
  have hstable : (prefixWord ++ tailWord_3966770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966770).length < 2 ^ (prefixWord ++ tailWord_3966770).sum := by decide
  have hdescent : baseEnd_3966770 < baseStart_3966770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966774 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3966774 : Nat := 118140960795 + 3966774 * 2 ^ 59
def prefixEnd_3966774 : Nat := 4983230072969 + 3 ^ 40 * 3966774 * 2
def baseEnd_3966774 : Nat := 2036861709758168212182145

theorem tailTrace_3966774 : CollatzResearch.WordTrace tailWord_3966774 prefixEnd_3966774 2036861709758168212182145 := by
  unfold tailWord_3966774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042508358191421494255211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96453422487375162605388917 9042508358191421494255211)
  ·
    refine ⟨13563762537287132241382817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9042508358191421494255211 13563762537287132241382817)
    ·
      refine ⟨10172821902965349181037113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13563762537287132241382817 10172821902965349181037113)
      ·
        refine ⟨7629616427224011885777835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10172821902965349181037113 7629616427224011885777835)
        ·
          refine ⟨11444424640836017828666753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7629616427224011885777835 11444424640836017828666753)
          ·
            refine ⟨8583318480627013371500065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11444424640836017828666753 8583318480627013371500065)
            ·
              refine ⟨6437488860470260028625049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8583318480627013371500065 6437488860470260028625049)
              ·
                refine ⟨4828116645352695021468787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6437488860470260028625049 4828116645352695021468787)
                ·
                  refine ⟨7242174968029042532203181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828116645352695021468787 7242174968029042532203181)
                  ·
                    refine ⟨2715815613010890949576193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7242174968029042532203181 2715815613010890949576193)
                    ·
                      refine ⟨2036861709758168212182145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715815613010890949576193 2036861709758168212182145)
                      ·
                        rfl

theorem cell23_3966774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3966774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966774 prefixEnd_3966774 := by exact prefixLift 3966774
  have htrace : WordTrace (prefixWord ++ tailWord_3966774) baseStart_3966774 baseEnd_3966774 := by
    simpa [prefixWord, tailWord_3966774, baseEnd_3966774] using wordTrace_append hprefix tailTrace_3966774
  have hstable : (prefixWord ++ tailWord_3966774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966774).length < 2 ^ (prefixWord ++ tailWord_3966774).sum := by decide
  have hdescent : baseEnd_3966774 < baseStart_3966774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966776 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 7]
def baseStart_3966776 : Nat := 118140960795 + 3966776 * 2 ^ 59
def prefixEnd_3966776 : Nat := 4983230072969 + 3 ^ 40 * 3966776 * 2
def baseEnd_3966776 : Nat := 226318081857719689373015

theorem tailTrace_3966776 : CollatzResearch.WordTrace tailWord_3966776 prefixEnd_3966776 226318081857719689373015 := by
  unfold tailWord_3966776
  simp only [CollatzResearch.WordTrace]
  refine ⟨72340103338527749124828091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96453471118036998833104121 72340103338527749124828091)
  ·
    refine ⟨108510155007791623687242137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72340103338527749124828091 108510155007791623687242137)
    ·
      refine ⟨81382616255843717765431603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108510155007791623687242137 81382616255843717765431603)
      ·
        refine ⟨122073924383765576648147405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81382616255843717765431603 122073924383765576648147405)
        ·
          refine ⟨45777721643912091243055277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122073924383765576648147405 45777721643912091243055277)
          ·
            refine ⟨17166645616467034216145729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45777721643912091243055277 17166645616467034216145729)
            ·
              refine ⟨12874984212350275662109297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17166645616467034216145729 12874984212350275662109297)
              ·
                refine ⟨9656238159262706746581973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12874984212350275662109297 9656238159262706746581973)
                ·
                  refine ⟨226318081857719689373015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9656238159262706746581973 226318081857719689373015)
                  ·
                    rfl

theorem cell23_3966776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 7].length) (baseStart_3966776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966776 prefixEnd_3966776 := by exact prefixLift 3966776
  have htrace : WordTrace (prefixWord ++ tailWord_3966776) baseStart_3966776 baseEnd_3966776 := by
    simpa [prefixWord, tailWord_3966776, baseEnd_3966776] using wordTrace_append hprefix tailTrace_3966776
  have hstable : (prefixWord ++ tailWord_3966776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966776).length < 2 ^ (prefixWord ++ tailWord_3966776).sum := by decide
  have hdescent : baseEnd_3966776 < baseStart_3966776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966790 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3966790 : Nat := 118140960795 + 3966790 * 2 ^ 59
def prefixEnd_3966790 : Nat := 4983230072969 + 3 ^ 40 * 3966790 * 2
def baseEnd_3966790 : Nat := 2036869925448640149582071

theorem tailTrace_3966790 : CollatzResearch.WordTrace tailWord_3966790 prefixEnd_3966790 2036869925448640149582071 := by
  unfold tailWord_3966790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521272415593899332520807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96453811532669852427110549 4521272415593899332520807)
  ·
    refine ⟨6781908623390848998781211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4521272415593899332520807 6781908623390848998781211)
    ·
      refine ⟨10172862935086273498171817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6781908623390848998781211 10172862935086273498171817)
      ·
        refine ⟨7629647201314705123628863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10172862935086273498171817 7629647201314705123628863)
        ·
          refine ⟨11444470801972057685443295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7629647201314705123628863 11444470801972057685443295)
          ·
            refine ⟨17166706202958086528164943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11444470801972057685443295 17166706202958086528164943)
            ·
              refine ⟨25750059304437129792247415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17166706202958086528164943 25750059304437129792247415)
              ·
                refine ⟨38625088956655694688371123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25750059304437129792247415 38625088956655694688371123)
                ·
                  refine ⟨57937633434983542032556685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38625088956655694688371123 57937633434983542032556685)
                  ·
                    refine ⟨21726612538118828262208757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57937633434983542032556685 21726612538118828262208757)
                    ·
                      refine ⟨2036869925448640149582071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21726612538118828262208757 2036869925448640149582071)
                      ·
                        rfl

theorem cell23_3966790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3966790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966790 prefixEnd_3966790 := by exact prefixLift 3966790
  have htrace : WordTrace (prefixWord ++ tailWord_3966790) baseStart_3966790 baseEnd_3966790 := by
    simpa [prefixWord, tailWord_3966790, baseEnd_3966790] using wordTrace_append hprefix tailTrace_3966790
  have hstable : (prefixWord ++ tailWord_3966790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966790).length < 2 ^ (prefixWord ++ tailWord_3966790).sum := by decide
  have hdescent : baseEnd_3966790 < baseStart_3966790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966810 : List Nat := [3, 1, 1, 2, 1, 3, 5, 2, 5]
def baseStart_3966810 : Nat := 118140960795 + 3966810 * 2 ^ 59
def prefixEnd_3966810 : Nat := 4983230072969 + 3 ^ 40 * 3966810 * 2
def baseEnd_3966810 : Nat := 226320021673525563481331

theorem tailTrace_3966810 : CollatzResearch.WordTrace tailWord_3966810 prefixEnd_3966810 226320021673525563481331 := by
  unfold tailWord_3966810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36170361689733080514098471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96454297839288214704262589 36170361689733080514098471)
  ·
    refine ⟨54255542534599620771147707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36170361689733080514098471 54255542534599620771147707)
    ·
      refine ⟨81383313801899431156721561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54255542534599620771147707 81383313801899431156721561)
      ·
        refine ⟨61037485351424573367541171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81383313801899431156721561 61037485351424573367541171)
        ·
          refine ⟨91556228027136860051311757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61037485351424573367541171 91556228027136860051311757)
          ·
            refine ⟨34333585510176322519241909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91556228027136860051311757 34333585510176322519241909)
            ·
              refine ⟨3218773641579030236178929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34333585510176322519241909 3218773641579030236178929)
              ·
                refine ⟨2414080231184272677134197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218773641579030236178929 2414080231184272677134197)
                ·
                  refine ⟨226320021673525563481331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2414080231184272677134197 226320021673525563481331)
                  ·
                    rfl

theorem cell23_3966810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_3966810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966810 prefixEnd_3966810 := by exact prefixLift 3966810
  have htrace : WordTrace (prefixWord ++ tailWord_3966810) baseStart_3966810 baseEnd_3966810 := by
    simpa [prefixWord, tailWord_3966810, baseEnd_3966810] using wordTrace_append hprefix tailTrace_3966810
  have hstable : (prefixWord ++ tailWord_3966810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966810).length < 2 ^ (prefixWord ++ tailWord_3966810).sum := by decide
  have hdescent : baseEnd_3966810 < baseStart_3966810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966816 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3966816 : Nat := 118140960795 + 3966816 * 2 ^ 59
def prefixEnd_3966816 : Nat := 4983230072969 + 3 ^ 40 * 3966816 * 2
def baseEnd_3966816 : Nat := 2036883275945657047856951

theorem tailTrace_3966816 : CollatzResearch.WordTrace tailWord_3966816 prefixEnd_3966816 2036883275945657047856951 := by
  unfold tailWord_3966816
  simp only [CollatzResearch.WordTrace]
  refine ⟨72340832798455292540556151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96454443731273723387408201 72340832798455292540556151)
  ·
    refine ⟨108511249197682938810834227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72340832798455292540556151 108511249197682938810834227)
    ·
      refine ⟨162766873796524408216251341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108511249197682938810834227 162766873796524408216251341)
      ·
        refine ⟨61037577673696653081094253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162766873796524408216251341 61037577673696653081094253)
        ·
          refine ⟨22889091627636244905410345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61037577673696653081094253 22889091627636244905410345)
          ·
            refine ⟨17166818720727183679057759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22889091627636244905410345 17166818720727183679057759)
            ·
              refine ⟨25750228081090775518586639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17166818720727183679057759 25750228081090775518586639)
              ·
                refine ⟨38625342121636163277879959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25750228081090775518586639 38625342121636163277879959)
                ·
                  refine ⟨57938013182454244916819939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38625342121636163277879959 57938013182454244916819939)
                  ·
                    refine ⟨86907019773681367375229909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57938013182454244916819939 86907019773681367375229909)
                    ·
                      refine ⟨2036883275945657047856951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86907019773681367375229909 2036883275945657047856951)
                      ·
                        rfl

theorem cell23_3966816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3966816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966816 prefixEnd_3966816 := by exact prefixLift 3966816
  have htrace : WordTrace (prefixWord ++ tailWord_3966816) baseStart_3966816 baseEnd_3966816 := by
    simpa [prefixWord, tailWord_3966816, baseEnd_3966816] using wordTrace_append hprefix tailTrace_3966816
  have hstable : (prefixWord ++ tailWord_3966816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966816).length < 2 ^ (prefixWord ++ tailWord_3966816).sum := by decide
  have hdescent : baseEnd_3966816 < baseStart_3966816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966843 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 4, 4, 2]
def baseStart_3966843 : Nat := 118140960795 + 3966843 * 2 ^ 59
def prefixEnd_3966843 : Nat := 4983230072969 + 3 ^ 40 * 3966843 * 2
def baseEnd_3966843 : Nat := 2036897139923328442219327

theorem tailTrace_3966843 : CollatzResearch.WordTrace tailWord_3966843 prefixEnd_3966843 2036897139923328442219327 := by
  unfold tailWord_3966843
  simp only [CollatzResearch.WordTrace]
  refine ⟨144682650367812768692345183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96455100245208512461563455 144682650367812768692345183)
  ·
    refine ⟨217023975551719153038517775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144682650367812768692345183 217023975551719153038517775)
    ·
      refine ⟨325535963327578729557776663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217023975551719153038517775 325535963327578729557776663)
      ·
        refine ⟨488303944991368094336664995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325535963327578729557776663 488303944991368094336664995)
        ·
          refine ⟨732455917487052141504997493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488303944991368094336664995 732455917487052141504997493)
          ·
            refine ⟨68667742264411138266093515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 732455917487052141504997493 68667742264411138266093515)
            ·
              refine ⟨103001613396616707399140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68667742264411138266093515 103001613396616707399140273)
              ·
                refine ⟨77251210047462530549355205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103001613396616707399140273 77251210047462530549355205)
                ·
                  refine ⟨14484601883899224478004101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77251210047462530549355205 14484601883899224478004101)
                  ·
                    refine ⟨2715862853231104589625769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14484601883899224478004101 2715862853231104589625769)
                    ·
                      refine ⟨2036897139923328442219327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715862853231104589625769 2036897139923328442219327)
                      ·
                        rfl

theorem cell23_3966843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 4, 2].length) (baseStart_3966843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966843 prefixEnd_3966843 := by exact prefixLift 3966843
  have htrace : WordTrace (prefixWord ++ tailWord_3966843) baseStart_3966843 baseEnd_3966843 := by
    simpa [prefixWord, tailWord_3966843, baseEnd_3966843] using wordTrace_append hprefix tailTrace_3966843
  have hstable : (prefixWord ++ tailWord_3966843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966843).length < 2 ^ (prefixWord ++ tailWord_3966843).sum := by decide
  have hdescent : baseEnd_3966843 < baseStart_3966843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966894 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3966894 : Nat := 118140960795 + 3966894 * 2 ^ 59
def prefixEnd_3966894 : Nat := 4983230072969 + 3 ^ 40 * 3966894 * 2
def baseEnd_3966894 : Nat := 2036923327436707742681593

theorem tailTrace_3966894 : CollatzResearch.WordTrace tailWord_3966894 prefixEnd_3966894 2036923327436707742681593 := by
  unfold tailWord_3966894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18085563811328500550306467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96456340327085336268301157 18085563811328500550306467)
  ·
    refine ⟨27128345716992750825459701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18085563811328500550306467 27128345716992750825459701)
    ·
      refine ⟨2543282410968070389886847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27128345716992750825459701 2543282410968070389886847)
      ·
        refine ⟨3814923616452105584830271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543282410968070389886847 3814923616452105584830271)
        ·
          refine ⟨5722385424678158377245407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3814923616452105584830271 5722385424678158377245407)
          ·
            refine ⟨8583578137017237565868111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722385424678158377245407 8583578137017237565868111)
            ·
              refine ⟨12875367205525856348802167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8583578137017237565868111 12875367205525856348802167)
              ·
                refine ⟨19313050808288784523203251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12875367205525856348802167 19313050808288784523203251)
                ·
                  refine ⟨28969576212433176784804877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19313050808288784523203251 28969576212433176784804877)
                  ·
                    refine ⟨10863591079662441294301829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28969576212433176784804877 10863591079662441294301829)
                    ·
                      refine ⟨2036923327436707742681593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10863591079662441294301829 2036923327436707742681593)
                      ·
                        rfl

theorem cell23_3966894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3966894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966894 prefixEnd_3966894 := by exact prefixLift 3966894
  have htrace : WordTrace (prefixWord ++ tailWord_3966894) baseStart_3966894 baseEnd_3966894 := by
    simpa [prefixWord, tailWord_3966894, baseEnd_3966894] using wordTrace_append hprefix tailTrace_3966894
  have hstable : (prefixWord ++ tailWord_3966894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966894).length < 2 ^ (prefixWord ++ tailWord_3966894).sum := by decide
  have hdescent : baseEnd_3966894 < baseStart_3966894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966897 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3966897 : Nat := 118140960795 + 3966897 * 2 ^ 59
def prefixEnd_3966897 : Nat := 4983230072969 + 3 ^ 40 * 3966897 * 2
def baseEnd_3966897 : Nat := 2036924867878671230944079

theorem tailTrace_3966897 : CollatzResearch.WordTrace tailWord_3966897 prefixEnd_3966897 2036924867878671230944079 := by
  unfold tailWord_3966897
  simp only [CollatzResearch.WordTrace]
  refine ⟨144684619909617135914810945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96456413273078090609873963 144684619909617135914810945)
  ·
    refine ⟨108513464932212851936108209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144684619909617135914810945 108513464932212851936108209)
    ·
      refine ⟨81385098699159638952081157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108513464932212851936108209 81385098699159638952081157)
      ·
        refine ⟨15259706006092432303515217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81385098699159638952081157 15259706006092432303515217)
        ·
          refine ⟨11444779504569324227636413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15259706006092432303515217 11444779504569324227636413)
          ·
            refine ⟨4291792314213496585363655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11444779504569324227636413 4291792314213496585363655)
            ·
              refine ⟨6437688471320244878045483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291792314213496585363655 6437688471320244878045483)
              ·
                refine ⟨9656532706980367317068225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437688471320244878045483 9656532706980367317068225)
                ·
                  refine ⟨7242399530235275487801169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9656532706980367317068225 7242399530235275487801169)
                  ·
                    refine ⟨5431799647676456615850877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7242399530235275487801169 5431799647676456615850877)
                    ·
                      refine ⟨2036924867878671230944079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5431799647676456615850877 2036924867878671230944079)
                      ·
                        rfl

theorem cell23_3966897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3966897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966897 prefixEnd_3966897 := by exact prefixLift 3966897
  have htrace : WordTrace (prefixWord ++ tailWord_3966897) baseStart_3966897 baseEnd_3966897 := by
    simpa [prefixWord, tailWord_3966897, baseEnd_3966897] using wordTrace_append hprefix tailTrace_3966897
  have hstable : (prefixWord ++ tailWord_3966897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966897).length < 2 ^ (prefixWord ++ tailWord_3966897).sum := by decide
  have hdescent : baseEnd_3966897 < baseStart_3966897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966927 : List Nat := [1, 1, 2, 1, 1, 5, 1, 6, 1, 1, 3]
def baseStart_3966927 : Nat := 118140960795 + 3966927 * 2 ^ 59
def prefixEnd_3966927 : Nat := 4983230072969 + 3 ^ 40 * 3966927 * 2
def baseEnd_3966927 : Nat := 2036940272298306113568941

theorem tailTrace_3966927 : CollatzResearch.WordTrace tailWord_3966927 prefixEnd_3966927 2036940272298306113568941 := by
  unfold tailWord_3966927
  simp only [CollatzResearch.WordTrace]
  refine ⟨144685714099508451038403035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96457142733005634025602023 144685714099508451038403035)
  ·
    refine ⟨217028571149262676557604553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144685714099508451038403035 217028571149262676557604553)
    ·
      refine ⟨162771428361947007418203415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217028571149262676557604553 162771428361947007418203415)
      ·
        refine ⟨244157142542920511127305123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162771428361947007418203415 244157142542920511127305123)
        ·
          refine ⟨366235713814380766690957685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244157142542920511127305123 366235713814380766690957685)
          ·
            refine ⟨34334598170098196877277283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366235713814380766690957685 34334598170098196877277283)
            ·
              refine ⟨51501897255147295315915925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34334598170098196877277283 51501897255147295315915925)
              ·
                refine ⟨2414151433835029467933559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51501897255147295315915925 2414151433835029467933559)
                ·
                  refine ⟨3621227150752544201900339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414151433835029467933559 3621227150752544201900339)
                  ·
                    refine ⟨5431840726128816302850509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3621227150752544201900339 5431840726128816302850509)
                    ·
                      refine ⟨2036940272298306113568941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5431840726128816302850509 2036940272298306113568941)
                      ·
                        rfl

theorem cell23_3966927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 1, 3].length) (baseStart_3966927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966927 prefixEnd_3966927 := by exact prefixLift 3966927
  have htrace : WordTrace (prefixWord ++ tailWord_3966927) baseStart_3966927 baseEnd_3966927 := by
    simpa [prefixWord, tailWord_3966927, baseEnd_3966927] using wordTrace_append hprefix tailTrace_3966927
  have hstable : (prefixWord ++ tailWord_3966927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966927).length < 2 ^ (prefixWord ++ tailWord_3966927).sum := by decide
  have hdescent : baseEnd_3966927 < baseStart_3966927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966934 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3966934 : Nat := 118140960795 + 3966934 * 2 ^ 59
def prefixEnd_3966934 : Nat := 4983230072969 + 3 ^ 40 * 3966934 * 2
def baseEnd_3966934 : Nat := 226327096295876398464601

theorem tailTrace_3966934 : CollatzResearch.WordTrace tailWord_3966934 prefixEnd_3966934 226327096295876398464601 := by
  unfold tailWord_3966934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042873088155193202119241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96457312940322060822605237 9042873088155193202119241)
  ·
    refine ⟨6782154816116394901589431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9042873088155193202119241 6782154816116394901589431)
    ·
      refine ⟨10173232224174592352384147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782154816116394901589431 10173232224174592352384147)
      ·
        refine ⟨15259848336261888528576221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10173232224174592352384147 15259848336261888528576221)
        ·
          refine ⟨5722443126098208198216083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15259848336261888528576221 5722443126098208198216083)
          ·
            refine ⟨8583664689147312297324125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722443126098208198216083 8583664689147312297324125)
            ·
              refine ⟨3218874258430242111496547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8583664689147312297324125 3218874258430242111496547)
              ·
                refine ⟨4828311387645363167244821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218874258430242111496547 4828311387645363167244821)
                ·
                  refine ⟨226327096295876398464601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4828311387645363167244821 226327096295876398464601)
                  ·
                    rfl

theorem cell23_3966934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3966934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966934 prefixEnd_3966934 := by exact prefixLift 3966934
  have htrace : WordTrace (prefixWord ++ tailWord_3966934) baseStart_3966934 baseEnd_3966934 := by
    simpa [prefixWord, tailWord_3966934, baseEnd_3966934] using wordTrace_append hprefix tailTrace_3966934
  have hstable : (prefixWord ++ tailWord_3966934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966934).length < 2 ^ (prefixWord ++ tailWord_3966934).sum := by decide
  have hdescent : baseEnd_3966934 < baseStart_3966934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966961 : List Nat := [1, 2, 2, 2, 5, 2, 1, 3, 1, 1, 3]
def baseStart_3966961 : Nat := 118140960795 + 3966961 * 2 ^ 59
def prefixEnd_3966961 : Nat := 4983230072969 + 3 ^ 40 * 3966961 * 2
def baseEnd_3966961 : Nat := 2036957730640558980543785

theorem tailTrace_3966961 : CollatzResearch.WordTrace tailWord_3966961 prefixEnd_3966961 2036957730640558980543785 := by
  unfold tailWord_3966961
  simp only [CollatzResearch.WordTrace]
  refine ⟨144686954181385274845140737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96457969454256849896760491 144686954181385274845140737)
  ·
    refine ⟨108515215636038956133855553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144686954181385274845140737 108515215636038956133855553)
    ·
      refine ⟨81386411727029217100391665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108515215636038956133855553 81386411727029217100391665)
      ·
        refine ⟨61039808795271912825293749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81386411727029217100391665 61039808795271912825293749)
        ·
          refine ⟨5722482074556741827371289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61039808795271912825293749 5722482074556741827371289)
          ·
            refine ⟨4291861555917556370528467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5722482074556741827371289 4291861555917556370528467)
            ·
              refine ⟨6437792333876334555792701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291861555917556370528467 6437792333876334555792701)
              ·
                refine ⟨2414172125203625458422263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6437792333876334555792701 2414172125203625458422263)
                ·
                  refine ⟨3621258187805438187633395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414172125203625458422263 3621258187805438187633395)
                  ·
                    refine ⟨5431887281708157281450093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3621258187805438187633395 5431887281708157281450093)
                    ·
                      refine ⟨2036957730640558980543785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5431887281708157281450093 2036957730640558980543785)
                      ·
                        rfl

theorem cell23_3966961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_3966961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966961 prefixEnd_3966961 := by exact prefixLift 3966961
  have htrace : WordTrace (prefixWord ++ tailWord_3966961) baseStart_3966961 baseEnd_3966961 := by
    simpa [prefixWord, tailWord_3966961, baseEnd_3966961] using wordTrace_append hprefix tailTrace_3966961
  have hstable : (prefixWord ++ tailWord_3966961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966961).length < 2 ^ (prefixWord ++ tailWord_3966961).sum := by decide
  have hdescent : baseEnd_3966961 < baseStart_3966961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966963 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4]
def baseStart_3966963 : Nat := 118140960795 + 3966963 * 2 ^ 59
def prefixEnd_3966963 : Nat := 4983230072969 + 3 ^ 40 * 3966963 * 2
def baseEnd_3966963 : Nat := 2036958757601867972718775

theorem tailTrace_3966963 : CollatzResearch.WordTrace tailWord_3966963 prefixEnd_3966963 2036958757601867972718775 := by
  unfold tailWord_3966963
  simp only [CollatzResearch.WordTrace]
  refine ⟨144687027127378029186713543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96458018084918686124475695 144687027127378029186713543)
  ·
    refine ⟨217030540691067043780070315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144687027127378029186713543 217030540691067043780070315)
    ·
      refine ⟨325545811036600565670105473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217030540691067043780070315 325545811036600565670105473)
      ·
        refine ⟨244159358277450424252579105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325545811036600565670105473 244159358277450424252579105)
        ·
          refine ⟨183119518708087818189434329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244159358277450424252579105 183119518708087818189434329)
          ·
            refine ⟨137339639031065863642075747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183119518708087818189434329 137339639031065863642075747)
            ·
              refine ⟨206009458546598795463113621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137339639031065863642075747 206009458546598795463113621)
              ·
                refine ⟨9656693369371818537333451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206009458546598795463113621 9656693369371818537333451)
                ·
                  refine ⟨14485040054057727806000177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9656693369371818537333451 14485040054057727806000177)
                  ·
                    refine ⟨10863780040543295854500133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14485040054057727806000177 10863780040543295854500133)
                    ·
                      refine ⟨2036958757601867972718775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10863780040543295854500133 2036958757601867972718775)
                      ·
                        rfl

theorem cell23_3966963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_3966963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3966963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3966963 prefixEnd_3966963 := by exact prefixLift 3966963
  have htrace : WordTrace (prefixWord ++ tailWord_3966963) baseStart_3966963 baseEnd_3966963 := by
    simpa [prefixWord, tailWord_3966963, baseEnd_3966963] using wordTrace_append hprefix tailTrace_3966963
  have hstable : (prefixWord ++ tailWord_3966963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966963).length < 2 ^ (prefixWord ++ tailWord_3966963).sum := by decide
  have hdescent : baseEnd_3966963 < baseStart_3966963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967000 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3967000 : Nat := 118140960795 + 3967000 * 2 ^ 59
def prefixEnd_3967000 : Nat := 4983230072969 + 3 ^ 40 * 3967000 * 2
def baseEnd_3967000 : Nat := 2036977756386084327956105

theorem tailTrace_3967000 : CollatzResearch.WordTrace tailWord_3967000 prefixEnd_3967000 2036977756386084327956105 := by
  unfold tailWord_3967000
  simp only [CollatzResearch.WordTrace]
  refine ⟨72344188314121992252905227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96458917752162656337206969 72344188314121992252905227)
  ·
    refine ⟨108516282471182988379357841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72344188314121992252905227 108516282471182988379357841)
    ·
      refine ⟨81387211853387241284518381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108516282471182988379357841 81387211853387241284518381)
      ·
        refine ⟨30520204445020215481694393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81387211853387241284518381 30520204445020215481694393)
        ·
          refine ⟨22890153333765161611270795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30520204445020215481694393 22890153333765161611270795)
          ·
            refine ⟨34335230000647742416906193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22890153333765161611270795 34335230000647742416906193)
            ·
              refine ⟨25751422500485806812679645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34335230000647742416906193 25751422500485806812679645)
              ·
                refine ⟨9656783437682177554754867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25751422500485806812679645 9656783437682177554754867)
                ·
                  refine ⟨14485175156523266332132301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9656783437682177554754867 14485175156523266332132301)
                  ·
                    refine ⟨5431940683696224874549613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14485175156523266332132301 5431940683696224874549613)
                    ·
                      refine ⟨2036977756386084327956105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5431940683696224874549613 2036977756386084327956105)
                      ·
                        rfl

theorem cell23_3967000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3967000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967000 prefixEnd_3967000 := by exact prefixLift 3967000
  have htrace : WordTrace (prefixWord ++ tailWord_3967000) baseStart_3967000 baseEnd_3967000 := by
    simpa [prefixWord, tailWord_3967000, baseEnd_3967000] using wordTrace_append hprefix tailTrace_3967000
  have hstable : (prefixWord ++ tailWord_3967000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967000).length < 2 ^ (prefixWord ++ tailWord_3967000).sum := by decide
  have hdescent : baseEnd_3967000 < baseStart_3967000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967004 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3967004 : Nat := 118140960795 + 3967004 * 2 ^ 59
def prefixEnd_3967004 : Nat := 4983230072969 + 3 ^ 40 * 3967004 * 2
def baseEnd_3967004 : Nat := 2036979810308702312306087

theorem tailTrace_3967004 : CollatzResearch.WordTrace tailWord_3967004 prefixEnd_3967004 2036979810308702312306087 := by
  unfold tailWord_3967004
  simp only [CollatzResearch.WordTrace]
  refine ⟨72344261260114746594478033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96459015013486328792637377 72344261260114746594478033)
  ·
    refine ⟨54258195945086059945858525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72344261260114746594478033 54258195945086059945858525)
    ·
      refine ⟨20346823479407272479696947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54258195945086059945858525 20346823479407272479696947)
      ·
        refine ⟨30520235219110908719545421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20346823479407272479696947 30520235219110908719545421)
        ·
          refine ⟨11445088207166590769829533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30520235219110908719545421 11445088207166590769829533)
          ·
            refine ⟨4291908077687471538686075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11445088207166590769829533 4291908077687471538686075)
            ·
              refine ⟨6437862116531207308029113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291908077687471538686075 6437862116531207308029113)
              ·
                refine ⟨4828396587398405481021835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6437862116531207308029113 4828396587398405481021835)
                ·
                  refine ⟨7242594881097608221532753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828396587398405481021835 7242594881097608221532753)
                  ·
                    refine ⟨5431946160823206166149565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7242594881097608221532753 5431946160823206166149565)
                    ·
                      refine ⟨2036979810308702312306087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5431946160823206166149565 2036979810308702312306087)
                      ·
                        rfl

theorem cell23_3967004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3967004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967004 prefixEnd_3967004 := by exact prefixLift 3967004
  have htrace : WordTrace (prefixWord ++ tailWord_3967004) baseStart_3967004 baseEnd_3967004 := by
    simpa [prefixWord, tailWord_3967004, baseEnd_3967004] using wordTrace_append hprefix tailTrace_3967004
  have hstable : (prefixWord ++ tailWord_3967004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967004).length < 2 ^ (prefixWord ++ tailWord_3967004).sum := by decide
  have hdescent : baseEnd_3967004 < baseStart_3967004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967027 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 1, 3, 2]
def baseStart_3967027 : Nat := 118140960795 + 3967027 * 2 ^ 59
def prefixEnd_3967027 : Nat := 4983230072969 + 3 ^ 40 * 3967027 * 2
def baseEnd_3967027 : Nat := 2036991620363755722318481

theorem tailTrace_3967027 : CollatzResearch.WordTrace tailWord_3967027 prefixEnd_3967027 2036991620363755722318481 := by
  unfold tailWord_3967027
  simp only [CollatzResearch.WordTrace]
  refine ⟨144689361399146168117043335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96459574266097445411362223 144689361399146168117043335)
  ·
    refine ⟨217034042098719252175565003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144689361399146168117043335 217034042098719252175565003)
    ·
      refine ⟨325551063148078878263347505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217034042098719252175565003 325551063148078878263347505)
      ·
        refine ⟨244163297361059158697510629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325551063148078878263347505 244163297361059158697510629)
        ·
          refine ⟨45780618255198592255783243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244163297361059158697510629 45780618255198592255783243)
          ·
            refine ⟨68670927382797888383674865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45780618255198592255783243 68670927382797888383674865)
            ·
              refine ⟨51503195537098416287756149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68670927382797888383674865 51503195537098416287756149)
              ·
                refine ⟨4828424581602976526977139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51503195537098416287756149 4828424581602976526977139)
                ·
                  refine ⟨7242636872404464790465709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828424581602976526977139 7242636872404464790465709)
                  ·
                    refine ⟨2715988827151674296424641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7242636872404464790465709 2715988827151674296424641)
                    ·
                      refine ⟨2036991620363755722318481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2715988827151674296424641 2036991620363755722318481)
                      ·
                        rfl

theorem cell23_3967027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 3, 2].length) (baseStart_3967027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967027 prefixEnd_3967027 := by exact prefixLift 3967027
  have htrace : WordTrace (prefixWord ++ tailWord_3967027) baseStart_3967027 baseEnd_3967027 := by
    simpa [prefixWord, tailWord_3967027, baseEnd_3967027] using wordTrace_append hprefix tailTrace_3967027
  have hstable : (prefixWord ++ tailWord_3967027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967027).length < 2 ^ (prefixWord ++ tailWord_3967027).sum := by decide
  have hdescent : baseEnd_3967027 < baseStart_3967027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967043 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5]
def baseStart_3967043 : Nat := 118140960795 + 3967043 * 2 ^ 59
def prefixEnd_3967043 : Nat := 4983230072969 + 3 ^ 40 * 3967043 * 2
def baseEnd_3967043 : Nat := 2036999836054227659718407

theorem tailTrace_3967043 : CollatzResearch.WordTrace tailWord_3967043 prefixEnd_3967043 2036999836054227659718407 := by
  unfold tailWord_3967043
  simp only [CollatzResearch.WordTrace]
  refine ⟨144689944967088202849625783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96459963311392135233083855 144689944967088202849625783)
  ·
    refine ⟨217034917450632304274438675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144689944967088202849625783 217034917450632304274438675)
    ·
      refine ⟨325552376175948456411658013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217034917450632304274438675 325552376175948456411658013)
      ·
        refine ⟨122082141065980671154371755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325552376175948456411658013 122082141065980671154371755)
        ·
          refine ⟨183123211598971006731557633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122082141065980671154371755 183123211598971006731557633)
          ·
            refine ⟨137342408699228255048668225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183123211598971006731557633 137342408699228255048668225)
            ·
              refine ⟨103006806524421191286501169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137342408699228255048668225 103006806524421191286501169)
              ·
                refine ⟨77255104893315893464875877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103006806524421191286501169 77255104893315893464875877)
                ·
                  refine ⟨14485332167496730024664227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77255104893315893464875877 14485332167496730024664227)
                  ·
                    refine ⟨21727998251245095036996341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14485332167496730024664227 21727998251245095036996341)
                    ·
                      refine ⟨2036999836054227659718407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21727998251245095036996341 2036999836054227659718407)
                      ·
                        rfl

theorem cell23_3967043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_3967043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967043 prefixEnd_3967043 := by exact prefixLift 3967043
  have htrace : WordTrace (prefixWord ++ tailWord_3967043) baseStart_3967043 baseEnd_3967043 := by
    simpa [prefixWord, tailWord_3967043, baseEnd_3967043] using wordTrace_append hprefix tailTrace_3967043
  have hstable : (prefixWord ++ tailWord_3967043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967043).length < 2 ^ (prefixWord ++ tailWord_3967043).sum := by decide
  have hdescent : baseEnd_3967043 < baseStart_3967043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967057 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 6, 2, 2]
def baseStart_3967057 : Nat := 118140960795 + 3967057 * 2 ^ 59
def prefixEnd_3967057 : Nat := 4983230072969 + 3 ^ 40 * 3967057 * 2
def baseEnd_3967057 : Nat := 2037007024783390604943343

theorem tailTrace_3967057 : CollatzResearch.WordTrace tailWord_3967057 prefixEnd_3967057 2037007024783390604943343 := by
  unfold tailWord_3967057
  simp only [CollatzResearch.WordTrace]
  refine ⟨144690455589037483240635425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96460303726024988827090283 144690455589037483240635425)
  ·
    refine ⟨108517841691778112430476569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144690455589037483240635425 108517841691778112430476569)
    ·
      refine ⟨81388381268833584322857427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108517841691778112430476569 81388381268833584322857427)
      ·
        refine ⟨122082571903250376484286141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81388381268833584322857427 122082571903250376484286141)
        ·
          refine ⟨45780964463718891181607303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122082571903250376484286141 45780964463718891181607303)
          ·
            refine ⟨68671446695578336772410955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45780964463718891181607303 68671446695578336772410955)
            ·
              refine ⟨103007170043367505158616433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68671446695578336772410955 103007170043367505158616433)
              ·
                refine ⟨77255377532525628868962325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103007170043367505158616433 77255377532525628868962325)
                ·
                  refine ⟨3621345821837138853232609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77255377532525628868962325 3621345821837138853232609)
                  ·
                    refine ⟨2716009366377854139924457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3621345821837138853232609 2716009366377854139924457)
                    ·
                      refine ⟨2037007024783390604943343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2716009366377854139924457 2037007024783390604943343)
                      ·
                        rfl

theorem cell23_3967057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_3967057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967057 prefixEnd_3967057 := by exact prefixLift 3967057
  have htrace : WordTrace (prefixWord ++ tailWord_3967057) baseStart_3967057 baseEnd_3967057 := by
    simpa [prefixWord, tailWord_3967057, baseEnd_3967057] using wordTrace_append hprefix tailTrace_3967057
  have hstable : (prefixWord ++ tailWord_3967057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967057).length < 2 ^ (prefixWord ++ tailWord_3967057).sum := by decide
  have hdescent : baseEnd_3967057 < baseStart_3967057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967060 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_3967060 : Nat := 118140960795 + 3967060 * 2 ^ 59
def prefixEnd_3967060 : Nat := 4983230072969 + 3 ^ 40 * 3967060 * 2
def baseEnd_3967060 : Nat := 2037008565225354093205829

theorem tailTrace_3967060 : CollatzResearch.WordTrace tailWord_3967060 prefixEnd_3967060 2037008565225354093205829 := by
  unfold tailWord_3967060
  simp only [CollatzResearch.WordTrace]
  refine ⟨72345282504013307376497317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96460376672017743168663089 72345282504013307376497317)
  ·
    refine ⟨13564740469502495133093247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72345282504013307376497317 13564740469502495133093247)
    ·
      refine ⟨20347110704253742699639871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13564740469502495133093247 20347110704253742699639871)
      ·
        refine ⟨30520666056380614049459807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20347110704253742699639871 30520666056380614049459807)
        ·
          refine ⟨45780999084570921074189711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30520666056380614049459807 45780999084570921074189711)
          ·
            refine ⟨68671498626856381611284567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45780999084570921074189711 68671498626856381611284567)
            ·
              refine ⟨103007247940284572416926851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68671498626856381611284567 103007247940284572416926851)
              ·
                refine ⟨154510871910426858625390277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103007247940284572416926851 154510871910426858625390277)
                ·
                  refine ⟨28970788483205035992260677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154510871910426858625390277 28970788483205035992260677)
                  ·
                    refine ⟨5432022840600944248548877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28970788483205035992260677 5432022840600944248548877)
                    ·
                      refine ⟨2037008565225354093205829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5432022840600944248548877 2037008565225354093205829)
                      ·
                        rfl

theorem cell23_3967060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_3967060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967060 prefixEnd_3967060 := by exact prefixLift 3967060
  have htrace : WordTrace (prefixWord ++ tailWord_3967060) baseStart_3967060 baseEnd_3967060 := by
    simpa [prefixWord, tailWord_3967060, baseEnd_3967060] using wordTrace_append hprefix tailTrace_3967060
  have hstable : (prefixWord ++ tailWord_3967060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967060).length < 2 ^ (prefixWord ++ tailWord_3967060).sum := by decide
  have hdescent : baseEnd_3967060 < baseStart_3967060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967063 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 9]
def baseStart_3967063 : Nat := 118140960795 + 3967063 * 2 ^ 59
def prefixEnd_3967063 : Nat := 4983230072969 + 3 ^ 40 * 3967063 * 2
def baseEnd_3967063 : Nat := 226334456185257509052035

theorem tailTrace_3967063 : CollatzResearch.WordTrace tailWord_3967063 prefixEnd_3967063 226334456185257509052035 := by
  unfold tailWord_3967063
  simp only [CollatzResearch.WordTrace]
  refine ⟨144690674427015746265353843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96460449618010497510235895 144690674427015746265353843)
  ·
    refine ⟨217036011640523619398030765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144690674427015746265353843 217036011640523619398030765)
    ·
      refine ⟨81388504365196357274261537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217036011640523619398030765 81388504365196357274261537)
      ·
        refine ⟨61041378273897267955696153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81388504365196357274261537 61041378273897267955696153)
        ·
          refine ⟨45781033705422950966772115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61041378273897267955696153 45781033705422950966772115)
          ·
            refine ⟨68671550558134426450158173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45781033705422950966772115 68671550558134426450158173)
            ·
              refine ⟨25751831459300409918809315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68671550558134426450158173 25751831459300409918809315)
              ·
                refine ⟨38627747188950614878213973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25751831459300409918809315 38627747188950614878213973)
                ·
                  refine ⟨226334456185257509052035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38627747188950614878213973 226334456185257509052035)
                  ·
                    rfl

theorem cell23_3967063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 9].length) (baseStart_3967063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967063 prefixEnd_3967063 := by exact prefixLift 3967063
  have htrace : WordTrace (prefixWord ++ tailWord_3967063) baseStart_3967063 baseEnd_3967063 := by
    simpa [prefixWord, tailWord_3967063, baseEnd_3967063] using wordTrace_append hprefix tailTrace_3967063
  have hstable : (prefixWord ++ tailWord_3967063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967063).length < 2 ^ (prefixWord ++ tailWord_3967063).sum := by decide
  have hdescent : baseEnd_3967063 < baseStart_3967063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967073 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3967073 : Nat := 118140960795 + 3967073 * 2 ^ 59
def prefixEnd_3967073 : Nat := 4983230072969 + 3 ^ 40 * 3967073 * 2
def baseEnd_3967073 : Nat := 2037015240473862542343269

theorem tailTrace_3967073 : CollatzResearch.WordTrace tailWord_3967073 prefixEnd_3967073 2037015240473862542343269 := by
  unfold tailWord_3967073
  simp only [CollatzResearch.WordTrace]
  refine ⟨144691039156979517973217873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96460692771319678648811915 144691039156979517973217873)
  ·
    refine ⟨108518279367734638479913405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144691039156979517973217873 108518279367734638479913405)
    ·
      refine ⟨40694354762900489429967527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108518279367734638479913405 40694354762900489429967527)
      ·
        refine ⟨61041532144350734144951291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40694354762900489429967527 61041532144350734144951291)
        ·
          refine ⟨91562298216526101217426937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61041532144350734144951291 91562298216526101217426937)
          ·
            refine ⟨68671723662394575913070203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91562298216526101217426937 68671723662394575913070203)
            ·
              refine ⟨103007585493591863869605305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68671723662394575913070203 103007585493591863869605305)
              ·
                refine ⟨77255689120193897902203979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103007585493591863869605305 77255689120193897902203979)
                ·
                  refine ⟨115883533680290846853305969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77255689120193897902203979 115883533680290846853305969)
                  ·
                    refine ⟨86912650260218135139979477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115883533680290846853305969 86912650260218135139979477)
                    ·
                      refine ⟨2037015240473862542343269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86912650260218135139979477 2037015240473862542343269)
                      ·
                        rfl

theorem cell23_3967073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3967073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3967073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3967073 prefixEnd_3967073 := by exact prefixLift 3967073
  have htrace : WordTrace (prefixWord ++ tailWord_3967073) baseStart_3967073 baseEnd_3967073 := by
    simpa [prefixWord, tailWord_3967073, baseEnd_3967073] using wordTrace_append hprefix tailTrace_3967073
  have hstable : (prefixWord ++ tailWord_3967073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967073).length < 2 ^ (prefixWord ++ tailWord_3967073).sum := by decide
  have hdescent : baseEnd_3967073 < baseStart_3967073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
