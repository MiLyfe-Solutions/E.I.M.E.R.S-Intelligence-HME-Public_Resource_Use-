import V185TrunkScan23Chunk1205

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7144313 : List Nat := [1, 2, 1, 3, 2, 3, 4, 2, 1, 1, 3]
def baseStart_7144313 : Nat := 118140960795 + 7144313 * 2 ^ 59
def prefixEnd_7144313 : Nat := 4983230072969 + 3 ^ 40 * 7144313 * 2
def baseEnd_7144313 : Nat := 3668466515165011576231409

theorem tailTrace_7144313 : CollatzResearch.WordTrace tailWord_7144313 prefixEnd_7144313 3668466515165011576231409 := by
  unfold tailWord_7144313
  simp only [CollatzResearch.WordTrace]
  refine ⟨260574502166381627364285593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173716334777587751576190395 260574502166381627364285593)
  ·
    refine ⟨195430876624786220523214195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260574502166381627364285593 195430876624786220523214195)
    ·
      refine ⟨293146314937179330784821293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195430876624786220523214195 293146314937179330784821293)
      ·
        refine ⟨109929868101442249044307985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293146314937179330784821293 109929868101442249044307985)
        ·
          refine ⟨82447401076081686783230989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109929868101442249044307985 82447401076081686783230989)
          ·
            refine ⟨30917775403530632543711621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82447401076081686783230989 30917775403530632543711621)
            ·
              refine ⟨5797082888161993601945929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30917775403530632543711621 5797082888161993601945929)
              ·
                refine ⟨4347812166121495201459447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797082888161993601945929 4347812166121495201459447)
                ·
                  refine ⟨6521718249182242802189171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347812166121495201459447 6521718249182242802189171)
                  ·
                    refine ⟨9782577373773364203283757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6521718249182242802189171 9782577373773364203283757)
                    ·
                      refine ⟨3668466515165011576231409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9782577373773364203283757 3668466515165011576231409)
                      ·
                        rfl

theorem cell23_7144313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_7144313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144313 prefixEnd_7144313 := by exact prefixLift 7144313
  have htrace : WordTrace (prefixWord ++ tailWord_7144313) baseStart_7144313 baseEnd_7144313 := by
    simpa [prefixWord, tailWord_7144313, baseEnd_7144313] using wordTrace_append hprefix tailTrace_7144313
  have hstable : (prefixWord ++ tailWord_7144313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144313).length < 2 ^ (prefixWord ++ tailWord_7144313).sum := by decide
  have hdescent : baseEnd_7144313 < baseStart_7144313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144315 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6]
def baseStart_7144315 : Nat := 118140960795 + 7144315 * 2 ^ 59
def prefixEnd_7144315 : Nat := 4983230072969 + 3 ^ 40 * 7144315 * 2
def baseEnd_7144315 : Nat := 3668467542126320568406399

theorem tailTrace_7144315 : CollatzResearch.WordTrace tailWord_7144315 prefixEnd_7144315 3668467542126320568406399 := by
  unfold tailWord_7144315
  simp only [CollatzResearch.WordTrace]
  refine ⟨260574575112374381705858399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173716383408249587803905599 260574575112374381705858399)
  ·
    refine ⟨390861862668561572558787599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260574575112374381705858399 390861862668561572558787599)
    ·
      refine ⟨586292794002842358838181399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390861862668561572558787599 586292794002842358838181399)
      ·
        refine ⟨879439191004263538257272099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586292794002842358838181399 879439191004263538257272099)
        ·
          refine ⟨1319158786506395307385908149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879439191004263538257272099 1319158786506395307385908149)
          ·
            refine ⟨123671136234974560067428889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1319158786506395307385908149 123671136234974560067428889)
            ·
              refine ⟨92753352176230920050571667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123671136234974560067428889 92753352176230920050571667)
              ·
                refine ⟨139130028264346380075857501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92753352176230920050571667 139130028264346380075857501)
                ·
                  refine ⟨52173760599129892528446563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139130028264346380075857501 52173760599129892528446563)
                  ·
                    refine ⟨78260640898694838792669845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52173760599129892528446563 78260640898694838792669845)
                    ·
                      refine ⟨3668467542126320568406399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78260640898694838792669845 3668467542126320568406399)
                      ·
                        rfl

theorem cell23_7144315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_7144315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144315 prefixEnd_7144315 := by exact prefixLift 7144315
  have htrace : WordTrace (prefixWord ++ tailWord_7144315) baseStart_7144315 baseEnd_7144315 := by
    simpa [prefixWord, tailWord_7144315, baseEnd_7144315] using wordTrace_append hprefix tailTrace_7144315
  have hstable : (prefixWord ++ tailWord_7144315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144315).length < 2 ^ (prefixWord ++ tailWord_7144315).sum := by decide
  have hdescent : baseEnd_7144315 < baseStart_7144315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144329 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 2, 4]
def baseStart_7144329 : Nat := 118140960795 + 7144329 * 2 ^ 59
def prefixEnd_7144329 : Nat := 4983230072969 + 3 ^ 40 * 7144329 * 2
def baseEnd_7144329 : Nat := 1222824910285161171210445

theorem tailTrace_7144329 : CollatzResearch.WordTrace tailWord_7144329 prefixEnd_7144329 1222824910285161171210445 := by
  unfold tailWord_7144329
  simp only [CollatzResearch.WordTrace]
  refine ⟨260575085734323662096868041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173716723822882441397912027 260575085734323662096868041)
  ·
    refine ⟨195431314300742746572651031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260575085734323662096868041 195431314300742746572651031)
    ·
      refine ⟨293146971451114119858976547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195431314300742746572651031 293146971451114119858976547)
      ·
        refine ⟨439720457176671179788464821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293146971451114119858976547 439720457176671179788464821)
        ·
          refine ⟨41223792860312923105168577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 439720457176671179788464821 41223792860312923105168577)
          ·
            refine ⟨30917844645234692328876433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41223792860312923105168577 30917844645234692328876433)
            ·
              refine ⟨23188383483926019246657325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30917844645234692328876433 23188383483926019246657325)
              ·
                refine ⟨8695643806472257217496497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23188383483926019246657325 8695643806472257217496497)
                ·
                  refine ⟨6521732854854192913122373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8695643806472257217496497 6521732854854192913122373)
                  ·
                    refine ⟨1222824910285161171210445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6521732854854192913122373 1222824910285161171210445)
                    ·
                      rfl

theorem cell23_7144329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_7144329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144329 prefixEnd_7144329 := by exact prefixLift 7144329
  have htrace : WordTrace (prefixWord ++ tailWord_7144329) baseStart_7144329 baseEnd_7144329 := by
    simpa [prefixWord, tailWord_7144329, baseEnd_7144329] using wordTrace_append hprefix tailTrace_7144329
  have hstable : (prefixWord ++ tailWord_7144329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144329).length < 2 ^ (prefixWord ++ tailWord_7144329).sum := by decide
  have hdescent : baseEnd_7144329 < baseStart_7144329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144332 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7144332 : Nat := 118140960795 + 7144332 * 2 ^ 59
def prefixEnd_7144332 : Nat := 4983230072969 + 3 ^ 40 * 7144332 * 2
def baseEnd_7144332 : Nat := 3668476271297447001893821

theorem tailTrace_7144332 : CollatzResearch.WordTrace tailWord_7144332 prefixEnd_7144332 3668476271297447001893821 := by
  unfold tailWord_7144332
  simp only [CollatzResearch.WordTrace]
  refine ⟨130287597576656396804613625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173716796768875195739484833 130287597576656396804613625)
  ·
    refine ⟨97715698182492297603460219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130287597576656396804613625 97715698182492297603460219)
    ·
      refine ⟨146573547273738446405190329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97715698182492297603460219 146573547273738446405190329)
      ·
        refine ⟨109930160455303834803892747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146573547273738446405190329 109930160455303834803892747)
        ·
          refine ⟨164895240682955752205839121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109930160455303834803892747 164895240682955752205839121)
          ·
            refine ⟨123671430512216814154379341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164895240682955752205839121 123671430512216814154379341)
            ·
              refine ⟨46376786442081305307892253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123671430512216814154379341 46376786442081305307892253)
              ·
                refine ⟨17391294915780489490459595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46376786442081305307892253 17391294915780489490459595)
                ·
                  refine ⟨26086942373670734235689393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17391294915780489490459595 26086942373670734235689393)
                  ·
                    refine ⟨19565206780253050676767045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26086942373670734235689393 19565206780253050676767045)
                    ·
                      refine ⟨3668476271297447001893821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19565206780253050676767045 3668476271297447001893821)
                      ·
                        rfl

theorem cell23_7144332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7144332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144332 prefixEnd_7144332 := by exact prefixLift 7144332
  have htrace : WordTrace (prefixWord ++ tailWord_7144332) baseStart_7144332 baseEnd_7144332 := by
    simpa [prefixWord, tailWord_7144332, baseEnd_7144332] using wordTrace_append hprefix tailTrace_7144332
  have hstable : (prefixWord ++ tailWord_7144332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144332).length < 2 ^ (prefixWord ++ tailWord_7144332).sum := by decide
  have hdescent : baseEnd_7144332 < baseStart_7144332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144353 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7144353 : Nat := 118140960795 + 7144353 * 2 ^ 59
def prefixEnd_7144353 : Nat := 4983230072969 + 3 ^ 40 * 7144353 * 2
def baseEnd_7144353 : Nat := 3668487054391191419731225

theorem tailTrace_7144353 : CollatzResearch.WordTrace tailWord_7144353 prefixEnd_7144353 3668487054391191419731225 := by
  unfold tailWord_7144353
  simp only [CollatzResearch.WordTrace]
  refine ⟨260575961086236714195741713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173717307390824476130494475 260575961086236714195741713)
  ·
    refine ⟨195431970814677535646806285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260575961086236714195741713 195431970814677535646806285)
    ·
      refine ⟨73286989055504075867552357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195431970814677535646806285 73286989055504075867552357)
      ·
        refine ⟨13741310447907014225166067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73286989055504075867552357 13741310447907014225166067)
        ·
          refine ⟨20611965671860521337749101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13741310447907014225166067 20611965671860521337749101)
          ·
            refine ⟨7729487126947695501655913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20611965671860521337749101 7729487126947695501655913)
            ·
              refine ⟨5797115345210771626241935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7729487126947695501655913 5797115345210771626241935)
              ·
                refine ⟨8695673017816157439362903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797115345210771626241935 8695673017816157439362903)
                ·
                  refine ⟨13043509526724236159044355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8695673017816157439362903 13043509526724236159044355)
                  ·
                    refine ⟨19565264290086354238566533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13043509526724236159044355 19565264290086354238566533)
                    ·
                      refine ⟨3668487054391191419731225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19565264290086354238566533 3668487054391191419731225)
                      ·
                        rfl

theorem cell23_7144353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7144353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144353 prefixEnd_7144353 := by exact prefixLift 7144353
  have htrace : WordTrace (prefixWord ++ tailWord_7144353) baseStart_7144353 baseEnd_7144353 := by
    simpa [prefixWord, tailWord_7144353, baseEnd_7144353] using wordTrace_append hprefix tailTrace_7144353
  have hstable : (prefixWord ++ tailWord_7144353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144353).length < 2 ^ (prefixWord ++ tailWord_7144353).sum := by decide
  have hdescent : baseEnd_7144353 < baseStart_7144353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144413 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_7144413 : Nat := 118140960795 + 7144413 * 2 ^ 59
def prefixEnd_7144413 : Nat := 4983230072969 + 3 ^ 40 * 7144413 * 2
def baseEnd_7144413 : Nat := 3668517863230461184980949

theorem tailTrace_7144413 : CollatzResearch.WordTrace tailWord_7144413 prefixEnd_7144413 3668517863230461184980949 := by
  unfold tailWord_7144413
  simp only [CollatzResearch.WordTrace]
  refine ⟨260578149466019344442925893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173718766310679562961950595 260578149466019344442925893)
  ·
    refine ⟨48858403024878627083048605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260578149466019344442925893 48858403024878627083048605)
    ·
      refine ⟨18321901134329485156143227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48858403024878627083048605 18321901134329485156143227)
      ·
        refine ⟨27482851701494227734214841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18321901134329485156143227 27482851701494227734214841)
        ·
          refine ⟨20612138776120670800661131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27482851701494227734214841 20612138776120670800661131)
          ·
            refine ⟨30918208164181006200991697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20612138776120670800661131 30918208164181006200991697)
            ·
              refine ⟨23188656123135754650743773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30918208164181006200991697 23188656123135754650743773)
              ·
                refine ⟨8695746046175907994028915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23188656123135754650743773 8695746046175907994028915)
                ·
                  refine ⟨13043619069263861991043373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8695746046175907994028915 13043619069263861991043373)
                  ·
                    refine ⟨4891357150973948246641265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13043619069263861991043373 4891357150973948246641265)
                    ·
                      refine ⟨3668517863230461184980949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891357150973948246641265 3668517863230461184980949)
                      ·
                        rfl

theorem cell23_7144413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_7144413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144413 prefixEnd_7144413 := by exact prefixLift 7144413
  have htrace : WordTrace (prefixWord ++ tailWord_7144413) baseStart_7144413 baseEnd_7144413 := by
    simpa [prefixWord, tailWord_7144413, baseEnd_7144413] using wordTrace_append hprefix tailTrace_7144413
  have hstable : (prefixWord ++ tailWord_7144413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144413).length < 2 ^ (prefixWord ++ tailWord_7144413).sum := by decide
  have hdescent : baseEnd_7144413 < baseStart_7144413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144479 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 2, 5]
def baseStart_7144479 : Nat := 118140960795 + 7144479 * 2 ^ 59
def prefixEnd_7144479 : Nat := 4983230072969 + 3 ^ 40 * 7144479 * 2
def baseEnd_7144479 : Nat := 1222850584317885975585215

theorem tailTrace_7144479 : CollatzResearch.WordTrace tailWord_7144479 prefixEnd_7144479 1222850584317885975585215 := by
  unfold tailWord_7144479
  simp only [CollatzResearch.WordTrace]
  refine ⟨260580556683780237714828491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173720371122520158476552327 260580556683780237714828491)
  ·
    refine ⟨390870835025670356572242737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260580556683780237714828491 390870835025670356572242737)
    ·
      refine ⟨293153126269252767429182053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390870835025670356572242737 293153126269252767429182053)
      ·
        refine ⟨54966211175484893892971635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293153126269252767429182053 54966211175484893892971635)
        ·
          refine ⟨82449316763227340839457453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54966211175484893892971635 82449316763227340839457453)
          ·
            refine ⟨30918493786210252814796545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82449316763227340839457453 30918493786210252814796545)
            ·
              refine ⟨23188870339657689611097409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30918493786210252814796545 23188870339657689611097409)
              ·
                refine ⟨17391652754743267208323057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23188870339657689611097409 17391652754743267208323057)
                ·
                  refine ⟨13043739566057450406242293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17391652754743267208323057 13043739566057450406242293)
                  ·
                    refine ⟨1222850584317885975585215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13043739566057450406242293 1222850584317885975585215)
                    ·
                      rfl

theorem cell23_7144479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_7144479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144479 prefixEnd_7144479 := by exact prefixLift 7144479
  have htrace : WordTrace (prefixWord ++ tailWord_7144479) baseStart_7144479 baseEnd_7144479 := by
    simpa [prefixWord, tailWord_7144479, baseEnd_7144479] using wordTrace_append hprefix tailTrace_7144479
  have hstable : (prefixWord ++ tailWord_7144479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144479).length < 2 ^ (prefixWord ++ tailWord_7144479).sum := by decide
  have hdescent : baseEnd_7144479 < baseStart_7144479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144483 : List Nat := [1, 1, 1, 4, 3, 4, 2, 2, 5]
def baseStart_7144483 : Nat := 118140960795 + 7144483 * 2 ^ 59
def prefixEnd_7144483 : Nat := 4983230072969 + 3 ^ 40 * 7144483 * 2
def baseEnd_7144483 : Nat := 407617089652919545678403

theorem tailTrace_7144483 : CollatzResearch.WordTrace tailWord_7144483 prefixEnd_7144483 407617089652919545678403 := by
  unfold tailWord_7144483
  simp only [CollatzResearch.WordTrace]
  refine ⟨260580702575765746397974103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173720468383843830931982735 260580702575765746397974103)
  ·
    refine ⟨390871053863648619596961155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260580702575765746397974103 390871053863648619596961155)
    ·
      refine ⟨586306580795472929395441733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390871053863648619596961155 586306580795472929395441733)
      ·
        refine ⟨109932483899151174261645325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 586306580795472929395441733 109932483899151174261645325)
        ·
          refine ⟨41224681462181690348116997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109932483899151174261645325 41224681462181690348116997)
          ·
            refine ⟨7729627774159066940271937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41224681462181690348116997 7729627774159066940271937)
            ·
              refine ⟨5797220830619300205203953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7729627774159066940271937 5797220830619300205203953)
              ·
                refine ⟨4347915622964475153902965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797220830619300205203953 4347915622964475153902965)
                ·
                  refine ⟨407617089652919545678403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4347915622964475153902965 407617089652919545678403)
                  ·
                    rfl

theorem cell23_7144483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 5].length) (baseStart_7144483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144483 prefixEnd_7144483 := by exact prefixLift 7144483
  have htrace : WordTrace (prefixWord ++ tailWord_7144483) baseStart_7144483 baseEnd_7144483 := by
    simpa [prefixWord, tailWord_7144483, baseEnd_7144483] using wordTrace_append hprefix tailTrace_7144483
  have hstable : (prefixWord ++ tailWord_7144483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144483).length < 2 ^ (prefixWord ++ tailWord_7144483).sum := by decide
  have hdescent : baseEnd_7144483 < baseStart_7144483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144513 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7144513 : Nat := 118140960795 + 7144513 * 2 ^ 59
def prefixEnd_7144513 : Nat := 4983230072969 + 3 ^ 40 * 7144513 * 2
def baseEnd_7144513 : Nat := 1222856403765303597910163

theorem tailTrace_7144513 : CollatzResearch.WordTrace tailWord_7144513 prefixEnd_7144513 1222856403765303597910163 := by
  unfold tailWord_7144513
  simp only [CollatzResearch.WordTrace]
  refine ⟨260581796765657061521566193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173721197843771374347710795 260581796765657061521566193)
  ·
    refine ⟨195436347574242796141174645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260581796765657061521566193 195436347574242796141174645)
    ·
      refine ⟨18322157585085262138235123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195436347574242796141174645 18322157585085262138235123)
      ·
        refine ⟨27483236377627893207352685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18322157585085262138235123 27483236377627893207352685)
        ·
          refine ⟨10306213641610459952757257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27483236377627893207352685 10306213641610459952757257)
          ·
            refine ⟨7729660231207844964567943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10306213641610459952757257 7729660231207844964567943)
            ·
              refine ⟨11594490346811767446851915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7729660231207844964567943 11594490346811767446851915)
              ·
                refine ⟨17391735520217651170277873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11594490346811767446851915 17391735520217651170277873)
                ·
                  refine ⟨13043801640163238377708405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17391735520217651170277873 13043801640163238377708405)
                  ·
                    refine ⟨1222856403765303597910163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13043801640163238377708405 1222856403765303597910163)
                    ·
                      rfl

theorem cell23_7144513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7144513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144513 prefixEnd_7144513 := by exact prefixLift 7144513
  have htrace : WordTrace (prefixWord ++ tailWord_7144513) baseStart_7144513 baseEnd_7144513 := by
    simpa [prefixWord, tailWord_7144513, baseEnd_7144513] using wordTrace_append hprefix tailTrace_7144513
  have hstable : (prefixWord ++ tailWord_7144513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144513).length < 2 ^ (prefixWord ++ tailWord_7144513).sum := by decide
  have hdescent : baseEnd_7144513 < baseStart_7144513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144556 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 6]
def baseStart_7144556 : Nat := 118140960795 + 7144556 * 2 ^ 59
def prefixEnd_7144556 : Nat := 4983230072969 + 3 ^ 40 * 7144556 * 2
def baseEnd_7144556 : Nat := 407621254551561569499199

theorem tailTrace_7144556 : CollatzResearch.WordTrace tailWord_7144556 prefixEnd_7144556 407621254551561569499199 := by
  unfold tailWord_7144556
  simp only [CollatzResearch.WordTrace]
  refine ⟨130291682552250639932690761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173722243403000853243587681 130291682552250639932690761)
  ·
    refine ⟨97718761914187979949518071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130291682552250639932690761 97718761914187979949518071)
    ·
      refine ⟨146578142871281969924277107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97718761914187979949518071 146578142871281969924277107)
      ·
        refine ⟨219867214306922954886415661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146578142871281969924277107 219867214306922954886415661)
        ·
          refine ⟨82450205365096108082405873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219867214306922954886415661 82450205365096108082405873)
          ·
            refine ⟨61837654023822081061804405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82450205365096108082405873 61837654023822081061804405)
            ·
              refine ⟨5797280064733320099544163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61837654023822081061804405 5797280064733320099544163)
              ·
                refine ⟨8695920097099980149316245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797280064733320099544163 8695920097099980149316245)
                ·
                  refine ⟨407621254551561569499199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8695920097099980149316245 407621254551561569499199)
                  ·
                    rfl

theorem cell23_7144556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_7144556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144556 prefixEnd_7144556 := by exact prefixLift 7144556
  have htrace : WordTrace (prefixWord ++ tailWord_7144556) baseStart_7144556 baseEnd_7144556 := by
    simpa [prefixWord, tailWord_7144556, baseEnd_7144556] using wordTrace_append hprefix tailTrace_7144556
  have hstable : (prefixWord ++ tailWord_7144556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144556).length < 2 ^ (prefixWord ++ tailWord_7144556).sum := by decide
  have hdescent : baseEnd_7144556 < baseStart_7144556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144566 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7144566 : Nat := 118140960795 + 7144566 * 2 ^ 59
def prefixEnd_7144566 : Nat := 4983230072969 + 3 ^ 40 * 7144566 * 2
def baseEnd_7144566 : Nat := 3668596425770599086367745

theorem tailTrace_7144566 : CollatzResearch.WordTrace tailWord_7144566 prefixEnd_7144566 3668596425770599086367745 := by
  unfold tailWord_7144566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16286483114654065723327847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173722486556310034382163701 16286483114654065723327847)
  ·
    refine ⟨24429724671981098584991771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16286483114654065723327847 24429724671981098584991771)
    ·
      refine ⟨36644587007971647877487657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24429724671981098584991771 36644587007971647877487657)
      ·
        refine ⟨27483440255978735908115743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36644587007971647877487657 27483440255978735908115743)
        ·
          refine ⟨41225160383968103862173615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27483440255978735908115743 41225160383968103862173615)
          ·
            refine ⟨61837740575952155793260423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41225160383968103862173615 61837740575952155793260423)
            ·
              refine ⟨92756610863928233689890635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61837740575952155793260423 92756610863928233689890635)
              ·
                refine ⟨139134916295892350534835953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92756610863928233689890635 139134916295892350534835953)
                ·
                  refine ⟨104351187221919262901126965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139134916295892350534835953 104351187221919262901126965)
                  ·
                    refine ⟨9782923802054930896980653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104351187221919262901126965 9782923802054930896980653)
                    ·
                      refine ⟨3668596425770599086367745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9782923802054930896980653 3668596425770599086367745)
                      ·
                        rfl

theorem cell23_7144566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7144566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144566 prefixEnd_7144566 := by exact prefixLift 7144566
  have htrace : WordTrace (prefixWord ++ tailWord_7144566) baseStart_7144566 baseEnd_7144566 := by
    simpa [prefixWord, tailWord_7144566, baseEnd_7144566] using wordTrace_append hprefix tailTrace_7144566
  have hstable : (prefixWord ++ tailWord_7144566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144566).length < 2 ^ (prefixWord ++ tailWord_7144566).sum := by decide
  have hdescent : baseEnd_7144566 < baseStart_7144566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144576 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 1, 5, 2]
def baseStart_7144576 : Nat := 118140960795 + 7144576 * 2 ^ 59
def prefixEnd_7144576 : Nat := 4983230072969 + 3 ^ 40 * 7144576 * 2
def baseEnd_7144576 : Nat := 3668601560577144047242699

theorem tailTrace_7144576 : CollatzResearch.WordTrace tailWord_7144576 prefixEnd_7144576 3668601560577144047242699 := by
  unfold tailWord_7144576
  simp only [CollatzResearch.WordTrace]
  refine ⟨130292047282214411640554791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173722729709619215520739721 130292047282214411640554791)
  ·
    refine ⟨195438070923321617460832187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130292047282214411640554791 195438070923321617460832187)
    ·
      refine ⟨293157106384982426191248281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195438070923321617460832187 293157106384982426191248281)
      ·
        refine ⟨219867829788736819643436211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293157106384982426191248281 219867829788736819643436211)
        ·
          refine ⟨329801744683105229465154317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219867829788736819643436211 329801744683105229465154317)
          ·
            refine ⟨123675654256164461049432869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329801744683105229465154317 123675654256164461049432869)
            ·
              refine ⟨23189185173030836446768663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123675654256164461049432869 23189185173030836446768663)
              ·
                refine ⟨34783777759546254670152995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23189185173030836446768663 34783777759546254670152995)
                ·
                  refine ⟨52175666639319382005229493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34783777759546254670152995 52175666639319382005229493)
                  ·
                    refine ⟨4891468747436192062990265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52175666639319382005229493 4891468747436192062990265)
                    ·
                      refine ⟨3668601560577144047242699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891468747436192062990265 3668601560577144047242699)
                      ·
                        rfl

theorem cell23_7144576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_7144576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144576 prefixEnd_7144576 := by exact prefixLift 7144576
  have htrace : WordTrace (prefixWord ++ tailWord_7144576) baseStart_7144576 baseEnd_7144576 := by
    simpa [prefixWord, tailWord_7144576, baseEnd_7144576] using wordTrace_append hprefix tailTrace_7144576
  have hstable : (prefixWord ++ tailWord_7144576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144576).length < 2 ^ (prefixWord ++ tailWord_7144576).sum := by decide
  have hdescent : baseEnd_7144576 < baseStart_7144576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144586 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_7144586 : Nat := 118140960795 + 7144586 * 2 ^ 59
def prefixEnd_7144586 : Nat := 4983230072969 + 3 ^ 40 * 7144586 * 2
def baseEnd_7144586 : Nat := 1222868898461229669372551

theorem tailTrace_7144586 : CollatzResearch.WordTrace tailWord_7144586 prefixEnd_7144586 1222868898461229669372551 := by
  unfold tailWord_7144586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65146114823598148747243403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173722972862928396659315741 65146114823598148747243403)
  ·
    refine ⟨97719172235397223120865105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65146114823598148747243403 97719172235397223120865105)
    ·
      refine ⟨73289379176547917340648829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97719172235397223120865105 73289379176547917340648829)
      ·
        refine ⟨27483517191205469002743311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73289379176547917340648829 27483517191205469002743311)
        ·
          refine ⟨41225275786808203504114967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27483517191205469002743311 41225275786808203504114967)
          ·
            refine ⟨61837913680212305256172451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41225275786808203504114967 61837913680212305256172451)
            ·
              refine ⟨92756870520318457884258677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61837913680212305256172451 92756870520318457884258677)
              ·
                refine ⟨8695956611279855426649251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92756870520318457884258677 8695956611279855426649251)
                ·
                  refine ⟨13043934916919783139973877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8695956611279855426649251 13043934916919783139973877)
                  ·
                    refine ⟨1222868898461229669372551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13043934916919783139973877 1222868898461229669372551)
                    ·
                      rfl

theorem cell23_7144586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_7144586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144586 prefixEnd_7144586 := by exact prefixLift 7144586
  have htrace : WordTrace (prefixWord ++ tailWord_7144586) baseStart_7144586 baseEnd_7144586 := by
    simpa [prefixWord, tailWord_7144586, baseEnd_7144586] using wordTrace_append hprefix tailTrace_7144586
  have hstable : (prefixWord ++ tailWord_7144586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144586).length < 2 ^ (prefixWord ++ tailWord_7144586).sum := by decide
  have hdescent : baseEnd_7144586 < baseStart_7144586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144600 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7144600 : Nat := 118140960795 + 7144600 * 2 ^ 59
def prefixEnd_7144600 : Nat := 4983230072969 + 3 ^ 40 * 7144600 * 2
def baseEnd_7144600 : Nat := 3668613884112851953342589

theorem tailTrace_7144600 : CollatzResearch.WordTrace tailWord_7144600 prefixEnd_7144600 3668613884112851953342589 := by
  unfold tailWord_7144600
  simp only [CollatzResearch.WordTrace]
  refine ⟨130292484958170937689991627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173723313277561250253322169 130292484958170937689991627)
  ·
    refine ⟨195438727437256406534987441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130292484958170937689991627 195438727437256406534987441)
    ·
      refine ⟨146579045577942304901240581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195438727437256406534987441 146579045577942304901240581)
      ·
        refine ⟨27483571045864182168982609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146579045577942304901240581 27483571045864182168982609)
        ·
          refine ⟨20612678284398136626736957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27483571045864182168982609 20612678284398136626736957)
          ·
            refine ⟨7729754356649301235026359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20612678284398136626736957 7729754356649301235026359)
            ·
              refine ⟨11594631534973951852539539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7729754356649301235026359 11594631534973951852539539)
              ·
                refine ⟨17391947302460927778809309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11594631534973951852539539 17391947302460927778809309)
                ·
                  refine ⟨6521980238422847917053491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17391947302460927778809309 6521980238422847917053491)
                  ·
                    refine ⟨9782970357634271875580237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6521980238422847917053491 9782970357634271875580237)
                    ·
                      refine ⟨3668613884112851953342589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9782970357634271875580237 3668613884112851953342589)
                      ·
                        rfl

theorem cell23_7144600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7144600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144600 prefixEnd_7144600 := by exact prefixLift 7144600
  have htrace : WordTrace (prefixWord ++ tailWord_7144600) baseStart_7144600 baseEnd_7144600 := by
    simpa [prefixWord, tailWord_7144600, baseEnd_7144600] using wordTrace_append hprefix tailTrace_7144600
  have hstable : (prefixWord ++ tailWord_7144600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144600).length < 2 ^ (prefixWord ++ tailWord_7144600).sum := by decide
  have hdescent : baseEnd_7144600 < baseStart_7144600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144623 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 3, 2, 2]
def baseStart_7144623 : Nat := 118140960795 + 7144623 * 2 ^ 59
def prefixEnd_7144623 : Nat := 4983230072969 + 3 ^ 40 * 7144623 * 2
def baseEnd_7144623 : Nat := 3668625694167905363354983

theorem tailTrace_7144623 : CollatzResearch.WordTrace tailWord_7144623 prefixEnd_7144623 3668625694167905363354983 := by
  unfold tailWord_7144623
  simp only [CollatzResearch.WordTrace]
  refine ⟨260585808795258550308070523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173723872530172366872047015 260585808795258550308070523)
  ·
    refine ⟨390878713192887825462105785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260585808795258550308070523 390878713192887825462105785)
    ·
      refine ⟨293159034894665869096579339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390878713192887825462105785 293159034894665869096579339)
      ·
        refine ⟨439738552341998803644869009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293159034894665869096579339 439738552341998803644869009)
        ·
          refine ⟨329803914256499102733651757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439738552341998803644869009 329803914256499102733651757)
          ·
            refine ⟨123676467846187163525119409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329803914256499102733651757 123676467846187163525119409)
            ·
              refine ⟨92757350884640372643839557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123676467846187163525119409 92757350884640372643839557)
              ·
                refine ⟨17392003290870069870719917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92757350884640372643839557 17392003290870069870719917)
                ·
                  refine ⟨6522001234076276201519969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17392003290870069870719917 6522001234076276201519969)
                  ·
                    refine ⟨4891500925557207151139977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6522001234076276201519969 4891500925557207151139977)
                    ·
                      refine ⟨3668625694167905363354983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891500925557207151139977 3668625694167905363354983)
                      ·
                        rfl

theorem cell23_7144623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 2, 2].length) (baseStart_7144623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144623 prefixEnd_7144623 := by exact prefixLift 7144623
  have htrace : WordTrace (prefixWord ++ tailWord_7144623) baseStart_7144623 baseEnd_7144623 := by
    simpa [prefixWord, tailWord_7144623, baseEnd_7144623] using wordTrace_append hprefix tailTrace_7144623
  have hstable : (prefixWord ++ tailWord_7144623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144623).length < 2 ^ (prefixWord ++ tailWord_7144623).sum := by decide
  have hdescent : baseEnd_7144623 < baseStart_7144623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144636 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_7144636 : Nat := 118140960795 + 7144636 * 2 ^ 59
def prefixEnd_7144636 : Nat := 4983230072969 + 3 ^ 40 * 7144636 * 2
def baseEnd_7144636 : Nat := 3668632369416413812492423

theorem tailTrace_7144636 : CollatzResearch.WordTrace tailWord_7144636 prefixEnd_7144636 3668632369416413812492423 := by
  unfold tailWord_7144636
  simp only [CollatzResearch.WordTrace]
  refine ⟨130293141472105726764146881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173724188629474302352195841 130293141472105726764146881)
  ·
    refine ⟨97719856104079295073110161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130293141472105726764146881 97719856104079295073110161)
    ·
      refine ⟨73289892078059471304832621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97719856104079295073110161 73289892078059471304832621)
      ·
        refine ⟨27483709529272301739312233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73289892078059471304832621 27483709529272301739312233)
        ·
          refine ⟨20612782146954226304484175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27483709529272301739312233 20612782146954226304484175)
          ·
            refine ⟨30919173220431339456726263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20612782146954226304484175 30919173220431339456726263)
            ·
              refine ⟨46378759830647009185089395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30919173220431339456726263 46378759830647009185089395)
              ·
                refine ⟨69568139745970513777634093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46378759830647009185089395 69568139745970513777634093)
                ·
                  refine ⟨26088052404738942666612785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69568139745970513777634093 26088052404738942666612785)
                  ·
                    refine ⟨19566039303554206999959589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26088052404738942666612785 19566039303554206999959589)
                    ·
                      refine ⟨3668632369416413812492423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19566039303554206999959589 3668632369416413812492423)
                      ·
                        rfl

theorem cell23_7144636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_7144636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144636 prefixEnd_7144636 := by exact prefixLift 7144636
  have htrace : WordTrace (prefixWord ++ tailWord_7144636) baseStart_7144636 baseEnd_7144636 := by
    simpa [prefixWord, tailWord_7144636, baseEnd_7144636] using wordTrace_append hprefix tailTrace_7144636
  have hstable : (prefixWord ++ tailWord_7144636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144636).length < 2 ^ (prefixWord ++ tailWord_7144636).sum := by decide
  have hdescent : baseEnd_7144636 < baseStart_7144636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144640 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 1, 1, 4]
def baseStart_7144640 : Nat := 118140960795 + 7144640 * 2 ^ 59
def prefixEnd_7144640 : Nat := 4983230072969 + 3 ^ 40 * 7144640 * 2
def baseEnd_7144640 : Nat := 3668634423339031796842405

theorem tailTrace_7144640 : CollatzResearch.WordTrace tailWord_7144640 prefixEnd_7144640 3668634423339031796842405 := by
  unfold tailWord_7144640
  simp only [CollatzResearch.WordTrace]
  refine ⟨130293214418098481105719687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173724285890797974807626249 130293214418098481105719687)
  ·
    refine ⟨195439821627147721658579531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130293214418098481105719687 195439821627147721658579531)
    ·
      refine ⟨293159732440721582487869297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195439821627147721658579531 293159732440721582487869297)
      ·
        refine ⟨219869799330541186865901973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293159732440721582487869297 219869799330541186865901973)
        ·
          refine ⟨10306396843619118134339155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219869799330541186865901973 10306396843619118134339155)
          ·
            refine ⟨15459595265428677201508733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10306396843619118134339155 15459595265428677201508733)
            ·
              refine ⟨5797348224535753950565775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15459595265428677201508733 5797348224535753950565775)
              ·
                refine ⟨8696022336803630925848663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797348224535753950565775 8696022336803630925848663)
                ·
                  refine ⟨13044033505205446388772995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8696022336803630925848663 13044033505205446388772995)
                  ·
                    refine ⟨19566050257808169583159493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13044033505205446388772995 19566050257808169583159493)
                    ·
                      refine ⟨3668634423339031796842405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19566050257808169583159493 3668634423339031796842405)
                      ·
                        rfl

theorem cell23_7144640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_7144640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144640 prefixEnd_7144640 := by exact prefixLift 7144640
  have htrace : WordTrace (prefixWord ++ tailWord_7144640) baseStart_7144640 baseEnd_7144640 := by
    simpa [prefixWord, tailWord_7144640, baseEnd_7144640] using wordTrace_append hprefix tailTrace_7144640
  have hstable : (prefixWord ++ tailWord_7144640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144640).length < 2 ^ (prefixWord ++ tailWord_7144640).sum := by decide
  have hdescent : baseEnd_7144640 < baseStart_7144640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144673 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_7144673 : Nat := 118140960795 + 7144673 * 2 ^ 59
def prefixEnd_7144673 : Nat := 4983230072969 + 3 ^ 40 * 7144673 * 2
def baseEnd_7144673 : Nat := 3668651368200630167729753

theorem tailTrace_7144673 : CollatzResearch.WordTrace tailWord_7144673 prefixEnd_7144673 3668651368200630167729753 := by
  unfold tailWord_7144673
  simp only [CollatzResearch.WordTrace]
  refine ⟨260587632445077408847390673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173725088296718272564927115 260587632445077408847390673)
  ·
    refine ⟨195440724333808056635543005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260587632445077408847390673 195440724333808056635543005)
    ·
      refine ⟨73290271625178021238328627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195440724333808056635543005 73290271625178021238328627)
      ·
        refine ⟨109935407437767031857492941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73290271625178021238328627 109935407437767031857492941)
        ·
          refine ⟨41225777789162636946559853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109935407437767031857492941 41225777789162636946559853)
          ·
            refine ⟨15459666670935988854959945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41225777789162636946559853 15459666670935988854959945)
            ·
              refine ⟨11594750003201991641219959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15459666670935988854959945 11594750003201991641219959)
              ·
                refine ⟨17392125004802987461829939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11594750003201991641219959 17392125004802987461829939)
                ·
                  refine ⟨26088187507204481192744909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17392125004802987461829939 26088187507204481192744909)
                  ·
                    refine ⟨9783070315201680447279341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26088187507204481192744909 9783070315201680447279341)
                    ·
                      refine ⟨3668651368200630167729753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9783070315201680447279341 3668651368200630167729753)
                      ·
                        rfl

theorem cell23_7144673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_7144673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144673 prefixEnd_7144673 := by exact prefixLift 7144673
  have htrace : WordTrace (prefixWord ++ tailWord_7144673) baseStart_7144673 baseEnd_7144673 := by
    simpa [prefixWord, tailWord_7144673, baseEnd_7144673] using wordTrace_append hprefix tailTrace_7144673
  have hstable : (prefixWord ++ tailWord_7144673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144673).length < 2 ^ (prefixWord ++ tailWord_7144673).sum := by decide
  have hdescent : baseEnd_7144673 < baseStart_7144673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144683 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 3, 3, 2]
def baseStart_7144683 : Nat := 118140960795 + 7144683 * 2 ^ 59
def prefixEnd_7144683 : Nat := 4983230072969 + 3 ^ 40 * 7144683 * 2
def baseEnd_7144683 : Nat := 3668656503007175128604707

theorem tailTrace_7144683 : CollatzResearch.WordTrace tailWord_7144683 prefixEnd_7144683 3668656503007175128604707 := by
  unfold tailWord_7144683
  simp only [CollatzResearch.WordTrace]
  refine ⟨260587997175041180555254703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173725331450027453703503135 260587997175041180555254703)
  ·
    refine ⟨390881995762561770832882055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260587997175041180555254703 390881995762561770832882055)
    ·
      refine ⟨586322993643842656249323083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390881995762561770832882055 586322993643842656249323083)
      ·
        refine ⟨879484490465763984373984625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586322993643842656249323083 879484490465763984373984625)
        ·
          refine ⟨659613367849322988280488469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 879484490465763984373984625 659613367849322988280488469)
          ·
            refine ⟨30919376617937015075647897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 659613367849322988280488469 30919376617937015075647897)
            ·
              refine ⟨23189532463452761306735923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30919376617937015075647897 23189532463452761306735923)
              ·
                refine ⟨34784298695179141960103885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23189532463452761306735923 34784298695179141960103885)
                ·
                  refine ⟨13044112010692178235038957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34784298695179141960103885 13044112010692178235038957)
                  ·
                    refine ⟨4891542004009566838139609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13044112010692178235038957 4891542004009566838139609)
                    ·
                      refine ⟨3668656503007175128604707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891542004009566838139609 3668656503007175128604707)
                      ·
                        rfl

theorem cell23_7144683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3, 2].length) (baseStart_7144683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144683 prefixEnd_7144683 := by exact prefixLift 7144683
  have htrace : WordTrace (prefixWord ++ tailWord_7144683) baseStart_7144683 baseEnd_7144683 := by
    simpa [prefixWord, tailWord_7144683, baseEnd_7144683] using wordTrace_append hprefix tailTrace_7144683
  have hstable : (prefixWord ++ tailWord_7144683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144683).length < 2 ^ (prefixWord ++ tailWord_7144683).sum := by decide
  have hdescent : baseEnd_7144683 < baseStart_7144683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144689 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 3, 8]
def baseStart_7144689 : Nat := 118140960795 + 7144689 * 2 ^ 59
def prefixEnd_7144689 : Nat := 4983230072969 + 3 ^ 40 * 7144689 * 2
def baseEnd_7144689 : Nat := 1222886527963700701709893

theorem tailTrace_7144689 : CollatzResearch.WordTrace tailWord_7144689 prefixEnd_7144689 1222886527963700701709893 := by
  unfold tailWord_7144689
  simp only [CollatzResearch.WordTrace]
  refine ⟨260588216013019443579973121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173725477342012962386648747 260588216013019443579973121)
  ·
    refine ⟨195441162009764582684979841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260588216013019443579973121 195441162009764582684979841)
    ·
      refine ⟨146580871507323437013734881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195441162009764582684979841 146580871507323437013734881)
      ·
        refine ⟨109935653630492577760301161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146580871507323437013734881 109935653630492577760301161)
        ·
          refine ⟨82451740222869433320225871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109935653630492577760301161 82451740222869433320225871)
          ·
            refine ⟨123677610334304149980338807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82451740222869433320225871 123677610334304149980338807)
            ·
              refine ⟨185516415501456224970508211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123677610334304149980338807 185516415501456224970508211)
              ·
                refine ⟨278274623252184337455762317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185516415501456224970508211 278274623252184337455762317)
                ·
                  refine ⟨104352983719569126545910869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278274623252184337455762317 104352983719569126545910869)
                  ·
                    refine ⟨1222886527963700701709893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104352983719569126545910869 1222886527963700701709893)
                    ·
                      rfl

theorem cell23_7144689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_7144689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144689 prefixEnd_7144689 := by exact prefixLift 7144689
  have htrace : WordTrace (prefixWord ++ tailWord_7144689) baseStart_7144689 baseEnd_7144689 := by
    simpa [prefixWord, tailWord_7144689, baseEnd_7144689] using wordTrace_append hprefix tailTrace_7144689
  have hstable : (prefixWord ++ tailWord_7144689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144689).length < 2 ^ (prefixWord ++ tailWord_7144689).sum := by decide
  have hdescent : baseEnd_7144689 < baseStart_7144689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144729 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_7144729 : Nat := 118140960795 + 7144729 * 2 ^ 59
def prefixEnd_7144729 : Nat := 4983230072969 + 3 ^ 40 * 7144729 * 2
def baseEnd_7144729 : Nat := 3668680123117281948629495

theorem tailTrace_7144729 : CollatzResearch.WordTrace tailWord_7144729 prefixEnd_7144729 3668680123117281948629495 := by
  unfold tailWord_7144729
  simp only [CollatzResearch.WordTrace]
  refine ⟨260589674932874530411429241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173726449955249686940952827 260589674932874530411429241)
  ·
    refine ⟨195442256199655897808571931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260589674932874530411429241 195442256199655897808571931)
    ·
      refine ⟨293163384299483846712857897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195442256199655897808571931 293163384299483846712857897)
      ·
        refine ⟨219872538224612885034643423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293163384299483846712857897 219872538224612885034643423)
        ·
          refine ⟨329808807336919327551965135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219872538224612885034643423 329808807336919327551965135)
          ·
            refine ⟨494713211005378991327947703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329808807336919327551965135 494713211005378991327947703)
            ·
              refine ⟨742069816508068486991921555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494713211005378991327947703 742069816508068486991921555)
              ·
                refine ⟨1113104724762102730487882333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742069816508068486991921555 1113104724762102730487882333)
                ·
                  refine ⟨417414271785788523932955875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113104724762102730487882333 417414271785788523932955875)
                  ·
                    refine ⟨626121407678682785899433813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 417414271785788523932955875 626121407678682785899433813)
                    ·
                      refine ⟨3668680123117281948629495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 626121407678682785899433813 3668680123117281948629495)
                      ·
                        rfl

theorem cell23_7144729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_7144729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144729 prefixEnd_7144729 := by exact prefixLift 7144729
  have htrace : WordTrace (prefixWord ++ tailWord_7144729) baseStart_7144729 baseEnd_7144729 := by
    simpa [prefixWord, tailWord_7144729, baseEnd_7144729] using wordTrace_append hprefix tailTrace_7144729
  have hstable : (prefixWord ++ tailWord_7144729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144729).length < 2 ^ (prefixWord ++ tailWord_7144729).sum := by decide
  have hdescent : baseEnd_7144729 < baseStart_7144729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144730 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2]
def baseStart_7144730 : Nat := 118140960795 + 7144730 * 2 ^ 59
def prefixEnd_7144730 : Nat := 4983230072969 + 3 ^ 40 * 7144730 * 2
def baseEnd_7144730 : Nat := 3668680636597936444716991

theorem tailTrace_7144730 : CollatzResearch.WordTrace tailWord_7144730 prefixEnd_7144730 3668680636597936444716991 := by
  unfold tailWord_7144730
  simp only [CollatzResearch.WordTrace]
  refine ⟨65147427851467726895553911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173726474270580605054810429 65147427851467726895553911)
  ·
    refine ⟨97721141777201590343330867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65147427851467726895553911 97721141777201590343330867)
    ·
      refine ⟨146581712665802385514996301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97721141777201590343330867 146581712665802385514996301)
      ·
        refine ⟨54968142249675894568123613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146581712665802385514996301 54968142249675894568123613)
        ·
          refine ⟨20613053343628460463046355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54968142249675894568123613 20613053343628460463046355)
          ·
            refine ⟨30919580015442690694569533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20613053343628460463046355 30919580015442690694569533)
            ·
              refine ⟨11594842505791009010463575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30919580015442690694569533 11594842505791009010463575)
              ·
                refine ⟨17392263758686513515695363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11594842505791009010463575 17392263758686513515695363)
                ·
                  refine ⟨26088395638029770273543045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17392263758686513515695363 26088395638029770273543045)
                  ·
                    refine ⟨4891574182130581926289321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26088395638029770273543045 4891574182130581926289321)
                    ·
                      refine ⟨3668680636597936444716991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891574182130581926289321 3668680636597936444716991)
                      ·
                        rfl

theorem cell23_7144730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_7144730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144730 prefixEnd_7144730 := by exact prefixLift 7144730
  have htrace : WordTrace (prefixWord ++ tailWord_7144730) baseStart_7144730 baseEnd_7144730 := by
    simpa [prefixWord, tailWord_7144730, baseEnd_7144730] using wordTrace_append hprefix tailTrace_7144730
  have hstable : (prefixWord ++ tailWord_7144730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144730).length < 2 ^ (prefixWord ++ tailWord_7144730).sum := by decide
  have hdescent : baseEnd_7144730 < baseStart_7144730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144781 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7144781 : Nat := 118140960795 + 7144781 * 2 ^ 59
def prefixEnd_7144781 : Nat := 4983230072969 + 3 ^ 40 * 7144781 * 2
def baseEnd_7144781 : Nat := 3668706824111315745179257

theorem tailTrace_7144781 : CollatzResearch.WordTrace tailWord_7144781 prefixEnd_7144781 3668706824111315745179257 := by
  unfold tailWord_7144781
  simp only [CollatzResearch.WordTrace]
  refine ⟨260591571528686143292322197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173727714352457428861548131 260591571528686143292322197)
  ·
    refine ⟨12215229915407162966827603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260591571528686143292322197 12215229915407162966827603)
    ·
      refine ⟨18322844873110744450241405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12215229915407162966827603 18322844873110744450241405)
      ·
        refine ⟨6871066827416529168840527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18322844873110744450241405 6871066827416529168840527)
        ·
          refine ⟨10306600241124793753260791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871066827416529168840527 10306600241124793753260791)
          ·
            refine ⟨15459900361687190629891187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10306600241124793753260791 15459900361687190629891187)
            ·
              refine ⟨23189850542530785944836781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15459900361687190629891187 23189850542530785944836781)
              ·
                refine ⟨8696193953449044729313793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23189850542530785944836781 8696193953449044729313793)
                ·
                  refine ⟨6522145465086783546985345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8696193953449044729313793 6522145465086783546985345)
                  ·
                    refine ⟨4891609098815087660239009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6522145465086783546985345 4891609098815087660239009)
                    ·
                      refine ⟨3668706824111315745179257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891609098815087660239009 3668706824111315745179257)
                      ·
                        rfl

theorem cell23_7144781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7144781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144781 prefixEnd_7144781 := by exact prefixLift 7144781
  have htrace : WordTrace (prefixWord ++ tailWord_7144781) baseStart_7144781 baseEnd_7144781 := by
    simpa [prefixWord, tailWord_7144781, baseEnd_7144781] using wordTrace_append hprefix tailTrace_7144781
  have hstable : (prefixWord ++ tailWord_7144781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144781).length < 2 ^ (prefixWord ++ tailWord_7144781).sum := by decide
  have hdescent : baseEnd_7144781 < baseStart_7144781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144803 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 4]
def baseStart_7144803 : Nat := 118140960795 + 7144803 * 2 ^ 59
def prefixEnd_7144803 : Nat := 4983230072969 + 3 ^ 40 * 7144803 * 2
def baseEnd_7144803 : Nat := 3668718120685714659104155

theorem tailTrace_7144803 : CollatzResearch.WordTrace tailWord_7144803 prefixEnd_7144803 3668718120685714659104155 := by
  unfold tailWord_7144803
  simp only [CollatzResearch.WordTrace]
  refine ⟨260592373934606441049623063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173728249289737627366415375 260592373934606441049623063)
  ·
    refine ⟨390888560901909661574434595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260592373934606441049623063 390888560901909661574434595)
    ·
      refine ⟨586332841352864492361651893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390888560901909661574434595 586332841352864492361651893)
      ·
        refine ⟨54968703876831046158904865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 586332841352864492361651893 54968703876831046158904865)
        ·
          refine ⟨41226527907623284619178649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54968703876831046158904865 41226527907623284619178649)
          ·
            refine ⟨30919895930717463464383987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41226527907623284619178649 30919895930717463464383987)
            ·
              refine ⟨46379843896076195196575981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30919895930717463464383987 46379843896076195196575981)
              ·
                refine ⟨17392441461028573198715993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46379843896076195196575981 17392441461028573198715993)
                ·
                  refine ⟨13044331095771429899036995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17392441461028573198715993 13044331095771429899036995)
                  ·
                    refine ⟨19566496643657144848555493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13044331095771429899036995 19566496643657144848555493)
                    ·
                      refine ⟨3668718120685714659104155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19566496643657144848555493 3668718120685714659104155)
                      ·
                        rfl

theorem cell23_7144803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_7144803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144803 prefixEnd_7144803 := by exact prefixLift 7144803
  have htrace : WordTrace (prefixWord ++ tailWord_7144803) baseStart_7144803 baseEnd_7144803 := by
    simpa [prefixWord, tailWord_7144803, baseEnd_7144803] using wordTrace_append hprefix tailTrace_7144803
  have hstable : (prefixWord ++ tailWord_7144803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144803).length < 2 ^ (prefixWord ++ tailWord_7144803).sum := by decide
  have hdescent : baseEnd_7144803 < baseStart_7144803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144816 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_7144816 : Nat := 118140960795 + 7144816 * 2 ^ 59
def prefixEnd_7144816 : Nat := 4983230072969 + 3 ^ 40 * 7144816 * 2
def baseEnd_7144816 : Nat := 3668724795934223108241595

theorem tailTrace_7144816 : CollatzResearch.WordTrace tailWord_7144816 prefixEnd_7144816 3668724795934223108241595 := by
  unfold tailWord_7144816
  simp only [CollatzResearch.WordTrace]
  refine ⟨130296424041779672134923151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173728565389039562846564201 130296424041779672134923151)
  ·
    refine ⟨195444636062669508202384727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130296424041779672134923151 195444636062669508202384727)
    ·
      refine ⟨293166954094004262303577091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195444636062669508202384727 293166954094004262303577091)
      ·
        refine ⟨439750431141006393455365637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293166954094004262303577091 439750431141006393455365637)
        ·
          refine ⟨82453205838938698772881057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439750431141006393455365637 82453205838938698772881057)
          ·
            refine ⟨61839904379204024079660793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82453205838938698772881057 61839904379204024079660793)
            ·
              refine ⟨46379928284403018059745595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61839904379204024079660793 46379928284403018059745595)
              ·
                refine ⟨69569892426604527089618393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46379928284403018059745595 69569892426604527089618393)
                ·
                  refine ⟨52177419319953395317213795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69569892426604527089618393 52177419319953395317213795)
                  ·
                    refine ⟨78266128979930092975820693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52177419319953395317213795 78266128979930092975820693)
                    ·
                      refine ⟨3668724795934223108241595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78266128979930092975820693 3668724795934223108241595)
                      ·
                        rfl

theorem cell23_7144816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_7144816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144816 prefixEnd_7144816 := by exact prefixLift 7144816
  have htrace : WordTrace (prefixWord ++ tailWord_7144816) baseStart_7144816 baseEnd_7144816 := by
    simpa [prefixWord, tailWord_7144816, baseEnd_7144816] using wordTrace_append hprefix tailTrace_7144816
  have hstable : (prefixWord ++ tailWord_7144816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144816).length < 2 ^ (prefixWord ++ tailWord_7144816).sum := by decide
  have hdescent : baseEnd_7144816 < baseStart_7144816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144823 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_7144823 : Nat := 118140960795 + 7144823 * 2 ^ 59
def prefixEnd_7144823 : Nat := 4983230072969 + 3 ^ 40 * 7144823 * 2
def baseEnd_7144823 : Nat := 3668728390298804580854063

theorem tailTrace_7144823 : CollatzResearch.WordTrace tailWord_7144823 prefixEnd_7144823 3668728390298804580854063 := by
  unfold tailWord_7144823
  simp only [CollatzResearch.WordTrace]
  refine ⟨260593103394533984465351123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173728735596355989643567415 260593103394533984465351123)
  ·
    refine ⟨390889655091800976698026685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260593103394533984465351123 390889655091800976698026685)
    ·
      refine ⟨146583620659425366261760007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390889655091800976698026685 146583620659425366261760007)
      ·
        refine ⟨219875430989138049392640011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146583620659425366261760007 219875430989138049392640011)
        ·
          refine ⟨329813146483707074088960017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219875430989138049392640011 329813146483707074088960017)
          ·
            refine ⟨247359859862780305566720013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329813146483707074088960017 247359859862780305566720013)
            ·
              refine ⟨92759947448542614587520005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247359859862780305566720013 92759947448542614587520005)
              ·
                refine ⟨17392490146601740235160001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92759947448542614587520005 17392490146601740235160001)
                ·
                  refine ⟨13044367609951305176370001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17392490146601740235160001 13044367609951305176370001)
                  ·
                    refine ⟨9783275707463478882277501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13044367609951305176370001 9783275707463478882277501)
                    ·
                      refine ⟨3668728390298804580854063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9783275707463478882277501 3668728390298804580854063)
                      ·
                        rfl

theorem cell23_7144823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_7144823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144823 prefixEnd_7144823 := by exact prefixLift 7144823
  have htrace : WordTrace (prefixWord ++ tailWord_7144823) baseStart_7144823 baseEnd_7144823 := by
    simpa [prefixWord, tailWord_7144823, baseEnd_7144823] using wordTrace_append hprefix tailTrace_7144823
  have hstable : (prefixWord ++ tailWord_7144823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144823).length < 2 ^ (prefixWord ++ tailWord_7144823).sum := by decide
  have hdescent : baseEnd_7144823 < baseStart_7144823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144877 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 6]
def baseStart_7144877 : Nat := 118140960795 + 7144877 * 2 ^ 59
def prefixEnd_7144877 : Nat := 4983230072969 + 3 ^ 40 * 7144877 * 2
def baseEnd_7144877 : Nat := 407639568694905263286535

theorem tailTrace_7144877 : CollatzResearch.WordTrace tailWord_7144877 prefixEnd_7144877 407639568694905263286535 := by
  unfold tailWord_7144877
  simp only [CollatzResearch.WordTrace]
  refine ⟨260595072936338351687816885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173730048624225567791877923 260595072936338351687816885)
  ·
    refine ⟨24430788087781720470732833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260595072936338351687816885 24430788087781720470732833)
    ·
      refine ⟨18323091065836290353049625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24430788087781720470732833 18323091065836290353049625)
      ·
        refine ⟨13742318299377217764787219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18323091065836290353049625 13742318299377217764787219)
        ·
          refine ⟨20613477449065826647180829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13742318299377217764787219 20613477449065826647180829)
          ·
            refine ⟨7730054043399684992692811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20613477449065826647180829 7730054043399684992692811)
            ·
              refine ⟨11595081065099527489039217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730054043399684992692811 11595081065099527489039217)
              ·
                refine ⟨8696310798824645616779413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11595081065099527489039217 8696310798824645616779413)
                ·
                  refine ⟨407639568694905263286535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8696310798824645616779413 407639568694905263286535)
                  ·
                    rfl

theorem cell23_7144877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_7144877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144877 prefixEnd_7144877 := by exact prefixLift 7144877
  have htrace : WordTrace (prefixWord ++ tailWord_7144877) baseStart_7144877 baseEnd_7144877 := by
    simpa [prefixWord, tailWord_7144877, baseEnd_7144877] using wordTrace_append hprefix tailTrace_7144877
  have hstable : (prefixWord ++ tailWord_7144877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144877).length < 2 ^ (prefixWord ++ tailWord_7144877).sum := by decide
  have hdescent : baseEnd_7144877 < baseStart_7144877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144887 : List Nat := [1, 1, 3, 1, 3, 2, 1, 6, 1, 1, 3]
def baseStart_7144887 : Nat := 118140960795 + 7144887 * 2 ^ 59
def prefixEnd_7144887 : Nat := 4983230072969 + 3 ^ 40 * 7144887 * 2
def baseEnd_7144887 : Nat := 3668761253060692330453769

theorem tailTrace_7144887 : CollatzResearch.WordTrace tailWord_7144887 prefixEnd_7144887 3668761253060692330453769 := by
  unfold tailWord_7144887
  simp only [CollatzResearch.WordTrace]
  refine ⟨260595437666302123395680915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173730291777534748930453943 260595437666302123395680915)
  ·
    refine ⟨390893156499453185093521373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260595437666302123395680915 390893156499453185093521373)
    ·
      refine ⟨146584933687294944410070515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390893156499453185093521373 146584933687294944410070515)
      ·
        refine ⟨219877400530942416615105773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146584933687294944410070515 219877400530942416615105773)
        ·
          refine ⟨82454025199103406230664665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219877400530942416615105773 82454025199103406230664665)
          ·
            refine ⟨61840518899327554672998499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82454025199103406230664665 61840518899327554672998499)
            ·
              refine ⟨92760778348991332009497749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61840518899327554672998499 92760778348991332009497749)
              ·
                refine ⟨4348161485108968687945207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92760778348991332009497749 4348161485108968687945207)
                ·
                  refine ⟨6522242227663453031917811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348161485108968687945207 6522242227663453031917811)
                  ·
                    refine ⟨9783363341495179547876717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522242227663453031917811 9783363341495179547876717)
                    ·
                      refine ⟨3668761253060692330453769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9783363341495179547876717 3668761253060692330453769)
                      ·
                        rfl

theorem cell23_7144887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_7144887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144887 prefixEnd_7144887 := by exact prefixLift 7144887
  have htrace : WordTrace (prefixWord ++ tailWord_7144887) baseStart_7144887 baseEnd_7144887 := by
    simpa [prefixWord, tailWord_7144887, baseEnd_7144887] using wordTrace_append hprefix tailTrace_7144887
  have hstable : (prefixWord ++ tailWord_7144887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144887).length < 2 ^ (prefixWord ++ tailWord_7144887).sum := by decide
  have hdescent : baseEnd_7144887 < baseStart_7144887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144910 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_7144910 : Nat := 118140960795 + 7144910 * 2 ^ 59
def prefixEnd_7144910 : Nat := 4983230072969 + 3 ^ 40 * 7144910 * 2
def baseEnd_7144910 : Nat := 3668773063115745740466163

theorem tailTrace_7144910 : CollatzResearch.WordTrace tailWord_7144910 prefixEnd_7144910 3668773063115745740466163 := by
  unfold tailWord_7144910
  simp only [CollatzResearch.WordTrace]
  refine ⟨32574534568152349790471023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173730851030145865549178789 32574534568152349790471023)
  ·
    refine ⟨48861801852228524685706535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32574534568152349790471023 48861801852228524685706535)
    ·
      refine ⟨73292702778342787028559803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48861801852228524685706535 73292702778342787028559803)
      ·
        refine ⟨109939054167514180542839705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73292702778342787028559803 109939054167514180542839705)
        ·
          refine ⟨82454290625635635407129779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109939054167514180542839705 82454290625635635407129779)
          ·
            refine ⟨123681435938453453110694669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82454290625635635407129779 123681435938453453110694669)
            ·
              refine ⟨46380538476920044916510501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123681435938453453110694669 46380538476920044916510501)
              ·
                refine ⟨8696350964422508421845719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46380538476920044916510501 8696350964422508421845719)
                ·
                  refine ⟨13044526446633762632768579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8696350964422508421845719 13044526446633762632768579)
                  ·
                    refine ⟨19566789669950643949152869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13044526446633762632768579 19566789669950643949152869)
                    ·
                      refine ⟨3668773063115745740466163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19566789669950643949152869 3668773063115745740466163)
                      ·
                        rfl

theorem cell23_7144910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_7144910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144910 prefixEnd_7144910 := by exact prefixLift 7144910
  have htrace : WordTrace (prefixWord ++ tailWord_7144910) baseStart_7144910 baseEnd_7144910 := by
    simpa [prefixWord, tailWord_7144910, baseEnd_7144910] using wordTrace_append hprefix tailTrace_7144910
  have hstable : (prefixWord ++ tailWord_7144910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144910).length < 2 ^ (prefixWord ++ tailWord_7144910).sum := by decide
  have hdescent : baseEnd_7144910 < baseStart_7144910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144933 : List Nat := [1, 3, 1, 5, 1, 1, 11]
def baseStart_7144933 : Nat := 118140960795 + 7144933 * 2 ^ 59
def prefixEnd_7144933 : Nat := 4983230072969 + 3 ^ 40 * 7144933 * 2
def baseEnd_7144933 : Nat := 45293640409516038894797

theorem tailTrace_7144933 : CollatzResearch.WordTrace tailWord_7144933 prefixEnd_7144933 45293640409516038894797 := by
  unfold tailWord_7144933
  simp only [CollatzResearch.WordTrace]
  refine ⟨260597115424135473251855453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173731410282756982167903635 260597115424135473251855453)
  ·
    refine ⟨97723918284050802469445795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260597115424135473251855453 97723918284050802469445795)
    ·
      refine ⟨146585877426076203704168693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97723918284050802469445795 146585877426076203704168693)
      ·
        refine ⟨13742426008694644097265815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146585877426076203704168693 13742426008694644097265815)
        ·
          refine ⟨20613639013041966145898723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13742426008694644097265815 20613639013041966145898723)
          ·
            refine ⟨30920458519562949218848085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20613639013041966145898723 30920458519562949218848085)
            ·
              refine ⟨45293640409516038894797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30920458519562949218848085 45293640409516038894797)
              ·
                rfl

theorem cell23_7144933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 11].length) (baseStart_7144933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144933 prefixEnd_7144933 := by exact prefixLift 7144933
  have htrace : WordTrace (prefixWord ++ tailWord_7144933) baseStart_7144933 baseEnd_7144933 := by
    simpa [prefixWord, tailWord_7144933, baseEnd_7144933] using wordTrace_append hprefix tailTrace_7144933
  have hstable : (prefixWord ++ tailWord_7144933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144933).length < 2 ^ (prefixWord ++ tailWord_7144933).sum := by decide
  have hdescent : baseEnd_7144933 < baseStart_7144933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144944 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 3, 2, 2]
def baseStart_7144944 : Nat := 118140960795 + 7144944 * 2 ^ 59
def prefixEnd_7144944 : Nat := 4983230072969 + 3 ^ 40 * 7144944 * 2
def baseEnd_7144944 : Nat := 3668790521457998607441007

theorem tailTrace_7144944 : CollatzResearch.WordTrace tailWord_7144944 prefixEnd_7144944 3668790521457998607441007 := by
  unfold tailWord_7144944
  simp only [CollatzResearch.WordTrace]
  refine ⟨130298758313547811065252943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173731677751397081420337257 130298758313547811065252943)
  ·
    refine ⟨195448137470321716597879415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130298758313547811065252943 195448137470321716597879415)
    ·
      refine ⟨293172206205482574896819123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195448137470321716597879415 293172206205482574896819123)
      ·
        refine ⟨439758309308223862345228685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293172206205482574896819123 439758309308223862345228685)
        ·
          refine ⟨164909365990583948379460757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439758309308223862345228685 164909365990583948379460757)
          ·
            refine ⟨7730126530808622580287223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164909365990583948379460757 7730126530808622580287223)
            ·
              refine ⟨11595189796212933870430835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730126530808622580287223 11595189796212933870430835)
              ·
                refine ⟨17392784694319400805646253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11595189796212933870430835 17392784694319400805646253)
                ·
                  refine ⟨6522294260369775302117345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17392784694319400805646253 6522294260369775302117345)
                  ·
                    refine ⟨4891720695277331476588009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6522294260369775302117345 4891720695277331476588009)
                    ·
                      refine ⟨3668790521457998607441007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891720695277331476588009 3668790521457998607441007)
                      ·
                        rfl

theorem cell23_7144944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 2, 2].length) (baseStart_7144944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144944 prefixEnd_7144944 := by exact prefixLift 7144944
  have htrace : WordTrace (prefixWord ++ tailWord_7144944) baseStart_7144944 baseEnd_7144944 := by
    simpa [prefixWord, tailWord_7144944, baseEnd_7144944] using wordTrace_append hprefix tailTrace_7144944
  have hstable : (prefixWord ++ tailWord_7144944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144944).length < 2 ^ (prefixWord ++ tailWord_7144944).sum := by decide
  have hdescent : baseEnd_7144944 < baseStart_7144944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144950 : List Nat := [5, 1, 1, 1, 2, 3, 2, 8]
def baseStart_7144950 : Nat := 118140960795 + 7144950 * 2 ^ 59
def prefixEnd_7144950 : Nat := 4983230072969 + 3 ^ 40 * 7144950 * 2
def baseEnd_7144950 : Nat := 135881244531182429035777

theorem tailTrace_7144950 : CollatzResearch.WordTrace tailWord_7144950 prefixEnd_7144950 135881244531182429035777 := by
  unfold tailWord_7144950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287358466567117822201519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173731823643382590103482869 16287358466567117822201519)
  ·
    refine ⟨24431037699850676733302279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16287358466567117822201519 24431037699850676733302279)
    ·
      refine ⟨36646556549776015099953419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24431037699850676733302279 36646556549776015099953419)
      ·
        refine ⟨54969834824664022649930129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36646556549776015099953419 54969834824664022649930129)
        ·
          refine ⟨41227376118498016987447597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54969834824664022649930129 41227376118498016987447597)
          ·
            refine ⟨15460266044436756370292849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41227376118498016987447597 15460266044436756370292849)
            ·
              refine ⟨11595199533327567277719637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15460266044436756370292849 11595199533327567277719637)
              ·
                refine ⟨135881244531182429035777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11595199533327567277719637 135881244531182429035777)
                ·
                  rfl

theorem cell23_7144950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_7144950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144950 prefixEnd_7144950 := by exact prefixLift 7144950
  have htrace : WordTrace (prefixWord ++ tailWord_7144950) baseStart_7144950 baseEnd_7144950 := by
    simpa [prefixWord, tailWord_7144950, baseEnd_7144950] using wordTrace_append hprefix tailTrace_7144950
  have hstable : (prefixWord ++ tailWord_7144950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144950).length < 2 ^ (prefixWord ++ tailWord_7144950).sum := by decide
  have hdescent : baseEnd_7144950 < baseStart_7144950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7144995 : List Nat := [1, 1, 1, 4, 6, 1, 2, 2, 1, 2, 2]
def baseStart_7144995 : Nat := 118140960795 + 7144995 * 2 ^ 59
def prefixEnd_7144995 : Nat := 4983230072969 + 3 ^ 40 * 7144995 * 2
def baseEnd_7144995 : Nat := 3668816708971377907903273

theorem tailTrace_7144995 : CollatzResearch.WordTrace tailWord_7144995 prefixEnd_7144995 3668816708971377907903273 := by
  unfold tailWord_7144995
  simp only [CollatzResearch.WordTrace]
  refine ⟨260599376749910857840612439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173732917833273905227074959 260599376749910857840612439)
  ·
    refine ⟨390899065124866286760918659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260599376749910857840612439 390899065124866286760918659)
    ·
      refine ⟨586348597687299430141377989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390899065124866286760918659 586348597687299430141377989)
      ·
        refine ⟨109940362066368643151508373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 586348597687299430141377989 109940362066368643151508373)
        ·
          refine ⟨5153454471861030147726955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109940362066368643151508373 5153454471861030147726955)
          ·
            refine ⟨7730181707791545221590433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153454471861030147726955 7730181707791545221590433)
            ·
              refine ⟨5797636280843658916192825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7730181707791545221590433 5797636280843658916192825)
              ·
                refine ⟨4348227210632744187144619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797636280843658916192825 4348227210632744187144619)
                ·
                  refine ⟨6522340815949116280716929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348227210632744187144619 6522340815949116280716929)
                  ·
                    refine ⟨4891755611961837210537697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6522340815949116280716929 4891755611961837210537697)
                    ·
                      refine ⟨3668816708971377907903273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891755611961837210537697 3668816708971377907903273)
                      ·
                        rfl

theorem cell23_7144995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_7144995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7144995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7144995 prefixEnd_7144995 := by exact prefixLift 7144995
  have htrace : WordTrace (prefixWord ++ tailWord_7144995) baseStart_7144995 baseEnd_7144995 := by
    simpa [prefixWord, tailWord_7144995, baseEnd_7144995] using wordTrace_append hprefix tailTrace_7144995
  have hstable : (prefixWord ++ tailWord_7144995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7144995).length < 2 ^ (prefixWord ++ tailWord_7144995).sum := by decide
  have hdescent : baseEnd_7144995 < baseStart_7144995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7144995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145017 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7145017 : Nat := 118140960795 + 7145017 * 2 ^ 59
def prefixEnd_7145017 : Nat := 4983230072969 + 3 ^ 40 * 7145017 * 2
def baseEnd_7145017 : Nat := 3668828005545776821828171

theorem tailTrace_7145017 : CollatzResearch.WordTrace tailWord_7145017 prefixEnd_7145017 3668828005545776821828171 := by
  unfold tailWord_7145017
  simp only [CollatzResearch.WordTrace]
  refine ⟨260600179155831155597913305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173733452770554103731942203 260600179155831155597913305)
  ·
    refine ⟨195450134366873366698434979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260600179155831155597913305 195450134366873366698434979)
    ·
      refine ⟨293175201550310050047652469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195450134366873366698434979 293175201550310050047652469)
      ·
        refine ⟨27485175145341567191967419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293175201550310050047652469 27485175145341567191967419)
        ·
          refine ⟨41227762718012350787951129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27485175145341567191967419 41227762718012350787951129)
          ·
            refine ⟨30920822038509263090963347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41227762718012350787951129 30920822038509263090963347)
            ·
              refine ⟨46381233057763894636445021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30920822038509263090963347 46381233057763894636445021)
              ·
                refine ⟨17392962396661460488666883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46381233057763894636445021 17392962396661460488666883)
                ·
                  refine ⟨26089443594992190733000325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17392962396661460488666883 26089443594992190733000325)
                  ·
                    refine ⟨4891770674061035762437561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26089443594992190733000325 4891770674061035762437561)
                    ·
                      refine ⟨3668828005545776821828171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891770674061035762437561 3668828005545776821828171)
                      ·
                        rfl

theorem cell23_7145017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7145017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145017 prefixEnd_7145017 := by exact prefixLift 7145017
  have htrace : WordTrace (prefixWord ++ tailWord_7145017) baseStart_7145017 baseEnd_7145017 := by
    simpa [prefixWord, tailWord_7145017, baseEnd_7145017] using wordTrace_append hprefix tailTrace_7145017
  have hstable : (prefixWord ++ tailWord_7145017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145017).length < 2 ^ (prefixWord ++ tailWord_7145017).sum := by decide
  have hdescent : baseEnd_7145017 < baseStart_7145017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145023 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 9]
def baseStart_7145023 : Nat := 118140960795 + 7145023 * 2 ^ 59
def prefixEnd_7145023 : Nat := 4983230072969 + 3 ^ 40 * 7145023 * 2
def baseEnd_7145023 : Nat := 407647898492189310928127

theorem tailTrace_7145023 : CollatzResearch.WordTrace tailWord_7145023 prefixEnd_7145023 407647898492189310928127 := by
  unfold tailWord_7145023
  simp only [CollatzResearch.WordTrace]
  refine ⟨260600397993809418622631723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173733598662539612415087815 260600397993809418622631723)
  ·
    refine ⟨390900596990714127933947585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260600397993809418622631723 390900596990714127933947585)
    ·
      refine ⟨293175447743035595950460689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390900596990714127933947585 293175447743035595950460689)
      ·
        refine ⟨219881585807276696962845517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293175447743035595950460689 219881585807276696962845517)
        ·
          refine ⟨82455594677728761361067069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219881585807276696962845517 82455594677728761361067069)
          ·
            refine ⟨30920848004148285510400151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82455594677728761361067069 30920848004148285510400151)
            ·
              refine ⟨46381272006222428265600227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30920848004148285510400151 46381272006222428265600227)
              ·
                refine ⟨69571908009333642398400341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46381272006222428265600227 69571908009333642398400341)
                ·
                  refine ⟨407647898492189310928127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69571908009333642398400341 407647898492189310928127)
                  ·
                    rfl

theorem cell23_7145023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 9].length) (baseStart_7145023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145023 prefixEnd_7145023 := by exact prefixLift 7145023
  have htrace : WordTrace (prefixWord ++ tailWord_7145023) baseStart_7145023 baseEnd_7145023 := by
    simpa [prefixWord, tailWord_7145023, baseEnd_7145023] using wordTrace_append hprefix tailTrace_7145023
  have hstable : (prefixWord ++ tailWord_7145023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145023).length < 2 ^ (prefixWord ++ tailWord_7145023).sum := by decide
  have hdescent : baseEnd_7145023 < baseStart_7145023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145083 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 2, 8]
def baseStart_7145083 : Nat := 118140960795 + 7145083 * 2 ^ 59
def prefixEnd_7145083 : Nat := 4983230072969 + 3 ^ 40 * 7145083 * 2
def baseEnd_7145083 : Nat := 1222953965089657854534289

theorem tailTrace_7145083 : CollatzResearch.WordTrace tailWord_7145083 prefixEnd_7145083 1222953965089657854534289 := by
  unfold tailWord_7145083
  simp only [CollatzResearch.WordTrace]
  refine ⟨260602586373592048869815903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173735057582394699246543935 260602586373592048869815903)
  ·
    refine ⟨390903879560388073304723855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260602586373592048869815903 390903879560388073304723855)
    ·
      refine ⟨586355819340582109957085783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390903879560388073304723855 586355819340582109957085783)
      ·
        refine ⟨879533729010873164935628675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586355819340582109957085783 879533729010873164935628675)
        ·
          refine ⟨1319300593516309747403443013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879533729010873164935628675 1319300593516309747403443013)
          ·
            refine ⟨247368861284308077638145565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1319300593516309747403443013 247368861284308077638145565)
            ·
              refine ⟨92763322981615529114304587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247368861284308077638145565 92763322981615529114304587)
              ·
                refine ⟨139144984472423293671456881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92763322981615529114304587 139144984472423293671456881)
                ·
                  refine ⟨104358738354317470253592661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139144984472423293671456881 104358738354317470253592661)
                  ·
                    refine ⟨1222953965089657854534289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104358738354317470253592661 1222953965089657854534289)
                    ·
                      rfl

theorem cell23_7145083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_7145083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145083 prefixEnd_7145083 := by exact prefixLift 7145083
  have htrace : WordTrace (prefixWord ++ tailWord_7145083) baseStart_7145083 baseEnd_7145083 := by
    simpa [prefixWord, tailWord_7145083, baseEnd_7145083] using wordTrace_append hprefix tailTrace_7145083
  have hstable : (prefixWord ++ tailWord_7145083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145083).length < 2 ^ (prefixWord ++ tailWord_7145083).sum := by decide
  have hdescent : baseEnd_7145083 < baseStart_7145083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145157 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_7145157 : Nat := 118140960795 + 7145157 * 2 ^ 59
def prefixEnd_7145157 : Nat := 4983230072969 + 3 ^ 40 * 7145157 * 2
def baseEnd_7145157 : Nat := 3668899892837406274077527

theorem tailTrace_7145157 : CollatzResearch.WordTrace tailWord_7145157 prefixEnd_7145157 3668899892837406274077527 := by
  unfold tailWord_7145157
  simp only [CollatzResearch.WordTrace]
  refine ⟨260605285375323959508009725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173736856916882639672006483 260605285375323959508009725)
  ·
    refine ⟨97726982015746484815503647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260605285375323959508009725 97726982015746484815503647)
    ·
      refine ⟨146590473023619727223255471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97726982015746484815503647 146590473023619727223255471)
      ·
        refine ⟨219885709535429590834883207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146590473023619727223255471 219885709535429590834883207)
        ·
          refine ⟨329828564303144386252324811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219885709535429590834883207 329828564303144386252324811)
          ·
            refine ⟨494742846454716579378487217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329828564303144386252324811 494742846454716579378487217)
            ·
              refine ⟨371057134841037434533865413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494742846454716579378487217 371057134841037434533865413)
              ·
                refine ⟨69573212782694518975099765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371057134841037434533865413 69573212782694518975099765)
                ·
                  refine ⟨6522488698377611153915603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69573212782694518975099765 6522488698377611153915603)
                  ·
                    refine ⟨9783733047566416730873405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522488698377611153915603 9783733047566416730873405)
                    ·
                      refine ⟨3668899892837406274077527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9783733047566416730873405 3668899892837406274077527)
                      ·
                        rfl

theorem cell23_7145157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_7145157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145157 prefixEnd_7145157 := by exact prefixLift 7145157
  have htrace : WordTrace (prefixWord ++ tailWord_7145157) baseStart_7145157 baseEnd_7145157 := by
    simpa [prefixWord, tailWord_7145157, baseEnd_7145157] using wordTrace_append hprefix tailTrace_7145157
  have hstable : (prefixWord ++ tailWord_7145157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145157).length < 2 ^ (prefixWord ++ tailWord_7145157).sum := by decide
  have hdescent : baseEnd_7145157 < baseStart_7145157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145164 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 6]
def baseStart_7145164 : Nat := 118140960795 + 7145164 * 2 ^ 59
def prefixEnd_7145164 : Nat := 4983230072969 + 3 ^ 40 * 7145164 * 2
def baseEnd_7145164 : Nat := 407655943022443082965555

theorem tailTrace_7145164 : CollatzResearch.WordTrace tailWord_7145164 prefixEnd_7145164 407655943022443082965555 := by
  unfold tailWord_7145164
  simp only [CollatzResearch.WordTrace]
  refine ⟨130302770343149299851757273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173737027124199066469009697 130302770343149299851757273)
  ·
    refine ⟨97727077757361974888817955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130302770343149299851757273 97727077757361974888817955)
    ·
      refine ⟨146590616636042962333226933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97727077757361974888817955 146590616636042962333226933)
      ·
        refine ⟨13742870309629027718740025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146590616636042962333226933 13742870309629027718740025)
        ·
          refine ⟨10307152732221770789055019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13742870309629027718740025 10307152732221770789055019)
          ·
            refine ⟨15460729098332656183582529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307152732221770789055019 15460729098332656183582529)
            ·
              refine ⟨11595546823749492137686897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15460729098332656183582529 11595546823749492137686897)
              ·
                refine ⟨8696660117812119103265173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11595546823749492137686897 8696660117812119103265173)
                ·
                  refine ⟨407655943022443082965555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8696660117812119103265173 407655943022443082965555)
                  ·
                    rfl

theorem cell23_7145164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_7145164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145164 prefixEnd_7145164 := by exact prefixLift 7145164
  have htrace : WordTrace (prefixWord ++ tailWord_7145164) baseStart_7145164 baseEnd_7145164 := by
    simpa [prefixWord, tailWord_7145164, baseEnd_7145164] using wordTrace_append hprefix tailTrace_7145164
  have hstable : (prefixWord ++ tailWord_7145164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145164).length < 2 ^ (prefixWord ++ tailWord_7145164).sum := by decide
  have hdescent : baseEnd_7145164 < baseStart_7145164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145200 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_7145200 : Nat := 118140960795 + 7145200 * 2 ^ 59
def prefixEnd_7145200 : Nat := 4983230072969 + 3 ^ 40 * 7145200 * 2
def baseEnd_7145200 : Nat := 3668921972505549605839829

theorem tailTrace_7145200 : CollatzResearch.WordTrace tailWord_7145200 prefixEnd_7145200 3668921972505549605839829 := by
  unfold tailWord_7145200
  simp only [CollatzResearch.WordTrace]
  refine ⟨130303426857084088925912527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173737902476112118567883369 130303426857084088925912527)
  ·
    refine ⟨195455140285626133388868791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130303426857084088925912527 195455140285626133388868791)
    ·
      refine ⟨293182710428439200083303187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195455140285626133388868791 293182710428439200083303187)
      ·
        refine ⟨439774065642658800124954781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293182710428439200083303187 439774065642658800124954781)
        ·
          refine ⟨164915274615997050046858043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439774065642658800124954781 164915274615997050046858043)
          ·
            refine ⟨247372911923995575070287065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164915274615997050046858043 247372911923995575070287065)
            ·
              refine ⟨185529683942996681302715299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247372911923995575070287065 185529683942996681302715299)
              ·
                refine ⟨278294525914495021954072949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185529683942996681302715299 278294525914495021954072949)
                ·
                  refine ⟨26090111804483908308194339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278294525914495021954072949 26090111804483908308194339)
                  ·
                    refine ⟨39135167706725862462291509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26090111804483908308194339 39135167706725862462291509)
                    ·
                      refine ⟨3668921972505549605839829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39135167706725862462291509 3668921972505549605839829)
                      ·
                        rfl

theorem cell23_7145200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_7145200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145200 prefixEnd_7145200 := by exact prefixLift 7145200
  have htrace : WordTrace (prefixWord ++ tailWord_7145200) baseStart_7145200 baseEnd_7145200 := by
    simpa [prefixWord, tailWord_7145200, baseEnd_7145200] using wordTrace_append hprefix tailTrace_7145200
  have hstable : (prefixWord ++ tailWord_7145200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145200).length < 2 ^ (prefixWord ++ tailWord_7145200).sum := by decide
  have hdescent : baseEnd_7145200 < baseStart_7145200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145201 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 2, 3, 2]
def baseStart_7145201 : Nat := 118140960795 + 7145201 * 2 ^ 59
def prefixEnd_7145201 : Nat := 4983230072969 + 3 ^ 40 * 7145201 * 2
def baseEnd_7145201 : Nat := 3668922485986204101927325

theorem tailTrace_7145201 : CollatzResearch.WordTrace tailWord_7145201 prefixEnd_7145201 3668922485986204101927325 := by
  unfold tailWord_7145201
  simp only [CollatzResearch.WordTrace]
  refine ⟨260606890187164555022611457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173737926791443036681740971 260606890187164555022611457)
  ·
    refine ⟨195455167640373416266958593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260606890187164555022611457 195455167640373416266958593)
    ·
      refine ⟨146591375730280062200218945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195455167640373416266958593 146591375730280062200218945)
      ·
        refine ⟨109943531797710046650164209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146591375730280062200218945 109943531797710046650164209)
        ·
          refine ⟨82457648848282534987623157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109943531797710046650164209 82457648848282534987623157)
          ·
            refine ⟨7730404579526487655089671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82457648848282534987623157 7730404579526487655089671)
            ·
              refine ⟨11595606869289731482634507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730404579526487655089671 11595606869289731482634507)
              ·
                refine ⟨17393410303934597223951761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11595606869289731482634507 17393410303934597223951761)
                ·
                  refine ⟨13045057727950947917963821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17393410303934597223951761 13045057727950947917963821)
                  ·
                    refine ⟨4891896647981605469236433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13045057727950947917963821 4891896647981605469236433)
                    ·
                      refine ⟨3668922485986204101927325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891896647981605469236433 3668922485986204101927325)
                      ·
                        rfl

theorem cell23_7145201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_7145201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145201 prefixEnd_7145201 := by exact prefixLift 7145201
  have htrace : WordTrace (prefixWord ++ tailWord_7145201) baseStart_7145201 baseEnd_7145201 := by
    simpa [prefixWord, tailWord_7145201, baseEnd_7145201] using wordTrace_append hprefix tailTrace_7145201
  have hstable : (prefixWord ++ tailWord_7145201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145201).length < 2 ^ (prefixWord ++ tailWord_7145201).sum := by decide
  have hdescent : baseEnd_7145201 < baseStart_7145201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145210 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_7145210 : Nat := 118140960795 + 7145210 * 2 ^ 59
def prefixEnd_7145210 : Nat := 4983230072969 + 3 ^ 40 * 7145210 * 2
def baseEnd_7145210 : Nat := 3668927107312094566714783

theorem tailTrace_7145210 : CollatzResearch.WordTrace tailWord_7145210 prefixEnd_7145210 3668927107312094566714783 := by
  unfold tailWord_7145210
  simp only [CollatzResearch.WordTrace]
  refine ⟨65151804611032987389922271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173738145629421299706459389 65151804611032987389922271)
  ·
    refine ⟨97727706916549481084883407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65151804611032987389922271 97727706916549481084883407)
    ·
      refine ⟨146591560374824221627325111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97727706916549481084883407 146591560374824221627325111)
      ·
        refine ⟨219887340562236332440987667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146591560374824221627325111 219887340562236332440987667)
        ·
          refine ⟨329831010843354498661481501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219887340562236332440987667 329831010843354498661481501)
          ·
            refine ⟨123686629066257936998055563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329831010843354498661481501 123686629066257936998055563)
            ·
              refine ⟨185529943599386905497083345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123686629066257936998055563 185529943599386905497083345)
              ·
                refine ⟨139147457699540179122812509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185529943599386905497083345 139147457699540179122812509)
                ·
                  refine ⟨52180296637327567171054691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139147457699540179122812509 52180296637327567171054691)
                  ·
                    refine ⟨78270444955991350756582037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52180296637327567171054691 78270444955991350756582037)
                    ·
                      refine ⟨3668927107312094566714783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78270444955991350756582037 3668927107312094566714783)
                      ·
                        rfl

theorem cell23_7145210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_7145210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145210 prefixEnd_7145210 := by exact prefixLift 7145210
  have htrace : WordTrace (prefixWord ++ tailWord_7145210) baseStart_7145210 baseEnd_7145210 := by
    simpa [prefixWord, tailWord_7145210, baseEnd_7145210] using wordTrace_append hprefix tailTrace_7145210
  have hstable : (prefixWord ++ tailWord_7145210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145210).length < 2 ^ (prefixWord ++ tailWord_7145210).sum := by decide
  have hdescent : baseEnd_7145210 < baseStart_7145210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145234 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7145234 : Nat := 118140960795 + 7145234 * 2 ^ 59
def prefixEnd_7145234 : Nat := 4983230072969 + 3 ^ 40 * 7145234 * 2
def baseEnd_7145234 : Nat := 3668939430847802472814673

theorem tailTrace_7145234 : CollatzResearch.WordTrace tailWord_7145234 prefixEnd_7145234 3668939430847802472814673 := by
  unfold tailWord_7145234
  simp only [CollatzResearch.WordTrace]
  refine ⟨65152023449011250414640689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173738729197363334439041837 65152023449011250414640689)
  ·
    refine ⟨48864017586758437810980517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65152023449011250414640689 48864017586758437810980517)
    ·
      refine ⟨9162003297517207089558847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48864017586758437810980517 9162003297517207089558847)
      ·
        refine ⟨13743004946275810634338271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9162003297517207089558847 13743004946275810634338271)
        ·
          refine ⟨20614507419413715951507407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13743004946275810634338271 20614507419413715951507407)
          ·
            refine ⟨30921761129120573927261111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20614507419413715951507407 30921761129120573927261111)
            ·
              refine ⟨46382641693680860890891667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30921761129120573927261111 46382641693680860890891667)
              ·
                refine ⟨69573962540521291336337501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46382641693680860890891667 69573962540521291336337501)
                ·
                  refine ⟨26090235952695484251126563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69573962540521291336337501 26090235952695484251126563)
                  ·
                    refine ⟨39135353929043226376689845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26090235952695484251126563 39135353929043226376689845)
                    ·
                      refine ⟨3668939430847802472814673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39135353929043226376689845 3668939430847802472814673)
                      ·
                        rfl

theorem cell23_7145234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7145234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145234 prefixEnd_7145234 := by exact prefixLift 7145234
  have htrace : WordTrace (prefixWord ++ tailWord_7145234) baseStart_7145234 baseEnd_7145234 := by
    simpa [prefixWord, tailWord_7145234, baseEnd_7145234] using wordTrace_append hprefix tailTrace_7145234
  have hstable : (prefixWord ++ tailWord_7145234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145234).length < 2 ^ (prefixWord ++ tailWord_7145234).sum := by decide
  have hdescent : baseEnd_7145234 < baseStart_7145234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145265 : List Nat := [1, 2, 2, 3, 2, 4, 1, 3, 1, 2, 2]
def baseStart_7145265 : Nat := 118140960795 + 7145265 * 2 ^ 59
def prefixEnd_7145265 : Nat := 4983230072969 + 3 ^ 40 * 7145265 * 2
def baseEnd_7145265 : Nat := 3668955348748091851527031

theorem tailTrace_7145265 : CollatzResearch.WordTrace tailWord_7145265 prefixEnd_7145265 3668955348748091851527031 := by
  unfold tailWord_7145265
  simp only [CollatzResearch.WordTrace]
  refine ⟨260609224458932693952941249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173739482972621795968627499 260609224458932693952941249)
  ·
    refine ⟨195456918344199520464705937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260609224458932693952941249 195456918344199520464705937)
    ·
      refine ⟨146592688758149640348529453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195456918344199520464705937 146592688758149640348529453)
      ·
        refine ⟨54972258284306115130698545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146592688758149640348529453 54972258284306115130698545)
        ·
          refine ⟨41229193713229586348023909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54972258284306115130698545 41229193713229586348023909)
          ·
            refine ⟨7730473821230547440254483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41229193713229586348023909 7730473821230547440254483)
            ·
              refine ⟨11595710731845821160381725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730473821230547440254483 11595710731845821160381725)
              ·
                refine ⟨4348391524442182935143147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11595710731845821160381725 4348391524442182935143147)
                ·
                  refine ⟨6522587286663274402714721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348391524442182935143147 6522587286663274402714721)
                  ·
                    refine ⟨4891940464997455802036041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6522587286663274402714721 4891940464997455802036041)
                    ·
                      refine ⟨3668955348748091851527031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891940464997455802036041 3668955348748091851527031)
                      ·
                        rfl

theorem cell23_7145265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_7145265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145265 prefixEnd_7145265 := by exact prefixLift 7145265
  have htrace : WordTrace (prefixWord ++ tailWord_7145265) baseStart_7145265 baseEnd_7145265 := by
    simpa [prefixWord, tailWord_7145265, baseEnd_7145265] using wordTrace_append hprefix tailTrace_7145265
  have hstable : (prefixWord ++ tailWord_7145265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145265).length < 2 ^ (prefixWord ++ tailWord_7145265).sum := by decide
  have hdescent : baseEnd_7145265 < baseStart_7145265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145298 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_7145298 : Nat := 118140960795 + 7145298 * 2 ^ 59
def prefixEnd_7145298 : Nat := 4983230072969 + 3 ^ 40 * 7145298 * 2
def baseEnd_7145298 : Nat := 3668972293609690222414379

theorem tailTrace_7145298 : CollatzResearch.WordTrace tailWord_7145298 prefixEnd_7145298 3668972293609690222414379 := by
  unfold tailWord_7145298
  simp only [CollatzResearch.WordTrace]
  refine ⟨65152607016953285147223137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173740285378542093725928365 65152607016953285147223137)
  ·
    refine ⟨48864455262714963860417353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65152607016953285147223137 48864455262714963860417353)
    ·
      refine ⟨36648341447036222895313015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48864455262714963860417353 36648341447036222895313015)
      ·
        refine ⟨54972512170554334342969523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36648341447036222895313015 54972512170554334342969523)
        ·
          refine ⟨82458768255831501514454285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54972512170554334342969523 82458768255831501514454285)
          ·
            refine ⟨30922038095936813067920357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82458768255831501514454285 30922038095936813067920357)
            ·
              refine ⟨5797882142988152450235067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30922038095936813067920357 5797882142988152450235067)
              ·
                refine ⟨8696823214482228675352601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797882142988152450235067 8696823214482228675352601)
                ·
                  refine ⟨6522617410861671506514451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8696823214482228675352601 6522617410861671506514451)
                  ·
                    refine ⟨9783926116292507259771677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522617410861671506514451 9783926116292507259771677)
                    ·
                      refine ⟨3668972293609690222414379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9783926116292507259771677 3668972293609690222414379)
                      ·
                        rfl

theorem cell23_7145298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_7145298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145298 prefixEnd_7145298 := by exact prefixLift 7145298
  have htrace : WordTrace (prefixWord ++ tailWord_7145298) baseStart_7145298 baseEnd_7145298 := by
    simpa [prefixWord, tailWord_7145298, baseEnd_7145298] using wordTrace_append hprefix tailTrace_7145298
  have hstable : (prefixWord ++ tailWord_7145298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145298).length < 2 ^ (prefixWord ++ tailWord_7145298).sum := by decide
  have hdescent : baseEnd_7145298 < baseStart_7145298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145308 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7145308 : Nat := 118140960795 + 7145308 * 2 ^ 59
def prefixEnd_7145308 : Nat := 4983230072969 + 3 ^ 40 * 7145308 * 2
def baseEnd_7145308 : Nat := 3668977428416235183289333

theorem tailTrace_7145308 : CollatzResearch.WordTrace tailWord_7145308 prefixEnd_7145308 3668977428416235183289333 := by
  unfold tailWord_7145308
  simp only [CollatzResearch.WordTrace]
  refine ⟨130305396398888456148378289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173740528531851274864504385 130305396398888456148378289)
  ·
    refine ⟨97729047299166342111283717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130305396398888456148378289 97729047299166342111283717)
    ·
      refine ⟨18324196368593689145865697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97729047299166342111283717 18324196368593689145865697)
      ·
        refine ⟨13743147276445266859399273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18324196368593689145865697 13743147276445266859399273)
        ·
          refine ⟨10307360457333950144549455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13743147276445266859399273 10307360457333950144549455)
          ·
            refine ⟨15461040686000925216824183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307360457333950144549455 15461040686000925216824183)
            ·
              refine ⟨23191561029001387825236275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15461040686000925216824183 23191561029001387825236275)
              ·
                refine ⟨34787341543502081737854413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23191561029001387825236275 34787341543502081737854413)
                ·
                  refine ⟨13045253078813280651695405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34787341543502081737854413 13045253078813280651695405)
                  ·
                    refine ⟨4891969904554980244385777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13045253078813280651695405 4891969904554980244385777)
                    ·
                      refine ⟨3668977428416235183289333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4891969904554980244385777 3668977428416235183289333)
                      ·
                        rfl

theorem cell23_7145308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7145308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145308 prefixEnd_7145308 := by exact prefixLift 7145308
  have htrace : WordTrace (prefixWord ++ tailWord_7145308) baseStart_7145308 baseEnd_7145308 := by
    simpa [prefixWord, tailWord_7145308, baseEnd_7145308] using wordTrace_append hprefix tailTrace_7145308
  have hstable : (prefixWord ++ tailWord_7145308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145308).length < 2 ^ (prefixWord ++ tailWord_7145308).sum := by decide
  have hdescent : baseEnd_7145308 < baseStart_7145308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145317 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_7145317 : Nat := 118140960795 + 7145317 * 2 ^ 59
def prefixEnd_7145317 : Nat := 4983230072969 + 3 ^ 40 * 7145317 * 2
def baseEnd_7145317 : Nat := 3668982049742125648076791

theorem tailTrace_7145317 : CollatzResearch.WordTrace tailWord_7145317 prefixEnd_7145317 3668982049742125648076791 := by
  unfold tailWord_7145317
  simp only [CollatzResearch.WordTrace]
  refine ⟨260611121054744306833834205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173740747369829537889222803 260611121054744306833834205)
  ·
    refine ⟨97729170395529115062687827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260611121054744306833834205 97729170395529115062687827)
    ·
      refine ⟨146593755593293672594031741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97729170395529115062687827 146593755593293672594031741)
      ·
        refine ⟨54972658347485127222761903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146593755593293672594031741 54972658347485127222761903)
        ·
          refine ⟨82458987521227690834142855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54972658347485127222761903 82458987521227690834142855)
          ·
            refine ⟨123688481281841536251214283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82458987521227690834142855 123688481281841536251214283)
            ·
              refine ⟨185532721922762304376821425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123688481281841536251214283 185532721922762304376821425)
              ·
                refine ⟨139149541442071728282616069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185532721922762304376821425 139149541442071728282616069)
                ·
                  refine ⟨26090539020388449052990513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139149541442071728282616069 26090539020388449052990513)
                  ·
                    refine ⟨19567904265291336789742885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26090539020388449052990513 19567904265291336789742885)
                    ·
                      refine ⟨3668982049742125648076791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19567904265291336789742885 3668982049742125648076791)
                      ·
                        rfl

theorem cell23_7145317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_7145317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145317 prefixEnd_7145317 := by exact prefixLift 7145317
  have htrace : WordTrace (prefixWord ++ tailWord_7145317) baseStart_7145317 baseEnd_7145317 := by
    simpa [prefixWord, tailWord_7145317, baseEnd_7145317] using wordTrace_append hprefix tailTrace_7145317
  have hstable : (prefixWord ++ tailWord_7145317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145317).length < 2 ^ (prefixWord ++ tailWord_7145317).sum := by decide
  have hdescent : baseEnd_7145317 < baseStart_7145317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145344 : List Nat := [2, 1, 1, 2, 1, 2, 5, 4, 5]
def baseStart_7145344 : Nat := 118140960795 + 7145344 * 2 ^ 59
def prefixEnd_7145344 : Nat := 4983230072969 + 3 ^ 40 * 7145344 * 2
def baseEnd_7145344 : Nat := 407666212635533004715463

theorem tailTrace_7145344 : CollatzResearch.WordTrace tailWord_7145344 prefixEnd_7145344 407666212635533004715463 := by
  unfold tailWord_7145344
  simp only [CollatzResearch.WordTrace]
  refine ⟨130306052912823245222533543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173741403883764326963378057 130306052912823245222533543)
  ·
    refine ⟨195459079369234867833800315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130306052912823245222533543 195459079369234867833800315)
    ·
      refine ⟨293188619053852301750700473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195459079369234867833800315 293188619053852301750700473)
      ·
        refine ⟨219891464290389226313025355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293188619053852301750700473 219891464290389226313025355)
        ·
          refine ⟨329837196435583839469538033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219891464290389226313025355 329837196435583839469538033)
          ·
            refine ⟨247377897326687879602153525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329837196435583839469538033 247377897326687879602153525)
            ·
              refine ⟨23191677874376988712701893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247377897326687879602153525 23191677874376988712701893)
              ·
                refine ⟨4348439601445685383631605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23191677874376988712701893 4348439601445685383631605)
                ·
                  refine ⟨407666212635533004715463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4348439601445685383631605 407666212635533004715463)
                  ·
                    rfl

theorem cell23_7145344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 5].length) (baseStart_7145344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145344 prefixEnd_7145344 := by exact prefixLift 7145344
  have htrace : WordTrace (prefixWord ++ tailWord_7145344) baseStart_7145344 baseEnd_7145344 := by
    simpa [prefixWord, tailWord_7145344, baseEnd_7145344] using wordTrace_append hprefix tailTrace_7145344
  have hstable : (prefixWord ++ tailWord_7145344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145344).length < 2 ^ (prefixWord ++ tailWord_7145344).sum := by decide
  have hdescent : baseEnd_7145344 < baseStart_7145344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145378 : List Nat := [3, 3, 1, 2, 3, 1, 2, 3, 5]
def baseStart_7145378 : Nat := 118140960795 + 7145378 * 2 ^ 59
def prefixEnd_7145378 : Nat := 4983230072969 + 3 ^ 40 * 7145378 * 2
def baseEnd_7145378 : Nat := 407668152451338878823779

theorem tailTrace_7145378 : CollatzResearch.WordTrace tailWord_7145378 prefixEnd_7145378 407668152451338878823779 := by
  unfold tailWord_7145378
  simp only [CollatzResearch.WordTrace]
  refine ⟨65153336476880828562951197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173742230605015542834536525 65153336476880828562951197)
  ·
    refine ⟨24432501178830310711106699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65153336476880828562951197 24432501178830310711106699)
    ·
      refine ⟨36648751768245466066660049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24432501178830310711106699 36648751768245466066660049)
      ·
        refine ⟨27486563826184099549995037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36648751768245466066660049 27486563826184099549995037)
        ·
          refine ⟨10307461434819037331248139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27486563826184099549995037 10307461434819037331248139)
          ·
            refine ⟨15461192152228555996872209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307461434819037331248139 15461192152228555996872209)
            ·
              refine ⟨11595894114171416997654157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15461192152228555996872209 11595894114171416997654157)
              ·
                refine ⟨4348460292814281374120309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11595894114171416997654157 4348460292814281374120309)
                ·
                  refine ⟨407668152451338878823779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4348460292814281374120309 407668152451338878823779)
                  ·
                    rfl

theorem cell23_7145378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_7145378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145378 prefixEnd_7145378 := by exact prefixLift 7145378
  have htrace : WordTrace (prefixWord ++ tailWord_7145378) baseStart_7145378 baseEnd_7145378 := by
    simpa [prefixWord, tailWord_7145378, baseEnd_7145378] using wordTrace_append hprefix tailTrace_7145378
  have hstable : (prefixWord ++ tailWord_7145378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145378).length < 2 ^ (prefixWord ++ tailWord_7145378).sum := by decide
  have hdescent : baseEnd_7145378 < baseStart_7145378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145394 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_7145394 : Nat := 118140960795 + 7145394 * 2 ^ 59
def prefixEnd_7145394 : Nat := 4983230072969 + 3 ^ 40 * 7145394 * 2
def baseEnd_7145394 : Nat := 3669021587752521846813937

theorem tailTrace_7145394 : CollatzResearch.WordTrace tailWord_7145394 prefixEnd_7145394 3669021587752521846813937 := by
  unfold tailWord_7145394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65153482368866337246096809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173742619650310232656258157 65153482368866337246096809)
  ·
    refine ⟨48865111776649752934572607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65153482368866337246096809 48865111776649752934572607)
    ·
      refine ⟨73297667664974629401858911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48865111776649752934572607 73297667664974629401858911)
      ·
        refine ⟨109946501497461944102788367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73297667664974629401858911 109946501497461944102788367)
        ·
          refine ⟨164919752246192916154182551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109946501497461944102788367 164919752246192916154182551)
          ·
            refine ⟨247379628369289374231273827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164919752246192916154182551 247379628369289374231273827)
            ·
              refine ⟨371069442553934061346910741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247379628369289374231273827 371069442553934061346910741)
              ·
                refine ⟨17393880119715659125636441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 371069442553934061346910741 17393880119715659125636441)
                ·
                  refine ⟨13045410089786744344227331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17393880119715659125636441 13045410089786744344227331)
                  ·
                    refine ⟨19568115134680116516340997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13045410089786744344227331 19568115134680116516340997)
                    ·
                      refine ⟨3669021587752521846813937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19568115134680116516340997 3669021587752521846813937)
                      ·
                        rfl

theorem cell23_7145394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_7145394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145394 prefixEnd_7145394 := by exact prefixLift 7145394
  have htrace : WordTrace (prefixWord ++ tailWord_7145394) baseStart_7145394 baseEnd_7145394 := by
    simpa [prefixWord, tailWord_7145394, baseEnd_7145394] using wordTrace_append hprefix tailTrace_7145394
  have hstable : (prefixWord ++ tailWord_7145394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145394).length < 2 ^ (prefixWord ++ tailWord_7145394).sum := by decide
  have hdescent : baseEnd_7145394 < baseStart_7145394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145407 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_7145407 : Nat := 118140960795 + 7145407 * 2 ^ 59
def prefixEnd_7145407 : Nat := 4983230072969 + 3 ^ 40 * 7145407 * 2
def baseEnd_7145407 : Nat := 3669028263001030295951377

theorem tailTrace_7145407 : CollatzResearch.WordTrace tailWord_7145407 prefixEnd_7145407 3669028263001030295951377 := by
  unfold tailWord_7145407
  simp only [CollatzResearch.WordTrace]
  refine ⟨260614403624418252204610475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173742935749612168136406983 260614403624418252204610475)
  ·
    refine ⟨390921605436627378306915713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260614403624418252204610475 390921605436627378306915713)
    ·
      refine ⟨293191204077470533730186785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390921605436627378306915713 293191204077470533730186785)
      ·
        refine ⟨219893403058102900297640089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293191204077470533730186785 219893403058102900297640089)
        ·
          refine ⟨164920052293577175223230067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219893403058102900297640089 164920052293577175223230067)
          ·
            refine ⟨247380078440365762834845101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164920052293577175223230067 247380078440365762834845101)
            ·
              refine ⟨92767529415137161063066913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247380078440365762834845101 92767529415137161063066913)
              ·
                refine ⟨69575647061352870797300185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92767529415137161063066913 69575647061352870797300185)
                ·
                  refine ⟨52181735296014653097975139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69575647061352870797300185 52181735296014653097975139)
                  ·
                    refine ⟨78272602944021979646962709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52181735296014653097975139 78272602944021979646962709)
                    ·
                      refine ⟨3669028263001030295951377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78272602944021979646962709 3669028263001030295951377)
                      ·
                        rfl

theorem cell23_7145407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_7145407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145407 prefixEnd_7145407 := by exact prefixLift 7145407
  have htrace : WordTrace (prefixWord ++ tailWord_7145407) baseStart_7145407 baseEnd_7145407 := by
    simpa [prefixWord, tailWord_7145407, baseEnd_7145407] using wordTrace_append hprefix tailTrace_7145407
  have hstable : (prefixWord ++ tailWord_7145407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145407).length < 2 ^ (prefixWord ++ tailWord_7145407).sum := by decide
  have hdescent : baseEnd_7145407 < baseStart_7145407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145498 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_7145498 : Nat := 118140960795 + 7145498 * 2 ^ 59
def prefixEnd_7145498 : Nat := 4983230072969 + 3 ^ 40 * 7145498 * 2
def baseEnd_7145498 : Nat := 1223024996580196479971153

theorem tailTrace_7145498 : CollatzResearch.WordTrace tailWord_7145498 prefixEnd_7145498 1223024996580196479971153 := by
  unfold tailWord_7145498
  simp only [CollatzResearch.WordTrace]
  refine ⟨65154430666772143686543287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173745148444725716497448765 65154430666772143686543287)
  ·
    refine ⟨97731646000158215529814931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65154430666772143686543287 97731646000158215529814931)
    ·
      refine ⟨146597469000237323294722397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97731646000158215529814931 146597469000237323294722397)
      ·
        refine ⟨54974050875088996235520899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146597469000237323294722397 54974050875088996235520899)
        ·
          refine ⟨82461076312633494353281349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54974050875088996235520899 82461076312633494353281349)
          ·
            refine ⟨15461451808618780191240253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82461076312633494353281349 15461451808618780191240253)
            ·
              refine ⟨5798044428232042571715095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15461451808618780191240253 5798044428232042571715095)
              ·
                refine ⟨8697066642348063857572643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798044428232042571715095 8697066642348063857572643)
                ·
                  refine ⟨13045599963522095786358965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8697066642348063857572643 13045599963522095786358965)
                  ·
                    refine ⟨1223024996580196479971153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13045599963522095786358965 1223024996580196479971153)
                    ·
                      rfl

theorem cell23_7145498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_7145498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145498 prefixEnd_7145498 := by exact prefixLift 7145498
  have htrace : WordTrace (prefixWord ++ tailWord_7145498) baseStart_7145498 baseEnd_7145498 := by
    simpa [prefixWord, tailWord_7145498, baseEnd_7145498] using wordTrace_append hprefix tailTrace_7145498
  have hstable : (prefixWord ++ tailWord_7145498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145498).length < 2 ^ (prefixWord ++ tailWord_7145498).sum := by decide
  have hdescent : baseEnd_7145498 < baseStart_7145498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145521 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_7145521 : Nat := 118140960795 + 7145521 * 2 ^ 59
def prefixEnd_7145521 : Nat := 4983230072969 + 3 ^ 40 * 7145521 * 2
def baseEnd_7145521 : Nat := 3669086799795642849925853

theorem tailTrace_7145521 : CollatzResearch.WordTrace tailWord_7145521 prefixEnd_7145521 3669086799795642849925853 := by
  unfold tailWord_7145521
  simp only [CollatzResearch.WordTrace]
  refine ⟨260618561546005249674260417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173745707697336833116173611 260618561546005249674260417)
  ·
    refine ⟨195463921159503937255695313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260618561546005249674260417 195463921159503937255695313)
    ·
      refine ⟨146597940869627952941771485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195463921159503937255695313 146597940869627952941771485)
      ·
        refine ⟨54974227826110482353164307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146597940869627952941771485 54974227826110482353164307)
        ·
          refine ⟨82461341739165723529746461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54974227826110482353164307 82461341739165723529746461)
          ·
            refine ⟨30923003152187146323654923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82461341739165723529746461 30923003152187146323654923)
            ·
              refine ⟨46384504728280719485482385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30923003152187146323654923 46384504728280719485482385)
              ·
                refine ⟨34788378546210539614111789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46384504728280719485482385 34788378546210539614111789)
                ·
                  refine ⟨13045641954828952355291921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34788378546210539614111789 13045641954828952355291921)
                  ·
                    refine ⟨9784231466121714266468941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13045641954828952355291921 9784231466121714266468941)
                    ·
                      refine ⟨3669086799795642849925853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9784231466121714266468941 3669086799795642849925853)
                      ·
                        rfl

theorem cell23_7145521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_7145521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145521 prefixEnd_7145521 := by exact prefixLift 7145521
  have htrace : WordTrace (prefixWord ++ tailWord_7145521) baseStart_7145521 baseEnd_7145521 := by
    simpa [prefixWord, tailWord_7145521, baseEnd_7145521] using wordTrace_append hprefix tailTrace_7145521
  have hstable : (prefixWord ++ tailWord_7145521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145521).length < 2 ^ (prefixWord ++ tailWord_7145521).sum := by decide
  have hdescent : baseEnd_7145521 < baseStart_7145521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145551 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 3]
def baseStart_7145551 : Nat := 118140960795 + 7145551 * 2 ^ 59
def prefixEnd_7145551 : Nat := 4983230072969 + 3 ^ 40 * 7145551 * 2
def baseEnd_7145551 : Nat := 3669102204215277732550715

theorem tailTrace_7145551 : CollatzResearch.WordTrace tailWord_7145551 prefixEnd_7145551 3669102204215277732550715 := by
  unfold tailWord_7145551
  simp only [CollatzResearch.WordTrace]
  refine ⟨260619655735896564797852507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173746437157264376531901671 260619655735896564797852507)
  ·
    refine ⟨390929483603844847196778761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260619655735896564797852507 390929483603844847196778761)
    ·
      refine ⟨293197112702883635397584071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390929483603844847196778761 293197112702883635397584071)
      ·
        refine ⟨439795669054325453096376107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293197112702883635397584071 439795669054325453096376107)
        ·
          refine ⟨659693503581488179644564161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439795669054325453096376107 659693503581488179644564161)
          ·
            refine ⟨494770127686116134733423121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659693503581488179644564161 494770127686116134733423121)
            ·
              refine ⟨371077595764587101050067341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494770127686116134733423121 371077595764587101050067341)
              ·
                refine ⟨139154098411720162893775253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371077595764587101050067341 139154098411720162893775253)
                ·
                  refine ⟨6522848363049382635645715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139154098411720162893775253 6522848363049382635645715)
                  ·
                    refine ⟨9784272544574073953468573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522848363049382635645715 9784272544574073953468573)
                    ·
                      refine ⟨3669102204215277732550715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9784272544574073953468573 3669102204215277732550715)
                      ·
                        rfl

theorem cell23_7145551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 3].length) (baseStart_7145551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145551 prefixEnd_7145551 := by exact prefixLift 7145551
  have htrace : WordTrace (prefixWord ++ tailWord_7145551) baseStart_7145551 baseEnd_7145551 := by
    simpa [prefixWord, tailWord_7145551, baseEnd_7145551] using wordTrace_append hprefix tailTrace_7145551
  have hstable : (prefixWord ++ tailWord_7145551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145551).length < 2 ^ (prefixWord ++ tailWord_7145551).sum := by decide
  have hdescent : baseEnd_7145551 < baseStart_7145551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145558 : List Nat := [5, 2, 2, 1, 1, 2, 10]
def baseStart_7145558 : Nat := 118140960795 + 7145558 * 2 ^ 59
def prefixEnd_7145558 : Nat := 4983230072969 + 3 ^ 40 * 7145558 * 2
def baseEnd_7145558 : Nat := 45297602451603200063743

theorem tailTrace_7145558 : CollatzResearch.WordTrace tailWord_7145558 prefixEnd_7145558 45297602451603200063743 := by
  unfold tailWord_7145558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288744440429450312084833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173746607364580803328904885 16288744440429450312084833)
  ·
    refine ⟨12216558330322087734063625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16288744440429450312084833 12216558330322087734063625)
    ·
      refine ⟨9162418747741565800547719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12216558330322087734063625 9162418747741565800547719)
      ·
        refine ⟨13743628121612348700821579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9162418747741565800547719 13743628121612348700821579)
        ·
          refine ⟨20615442182418523051232369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13743628121612348700821579 20615442182418523051232369)
          ·
            refine ⟨15461581636813892288424277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20615442182418523051232369 15461581636813892288424277)
            ·
              refine ⟨45297602451603200063743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15461581636813892288424277 45297602451603200063743)
              ·
                rfl

theorem cell23_7145558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 10].length) (baseStart_7145558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145558 prefixEnd_7145558 := by exact prefixLift 7145558
  have htrace : WordTrace (prefixWord ++ tailWord_7145558) baseStart_7145558 baseEnd_7145558 := by
    simpa [prefixWord, tailWord_7145558, baseEnd_7145558] using wordTrace_append hprefix tailTrace_7145558
  have hstable : (prefixWord ++ tailWord_7145558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145558).length < 2 ^ (prefixWord ++ tailWord_7145558).sum := by decide
  have hdescent : baseEnd_7145558 < baseStart_7145558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145568 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 4, 1, 3]
def baseStart_7145568 : Nat := 118140960795 + 7145568 * 2 ^ 59
def prefixEnd_7145568 : Nat := 4983230072969 + 3 ^ 40 * 7145568 * 2
def baseEnd_7145568 : Nat := 3669110933386404166038137

theorem tailTrace_7145568 : CollatzResearch.WordTrace tailWord_7145568 prefixEnd_7145568 3669110933386404166038137 := by
  unfold tailWord_7145568
  simp only [CollatzResearch.WordTrace]
  refine ⟨130310137888417488350610679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173746850517889984467480905 130310137888417488350610679)
  ·
    refine ⟨195465206832626232525916019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130310137888417488350610679 195465206832626232525916019)
    ·
      refine ⟨293197810248939348788874029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195465206832626232525916019 293197810248939348788874029)
      ·
        refine ⟨109949178843352255795827761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293197810248939348788874029 109949178843352255795827761)
        ·
          refine ⟨82461884132514191846870821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109949178843352255795827761 82461884132514191846870821)
          ·
            refine ⟨15461603274846410971288279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82461884132514191846870821 15461603274846410971288279)
            ·
              refine ⟨23192404912269616456932419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15461603274846410971288279 23192404912269616456932419)
              ·
                refine ⟨34788607368404424685398629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23192404912269616456932419 34788607368404424685398629)
                ·
                  refine ⟨6522863881575829628512243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34788607368404424685398629 6522863881575829628512243)
                  ·
                    refine ⟨9784295822363744442768365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522863881575829628512243 9784295822363744442768365)
                    ·
                      refine ⟨3669110933386404166038137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9784295822363744442768365 3669110933386404166038137)
                      ·
                        rfl

theorem cell23_7145568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_7145568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145568 prefixEnd_7145568 := by exact prefixLift 7145568
  have htrace : WordTrace (prefixWord ++ tailWord_7145568) baseStart_7145568 baseEnd_7145568 := by
    simpa [prefixWord, tailWord_7145568, baseEnd_7145568] using wordTrace_append hprefix tailTrace_7145568
  have hstable : (prefixWord ++ tailWord_7145568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145568).length < 2 ^ (prefixWord ++ tailWord_7145568).sum := by decide
  have hdescent : baseEnd_7145568 < baseStart_7145568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145585 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 2, 1, 3]
def baseStart_7145585 : Nat := 118140960795 + 7145585 * 2 ^ 59
def prefixEnd_7145585 : Nat := 4983230072969 + 3 ^ 40 * 7145585 * 2
def baseEnd_7145585 : Nat := 3669119662557530599525559

theorem tailTrace_7145585 : CollatzResearch.WordTrace tailWord_7145585 prefixEnd_7145585 3669119662557530599525559 := by
  unfold tailWord_7145585
  simp only [CollatzResearch.WordTrace]
  refine ⟨260620895817773388604590209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173747263878515592403060139 260620895817773388604590209)
  ·
    refine ⟨195465671863330041453442657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260620895817773388604590209 195465671863330041453442657)
    ·
      refine ⟨146599253897497531090081993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195465671863330041453442657 146599253897497531090081993)
      ·
        refine ⟨109949440423123148317561495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146599253897497531090081993 109949440423123148317561495)
        ·
          refine ⟨164924160634684722476342243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109949440423123148317561495 164924160634684722476342243)
          ·
            refine ⟨247386240952027083714513365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164924160634684722476342243 247386240952027083714513365)
            ·
              refine ⟨5798115022313134774558907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 247386240952027083714513365 5798115022313134774558907)
              ·
                refine ⟨8697172533469702161838361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798115022313134774558907 8697172533469702161838361)
                ·
                  refine ⟨6522879400102276621378771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8697172533469702161838361 6522879400102276621378771)
                  ·
                    refine ⟨9784319100153414932068157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522879400102276621378771 9784319100153414932068157)
                    ·
                      refine ⟨3669119662557530599525559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9784319100153414932068157 3669119662557530599525559)
                      ·
                        rfl

theorem cell23_7145585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_7145585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145585 prefixEnd_7145585 := by exact prefixLift 7145585
  have htrace : WordTrace (prefixWord ++ tailWord_7145585) baseStart_7145585 baseEnd_7145585 := by
    simpa [prefixWord, tailWord_7145585, baseEnd_7145585] using wordTrace_append hprefix tailTrace_7145585
  have hstable : (prefixWord ++ tailWord_7145585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145585).length < 2 ^ (prefixWord ++ tailWord_7145585).sum := by decide
  have hdescent : baseEnd_7145585 < baseStart_7145585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145594 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_7145594 : Nat := 118140960795 + 7145594 * 2 ^ 59
def prefixEnd_7145594 : Nat := 4983230072969 + 3 ^ 40 * 7145594 * 2
def baseEnd_7145594 : Nat := 3669124283883421064313017

theorem tailTrace_7145594 : CollatzResearch.WordTrace tailWord_7145594 prefixEnd_7145594 3669124283883421064313017 := by
  unfold tailWord_7145594
  simp only [CollatzResearch.WordTrace]
  refine ⟨65155306018685195785416959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173747482716493855427778557 65155306018685195785416959)
  ·
    refine ⟨97732959028027793678125439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65155306018685195785416959 97732959028027793678125439)
    ·
      refine ⟨146599438542041690517188159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97732959028027793678125439 146599438542041690517188159)
      ·
        refine ⟨219899157813062535775782239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146599438542041690517188159 219899157813062535775782239)
        ·
          refine ⟨329848736719593803663673359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219899157813062535775782239 329848736719593803663673359)
          ·
            refine ⟨494773105079390705495510039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329848736719593803663673359 494773105079390705495510039)
            ·
              refine ⟨742159657619086058243265059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494773105079390705495510039 742159657619086058243265059)
              ·
                refine ⟨1113239486428629087364897589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742159657619086058243265059 1113239486428629087364897589)
                ·
                  refine ⟨104366201852683976940459149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113239486428629087364897589 104366201852683976940459149)
                  ·
                    refine ⟨39137325694756491352672181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104366201852683976940459149 39137325694756491352672181)
                    ·
                      refine ⟨3669124283883421064313017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39137325694756491352672181 3669124283883421064313017)
                      ·
                        rfl

theorem cell23_7145594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_7145594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145594 prefixEnd_7145594 := by exact prefixLift 7145594
  have htrace : WordTrace (prefixWord ++ tailWord_7145594) baseStart_7145594 baseEnd_7145594 := by
    simpa [prefixWord, tailWord_7145594, baseEnd_7145594] using wordTrace_append hprefix tailTrace_7145594
  have hstable : (prefixWord ++ tailWord_7145594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145594).length < 2 ^ (prefixWord ++ tailWord_7145594).sum := by decide
  have hdescent : baseEnd_7145594 < baseStart_7145594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145646 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7145646 : Nat := 118140960795 + 7145646 * 2 ^ 59
def prefixEnd_7145646 : Nat := 4983230072969 + 3 ^ 40 * 7145646 * 2
def baseEnd_7145646 : Nat := 3669150984877454860862779

theorem tailTrace_7145646 : CollatzResearch.WordTrace tailWord_7145646 prefixEnd_7145646 3669150984877454860862779 := by
  unfold tailWord_7145646
  simp only [CollatzResearch.WordTrace]
  refine ⟨32577890083819049502820099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173748747113701597348373861 32577890083819049502820099)
  ·
    refine ⟨48866835125728574254230149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32577890083819049502820099 48866835125728574254230149)
    ·
      refine ⟨9162531586074107672668153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48866835125728574254230149 9162531586074107672668153)
      ·
        refine ⟨6871898689555580754501115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9162531586074107672668153 6871898689555580754501115)
        ·
          refine ⟨10307848034333371131751673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871898689555580754501115 10307848034333371131751673)
          ·
            refine ⟨7730886025750028348813755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10307848034333371131751673 7730886025750028348813755)
            ·
              refine ⟨11596329038625042523220633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730886025750028348813755 11596329038625042523220633)
              ·
                refine ⟨8697246778968781892415475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11596329038625042523220633 8697246778968781892415475)
                ·
                  refine ⟨13045870168453172838623213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8697246778968781892415475 13045870168453172838623213)
                  ·
                    refine ⟨4892201313169939814483705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13045870168453172838623213 4892201313169939814483705)
                    ·
                      refine ⟨3669150984877454860862779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4892201313169939814483705 3669150984877454860862779)
                      ·
                        rfl

theorem cell23_7145646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7145646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145646 prefixEnd_7145646 := by exact prefixLift 7145646
  have htrace : WordTrace (prefixWord ++ tailWord_7145646) baseStart_7145646 baseEnd_7145646 := by
    simpa [prefixWord, tailWord_7145646, baseEnd_7145646] using wordTrace_append hprefix tailTrace_7145646
  have hstable : (prefixWord ++ tailWord_7145646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145646).length < 2 ^ (prefixWord ++ tailWord_7145646).sum := by decide
  have hdescent : baseEnd_7145646 < baseStart_7145646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145678 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_7145678 : Nat := 118140960795 + 7145678 * 2 ^ 59
def prefixEnd_7145678 : Nat := 4983230072969 + 3 ^ 40 * 7145678 * 2
def baseEnd_7145678 : Nat := 1223055805419466245220877

theorem tailTrace_7145678 : CollatzResearch.WordTrace tailWord_7145678 prefixEnd_7145678 1223055805419466245220877 := by
  unfold tailWord_7145678
  simp only [CollatzResearch.WordTrace]
  refine ⟨32578035975804558185965711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173749525204290976991817125 32578035975804558185965711)
  ·
    refine ⟨48867053963706837278948567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32578035975804558185965711 48867053963706837278948567)
    ·
      refine ⟨73300580945560255918422851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48867053963706837278948567 73300580945560255918422851)
      ·
        refine ⟨109950871418340383877634277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73300580945560255918422851 109950871418340383877634277)
        ·
          refine ⟨20615788390938821977056427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109950871418340383877634277 20615788390938821977056427)
          ·
            refine ⟨30923682586408232965584641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20615788390938821977056427 30923682586408232965584641)
            ·
              refine ⟨23192761939806174724188481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30923682586408232965584641 23192761939806174724188481)
              ·
                refine ⟨17394571454854631043141361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23192761939806174724188481 17394571454854631043141361)
                ·
                  refine ⟨13045928591140973282356021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17394571454854631043141361 13045928591140973282356021)
                  ·
                    refine ⟨1223055805419466245220877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13045928591140973282356021 1223055805419466245220877)
                    ·
                      rfl

theorem cell23_7145678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_7145678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145678 prefixEnd_7145678 := by exact prefixLift 7145678
  have htrace : WordTrace (prefixWord ++ tailWord_7145678) baseStart_7145678 baseEnd_7145678 := by
    simpa [prefixWord, tailWord_7145678, baseEnd_7145678] using wordTrace_append hprefix tailTrace_7145678
  have hstable : (prefixWord ++ tailWord_7145678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145678).length < 2 ^ (prefixWord ++ tailWord_7145678).sum := by decide
  have hdescent : baseEnd_7145678 < baseStart_7145678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145682 : List Nat := [3, 2, 2, 2, 1, 4, 2, 2, 5]
def baseStart_7145682 : Nat := 118140960795 + 7145682 * 2 ^ 59
def prefixEnd_7145682 : Nat := 4983230072969 + 3 ^ 40 * 7145682 * 2
def baseEnd_7145682 : Nat := 407685496686779635556957

theorem tailTrace_7145682 : CollatzResearch.WordTrace tailWord_7145682 prefixEnd_7145682 407685496686779635556957 := by
  unfold tailWord_7145682
  simp only [CollatzResearch.WordTrace]
  refine ⟨65156108424605493542717825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173749622465614649447247533 65156108424605493542717825)
  ·
    refine ⟨48867081318454120157038369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65156108424605493542717825 48867081318454120157038369)
    ·
      refine ⟨36650310988840590117778777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48867081318454120157038369 36650310988840590117778777)
      ·
        refine ⟨27487733241630442588334083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36650310988840590117778777 27487733241630442588334083)
        ·
          refine ⟨41231599862445663882501125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27487733241630442588334083 41231599862445663882501125)
          ·
            refine ⟨7730924974208561977968961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41231599862445663882501125 7730924974208561977968961)
            ·
              refine ⟨5798193730656421483476721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7730924974208561977968961 5798193730656421483476721)
              ·
                refine ⟨4348645297992316112607541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5798193730656421483476721 4348645297992316112607541)
                ·
                  refine ⟨407685496686779635556957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4348645297992316112607541 407685496686779635556957)
                  ·
                    rfl

theorem cell23_7145682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_7145682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145682 prefixEnd_7145682 := by exact prefixLift 7145682
  have htrace : WordTrace (prefixWord ++ tailWord_7145682) baseStart_7145682 baseEnd_7145682 := by
    simpa [prefixWord, tailWord_7145682, baseEnd_7145682] using wordTrace_append hprefix tailTrace_7145682
  have hstable : (prefixWord ++ tailWord_7145682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145682).length < 2 ^ (prefixWord ++ tailWord_7145682).sum := by decide
  have hdescent : baseEnd_7145682 < baseStart_7145682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145692 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7145692 : Nat := 118140960795 + 7145692 * 2 ^ 59
def prefixEnd_7145692 : Nat := 4983230072969 + 3 ^ 40 * 7145692 * 2
def baseEnd_7145692 : Nat := 3669174604987561680887567

theorem tailTrace_7145692 : CollatzResearch.WordTrace tailWord_7145692 prefixEnd_7145692 3669174604987561680887567 := by
  unfold tailWord_7145692
  simp only [CollatzResearch.WordTrace]
  refine ⟨130312399214192872939367665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173749865618923830585823553 130312399214192872939367665)
  ·
    refine ⟨97734299410644654704525749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130312399214192872939367665 97734299410644654704525749)
    ·
      refine ⟨9162590569747936378549289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97734299410644654704525749 9162590569747936378549289)
      ·
        refine ⟨6871942927310952283911967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9162590569747936378549289 6871942927310952283911967)
        ·
          refine ⟨10307914390966428425867951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871942927310952283911967 10307914390966428425867951)
          ·
            refine ⟨15461871586449642638801927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307914390966428425867951 15461871586449642638801927)
            ·
              refine ⟨23192807379674463958202891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15461871586449642638801927 23192807379674463958202891)
              ·
                refine ⟨34789211069511695937304337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23192807379674463958202891 34789211069511695937304337)
                ·
                  refine ⟨26091908302133771952978253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34789211069511695937304337 26091908302133771952978253)
                  ·
                    refine ⟨9784465613300164482366845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26091908302133771952978253 9784465613300164482366845)
                    ·
                      refine ⟨3669174604987561680887567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9784465613300164482366845 3669174604987561680887567)
                      ·
                        rfl

theorem cell23_7145692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7145692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145692 prefixEnd_7145692 := by exact prefixLift 7145692
  have htrace : WordTrace (prefixWord ++ tailWord_7145692) baseStart_7145692 baseEnd_7145692 := by
    simpa [prefixWord, tailWord_7145692, baseEnd_7145692] using wordTrace_append hprefix tailTrace_7145692
  have hstable : (prefixWord ++ tailWord_7145692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145692).length < 2 ^ (prefixWord ++ tailWord_7145692).sum := by decide
  have hdescent : baseEnd_7145692 < baseStart_7145692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145708 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_7145708 : Nat := 118140960795 + 7145708 * 2 ^ 59
def prefixEnd_7145708 : Nat := 4983230072969 + 3 ^ 40 * 7145708 * 2
def baseEnd_7145708 : Nat := 1223060940226011206095831

theorem tailTrace_7145708 : CollatzResearch.WordTrace tailWord_7145708 prefixEnd_7145708 1223060940226011206095831 := by
  unfold tailWord_7145708
  simp only [CollatzResearch.WordTrace]
  refine ⟨130312690998163890305658889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173750254664218520407545185 130312690998163890305658889)
  ·
    refine ⟨97734518248622917729244167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130312690998163890305658889 97734518248622917729244167)
    ·
      refine ⟨146601777372934376593866251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97734518248622917729244167 146601777372934376593866251)
      ·
        refine ⟨219902666059401564890799377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146601777372934376593866251 219902666059401564890799377)
        ·
          refine ⟨164926999544551173668099533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219902666059401564890799377 164926999544551173668099533)
          ·
            refine ⟨61847624829206690125537325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164926999544551173668099533 61847624829206690125537325)
            ·
              refine ⟨23192859310952508797076497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61847624829206690125537325 23192859310952508797076497)
              ·
                refine ⟨17394644483214381597807373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23192859310952508797076497 17394644483214381597807373)
                ·
                  refine ⟨6522991681205393099177765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17394644483214381597807373 6522991681205393099177765)
                  ·
                    refine ⟨1223060940226011206095831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6522991681205393099177765 1223060940226011206095831)
                    ·
                      rfl

theorem cell23_7145708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_7145708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145708 prefixEnd_7145708 := by exact prefixLift 7145708
  have htrace : WordTrace (prefixWord ++ tailWord_7145708) baseStart_7145708 baseEnd_7145708 := by
    simpa [prefixWord, tailWord_7145708, baseEnd_7145708] using wordTrace_append hprefix tailTrace_7145708
  have hstable : (prefixWord ++ tailWord_7145708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145708).length < 2 ^ (prefixWord ++ tailWord_7145708).sum := by decide
  have hdescent : baseEnd_7145708 < baseStart_7145708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145738 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 6]
def baseStart_7145738 : Nat := 118140960795 + 7145738 * 2 ^ 59
def prefixEnd_7145738 : Nat := 4983230072969 + 3 ^ 40 * 7145738 * 2
def baseEnd_7145738 : Nat := 407688691677518722323595

theorem tailTrace_7145738 : CollatzResearch.WordTrace tailWord_7145738 prefixEnd_7145738 407688691677518722323595 := by
  unfold tailWord_7145738
  simp only [CollatzResearch.WordTrace]
  refine ⟨65156619046554773933727467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173750984124146063823273245 65156619046554773933727467)
  ·
    refine ⟨97734928569832160900591201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65156619046554773933727467 97734928569832160900591201)
    ·
      refine ⟨73301196427374120675443401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97734928569832160900591201 73301196427374120675443401)
      ·
        refine ⟨54975897320530590506582551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73301196427374120675443401 54975897320530590506582551)
        ·
          refine ⟨82463845980795885759873827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54975897320530590506582551 82463845980795885759873827)
          ·
            refine ⟨123695768971193828639810741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82463845980795885759873827 123695768971193828639810741)
            ·
              refine ⟨11596478341049421434982257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123695768971193828639810741 11596478341049421434982257)
              ·
                refine ⟨8697358755787066076236693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11596478341049421434982257 8697358755787066076236693)
                ·
                  refine ⟨407688691677518722323595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8697358755787066076236693 407688691677518722323595)
                  ·
                    rfl

theorem cell23_7145738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_7145738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145738 prefixEnd_7145738 := by exact prefixLift 7145738
  have htrace : WordTrace (prefixWord ++ tailWord_7145738) baseStart_7145738 baseEnd_7145738 := by
    simpa [prefixWord, tailWord_7145738, baseEnd_7145738] using wordTrace_append hprefix tailTrace_7145738
  have hstable : (prefixWord ++ tailWord_7145738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145738).length < 2 ^ (prefixWord ++ tailWord_7145738).sum := by decide
  have hdescent : baseEnd_7145738 < baseStart_7145738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145761 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7145761 : Nat := 118140960795 + 7145761 * 2 ^ 59
def prefixEnd_7145761 : Nat := 4983230072969 + 3 ^ 40 * 7145761 * 2
def baseEnd_7145761 : Nat := 3669210035152721910924749

theorem tailTrace_7145761 : CollatzResearch.WordTrace tailWord_7145761 prefixEnd_7145761 3669210035152721910924749 := by
  unfold tailWord_7145761
  simp only [CollatzResearch.WordTrace]
  refine ⟨260627315065135770662997137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173751543376757180441998091 260627315065135770662997137)
  ·
    refine ⟨195470486298851827997247853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260627315065135770662997137 195470486298851827997247853)
    ·
      refine ⟨73301432362069435498967945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195470486298851827997247853 73301432362069435498967945)
      ·
        refine ⟨54976074271552076624225959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73301432362069435498967945 54976074271552076624225959)
        ·
          refine ⟨82464111407328114936338939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54976074271552076624225959 82464111407328114936338939)
          ·
            refine ⟨123696167110992172404508409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82464111407328114936338939 123696167110992172404508409)
            ·
              refine ⟨92772125333244129303381307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123696167110992172404508409 92772125333244129303381307)
              ·
                refine ⟨139158187999866193955071961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92772125333244129303381307 139158187999866193955071961)
                ·
                  refine ⟨104368640999899645466303971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139158187999866193955071961 104368640999899645466303971)
                  ·
                    refine ⟨156552961499849468199455957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104368640999899645466303971 156552961499849468199455957)
                    ·
                      refine ⟨3669210035152721910924749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156552961499849468199455957 3669210035152721910924749)
                      ·
                        rfl

theorem cell23_7145761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7145761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145761 prefixEnd_7145761 := by exact prefixLift 7145761
  have htrace : WordTrace (prefixWord ++ tailWord_7145761) baseStart_7145761 baseEnd_7145761 := by
    simpa [prefixWord, tailWord_7145761, baseEnd_7145761] using wordTrace_append hprefix tailTrace_7145761
  have hstable : (prefixWord ++ tailWord_7145761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145761).length < 2 ^ (prefixWord ++ tailWord_7145761).sum := by decide
  have hdescent : baseEnd_7145761 < baseStart_7145761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145785 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 1, 5]
def baseStart_7145785 : Nat := 118140960795 + 7145785 * 2 ^ 59
def prefixEnd_7145785 : Nat := 4983230072969 + 3 ^ 40 * 7145785 * 2
def baseEnd_7145785 : Nat := 1223074119562809939008213

theorem tailTrace_7145785 : CollatzResearch.WordTrace tailWord_7145785 prefixEnd_7145785 1223074119562809939008213 := by
  unfold tailWord_7145785
  simp only [CollatzResearch.WordTrace]
  refine ⟨260628190417048822761870809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173752126944699215174580539 260628190417048822761870809)
  ·
    refine ⟨195471142812786617071403107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260628190417048822761870809 195471142812786617071403107)
    ·
      refine ⟨293206714219179925607104661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195471142812786617071403107 293206714219179925607104661)
      ·
        refine ⟨13744064729024059012833031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 293206714219179925607104661 13744064729024059012833031)
        ·
          refine ⟨20616097093536088519249547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13744064729024059012833031 20616097093536088519249547)
          ·
            refine ⟨30924145640304132778874321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20616097093536088519249547 30924145640304132778874321)
            ·
              refine ⟨23193109230228099584155741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30924145640304132778874321 23193109230228099584155741)
              ·
                refine ⟨8697415961335537344058403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23193109230228099584155741 8697415961335537344058403)
                ·
                  refine ⟨13046123942003306016087605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8697415961335537344058403 13046123942003306016087605)
                  ·
                    refine ⟨1223074119562809939008213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13046123942003306016087605 1223074119562809939008213)
                    ·
                      rfl

theorem cell23_7145785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_7145785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145785 prefixEnd_7145785 := by exact prefixLift 7145785
  have htrace : WordTrace (prefixWord ++ tailWord_7145785) baseStart_7145785 baseEnd_7145785 := by
    simpa [prefixWord, tailWord_7145785, baseEnd_7145785] using wordTrace_append hprefix tailTrace_7145785
  have hstable : (prefixWord ++ tailWord_7145785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145785).length < 2 ^ (prefixWord ++ tailWord_7145785).sum := by decide
  have hdescent : baseEnd_7145785 < baseStart_7145785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145799 : List Nat := [1, 1, 4, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_7145799 : Nat := 118140960795 + 7145799 * 2 ^ 59
def prefixEnd_7145799 : Nat := 4983230072969 + 3 ^ 40 * 7145799 * 2
def baseEnd_7145799 : Nat := 3669229547417592762249575

theorem tailTrace_7145799 : CollatzResearch.WordTrace tailWord_7145799 prefixEnd_7145799 3669229547417592762249575 := by
  unfold tailWord_7145799
  simp only [CollatzResearch.WordTrace]
  refine ⟨260628701038998103152880451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173752467359332068768586967 260628701038998103152880451)
  ·
    refine ⟨390943051558497154729320677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260628701038998103152880451 390943051558497154729320677)
    ·
      refine ⟨73301822167218216511747627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390943051558497154729320677 73301822167218216511747627)
      ·
        refine ⟨109952733250827324767621441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73301822167218216511747627 109952733250827324767621441)
        ·
          refine ⟨82464549938120493575716081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109952733250827324767621441 82464549938120493575716081)
          ·
            refine ⟨61848412453590370181787061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82464549938120493575716081 61848412453590370181787061)
            ·
              refine ⟨5798288667524097204542537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61848412453590370181787061 5798288667524097204542537)
              ·
                refine ⟨4348716500643072903406903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5798288667524097204542537 4348716500643072903406903)
                ·
                  refine ⟨6523074750964609355110355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348716500643072903406903 6523074750964609355110355)
                  ·
                    refine ⟨9784612126446914032665533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6523074750964609355110355 9784612126446914032665533)
                    ·
                      refine ⟨3669229547417592762249575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9784612126446914032665533 3669229547417592762249575)
                      ·
                        rfl

theorem cell23_7145799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_7145799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145799 prefixEnd_7145799 := by exact prefixLift 7145799
  have htrace : WordTrace (prefixWord ++ tailWord_7145799) baseStart_7145799 baseEnd_7145799 := by
    simpa [prefixWord, tailWord_7145799, baseEnd_7145799] using wordTrace_append hprefix tailTrace_7145799
  have hstable : (prefixWord ++ tailWord_7145799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145799).length < 2 ^ (prefixWord ++ tailWord_7145799).sum := by decide
  have hdescent : baseEnd_7145799 < baseStart_7145799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145808 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_7145808 : Nat := 118140960795 + 7145808 * 2 ^ 59
def prefixEnd_7145808 : Nat := 4983230072969 + 3 ^ 40 * 7145808 * 2
def baseEnd_7145808 : Nat := 3669234168743483227037033

theorem tailTrace_7145808 : CollatzResearch.WordTrace tailWord_7145808 prefixEnd_7145808 3669234168743483227037033 := by
  unfold tailWord_7145808
  simp only [CollatzResearch.WordTrace]
  refine ⟨130314514647982748844979039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173752686197310331793305385 130314514647982748844979039)
  ·
    refine ⟨195471771971974123267468559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130314514647982748844979039 195471771971974123267468559)
    ·
      refine ⟨293207657957961184901202839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195471771971974123267468559 293207657957961184901202839)
      ·
        refine ⟨439811486936941777351804259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293207657957961184901202839 439811486936941777351804259)
        ·
          refine ⟨659717230405412666027706389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439811486936941777351804259 659717230405412666027706389)
          ·
            refine ⟨30924245175253718720048737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 659717230405412666027706389 30924245175253718720048737)
            ·
              refine ⟨23193183881440289040036553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30924245175253718720048737 23193183881440289040036553)
              ·
                refine ⟨17394887911080216780027415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23193183881440289040036553 17394887911080216780027415)
                ·
                  refine ⟨26092331866620325170041123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17394887911080216780027415 26092331866620325170041123)
                  ·
                    refine ⟨39138497799930487755061685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26092331866620325170041123 39138497799930487755061685)
                    ·
                      refine ⟨3669234168743483227037033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39138497799930487755061685 3669234168743483227037033)
                      ·
                        rfl

theorem cell23_7145808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_7145808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145808 prefixEnd_7145808 := by exact prefixLift 7145808
  have htrace : WordTrace (prefixWord ++ tailWord_7145808) baseStart_7145808 baseEnd_7145808 := by
    simpa [prefixWord, tailWord_7145808, baseEnd_7145808] using wordTrace_append hprefix tailTrace_7145808
  have hstable : (prefixWord ++ tailWord_7145808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145808).length < 2 ^ (prefixWord ++ tailWord_7145808).sum := by decide
  have hdescent : baseEnd_7145808 < baseStart_7145808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145815 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 2, 4]
def baseStart_7145815 : Nat := 118140960795 + 7145815 * 2 ^ 59
def prefixEnd_7145815 : Nat := 4983230072969 + 3 ^ 40 * 7145815 * 2
def baseEnd_7145815 : Nat := 1223079254369354899883167

theorem tailTrace_7145815 : CollatzResearch.WordTrace tailWord_7145815 prefixEnd_7145815 1223079254369354899883167 := by
  unfold tailWord_7145815
  simp only [CollatzResearch.WordTrace]
  refine ⟨260629284606940137885462899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173752856404626758590308599 260629284606940137885462899)
  ·
    refine ⟨390943926910410206828194349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260629284606940137885462899 390943926910410206828194349)
    ·
      refine ⟨146603972591403827560572881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390943926910410206828194349 146603972591403827560572881)
      ·
        refine ⟨109952979443552870670429661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146603972591403827560572881 109952979443552870670429661)
        ·
          refine ⟨41232367291332326501411123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109952979443552870670429661 41232367291332326501411123)
          ·
            refine ⟨61848550936998489752116685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41232367291332326501411123 61848550936998489752116685)
            ·
              refine ⟨23193206601374433657043757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61848550936998489752116685 23193206601374433657043757)
              ·
                refine ⟨8697452475515412621391409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23193206601374433657043757 8697452475515412621391409)
                ·
                  refine ⟨6523089356636559466043557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8697452475515412621391409 6523089356636559466043557)
                  ·
                    refine ⟨1223079254369354899883167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6523089356636559466043557 1223079254369354899883167)
                    ·
                      rfl

theorem cell23_7145815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_7145815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145815 prefixEnd_7145815 := by exact prefixLift 7145815
  have htrace : WordTrace (prefixWord ++ tailWord_7145815) baseStart_7145815 baseEnd_7145815 := by
    simpa [prefixWord, tailWord_7145815, baseEnd_7145815] using wordTrace_append hprefix tailTrace_7145815
  have hstable : (prefixWord ++ tailWord_7145815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145815).length < 2 ^ (prefixWord ++ tailWord_7145815).sum := by decide
  have hdescent : baseEnd_7145815 < baseStart_7145815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145818 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_7145818 : Nat := 118140960795 + 7145818 * 2 ^ 59
def prefixEnd_7145818 : Nat := 4983230072969 + 3 ^ 40 * 7145818 * 2
def baseEnd_7145818 : Nat := 3669239303550028187911987

theorem tailTrace_7145818 : CollatzResearch.WordTrace tailWord_7145818 prefixEnd_7145818 3669239303550028187911987 := by
  unfold tailWord_7145818
  simp only [CollatzResearch.WordTrace]
  refine ⟨65157348506482317349455527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173752929350619512931881405 65157348506482317349455527)
  ·
    refine ⟨97736022759723476024183291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65157348506482317349455527 97736022759723476024183291)
    ·
      refine ⟨146604034139585214036274937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97736022759723476024183291 146604034139585214036274937)
      ·
        refine ⟨109953025604688910527206203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146604034139585214036274937 109953025604688910527206203)
        ·
          refine ⟨164929538407033365790809305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109953025604688910527206203 164929538407033365790809305)
          ·
            refine ⟨123697153805275024343106979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164929538407033365790809305 123697153805275024343106979)
            ·
              refine ⟨185545730707912536514660469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123697153805275024343106979 185545730707912536514660469)
              ·
                refine ⟨17394912253866800298249419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185545730707912536514660469 17394912253866800298249419)
                ·
                  refine ⟨26092368380800200447374129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17394912253866800298249419 26092368380800200447374129)
                  ·
                    refine ⟨19569276285600150335530597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26092368380800200447374129 19569276285600150335530597)
                    ·
                      refine ⟨3669239303550028187911987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19569276285600150335530597 3669239303550028187911987)
                      ·
                        rfl

theorem cell23_7145818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_7145818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145818 prefixEnd_7145818 := by exact prefixLift 7145818
  have htrace : WordTrace (prefixWord ++ tailWord_7145818) baseStart_7145818 baseEnd_7145818 := by
    simpa [prefixWord, tailWord_7145818, baseEnd_7145818] using wordTrace_append hprefix tailTrace_7145818
  have hstable : (prefixWord ++ tailWord_7145818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145818).length < 2 ^ (prefixWord ++ tailWord_7145818).sum := by decide
  have hdescent : baseEnd_7145818 < baseStart_7145818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145882 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2]
def baseStart_7145882 : Nat := 118140960795 + 7145882 * 2 ^ 59
def prefixEnd_7145882 : Nat := 4983230072969 + 3 ^ 40 * 7145882 * 2
def baseEnd_7145882 : Nat := 3669272166311915937511693

theorem tailTrace_7145882 : CollatzResearch.WordTrace tailWord_7145882 prefixEnd_7145882 3669272166311915937511693 := by
  unfold tailWord_7145882
  simp only [CollatzResearch.WordTrace]
  refine ⟨65157932074424352082037975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173754485531798272218767933 65157932074424352082037975)
  ·
    refine ⟨97736898111636528123056963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65157932074424352082037975 97736898111636528123056963)
    ·
      refine ⟨146605347167454792184585445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97736898111636528123056963 146605347167454792184585445)
      ·
        refine ⟨27488502593897773534609771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146605347167454792184585445 27488502593897773534609771)
        ·
          refine ⟨41232753890846660301914657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27488502593897773534609771 41232753890846660301914657)
          ·
            refine ⟨30924565418134995226435993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41232753890846660301914657 30924565418134995226435993)
            ·
              refine ⟨23193424063601246419826995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30924565418134995226435993 23193424063601246419826995)
              ·
                refine ⟨34790136095401869629740493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23193424063601246419826995 34790136095401869629740493)
                ·
                  refine ⟨13046301035775701111152685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34790136095401869629740493 13046301035775701111152685)
                  ·
                    refine ⟨4892362888415887916682257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13046301035775701111152685 4892362888415887916682257)
                    ·
                      refine ⟨3669272166311915937511693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4892362888415887916682257 3669272166311915937511693)
                      ·
                        rfl

theorem cell23_7145882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_7145882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145882 prefixEnd_7145882 := by exact prefixLift 7145882
  have htrace : WordTrace (prefixWord ++ tailWord_7145882) baseStart_7145882 baseEnd_7145882 := by
    simpa [prefixWord, tailWord_7145882, baseEnd_7145882] using wordTrace_append hprefix tailTrace_7145882
  have hstable : (prefixWord ++ tailWord_7145882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145882).length < 2 ^ (prefixWord ++ tailWord_7145882).sum := by decide
  have hdescent : baseEnd_7145882 < baseStart_7145882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7145978 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_7145978 : Nat := 118140960795 + 7145978 * 2 ^ 59
def prefixEnd_7145978 : Nat := 4983230072969 + 3 ^ 40 * 7145978 * 2
def baseEnd_7145978 : Nat := 1223107153484915853970417

theorem tailTrace_7145978 : CollatzResearch.WordTrace tailWord_7145978 prefixEnd_7145978 1223107153484915853970417 := by
  unfold tailWord_7145978
  simp only [CollatzResearch.WordTrace]
  refine ⟨65158807426337404180911647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173756819803566411149097725 65158807426337404180911647)
  ·
    refine ⟨97738211139506106271367471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65158807426337404180911647 97738211139506106271367471)
    ·
      refine ⟨146607316709259159407051207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97738211139506106271367471 146607316709259159407051207)
      ·
        refine ⟨219910975063888739110576811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146607316709259159407051207 219910975063888739110576811)
        ·
          refine ⟨329866462595833108665865217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219910975063888739110576811 329866462595833108665865217)
          ·
            refine ⟨247399846946874831499398913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329866462595833108665865217 247399846946874831499398913)
            ·
              refine ⟨185549885210156123624549185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247399846946874831499398913 185549885210156123624549185)
              ·
                refine ⟨139162413907617092718411889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185549885210156123624549185 139162413907617092718411889)
                ·
                  refine ⟨104371810430712819538808917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139162413907617092718411889 104371810430712819538808917)
                  ·
                    refine ⟨1223107153484915853970417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104371810430712819538808917 1223107153484915853970417)
                    ·
                      rfl

theorem cell23_7145978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_7145978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7145978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7145978 prefixEnd_7145978 := by exact prefixLift 7145978
  have htrace : WordTrace (prefixWord ++ tailWord_7145978) baseStart_7145978 baseEnd_7145978 := by
    simpa [prefixWord, tailWord_7145978, baseEnd_7145978] using wordTrace_append hprefix tailTrace_7145978
  have hstable : (prefixWord ++ tailWord_7145978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7145978).length < 2 ^ (prefixWord ++ tailWord_7145978).sum := by decide
  have hdescent : baseEnd_7145978 < baseStart_7145978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7145978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146046 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_7146046 : Nat := 118140960795 + 7146046 * 2 ^ 59
def prefixEnd_7146046 : Nat := 4983230072969 + 3 ^ 40 * 7146046 * 2
def baseEnd_7146046 : Nat := 1223118792379751098620313

theorem tailTrace_7146046 : CollatzResearch.WordTrace tailWord_7146046 prefixEnd_7146046 1223118792379751098620313 := by
  unfold tailWord_7146046
  simp only [CollatzResearch.WordTrace]
  refine ⟨32579713733637908042140249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173758473246068842891414661 32579713733637908042140249)
  ·
    refine ⟨24434785300228431031605187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32579713733637908042140249 24434785300228431031605187)
    ·
      refine ⟨36652177950342646547407781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24434785300228431031605187 36652177950342646547407781)
      ·
        refine ⟨6872283365689246227638959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36652177950342646547407781 6872283365689246227638959)
        ·
          refine ⟨10308425048533869341458439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6872283365689246227638959 10308425048533869341458439)
          ·
            refine ⟨15462637572800804012187659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10308425048533869341458439 15462637572800804012187659)
            ·
              refine ⟨23193956359201206018281489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15462637572800804012187659 23193956359201206018281489)
              ·
                refine ⟨17395467269400904513711117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23193956359201206018281489 17395467269400904513711117)
                ·
                  refine ⟨6523300226025339192641669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17395467269400904513711117 6523300226025339192641669)
                  ·
                    refine ⟨1223118792379751098620313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6523300226025339192641669 1223118792379751098620313)
                    ·
                      rfl

theorem cell23_7146046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_7146046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146046 prefixEnd_7146046 := by exact prefixLift 7146046
  have htrace : WordTrace (prefixWord ++ tailWord_7146046) baseStart_7146046 baseEnd_7146046 := by
    simpa [prefixWord, tailWord_7146046, baseEnd_7146046] using wordTrace_append hprefix tailTrace_7146046
  have hstable : (prefixWord ++ tailWord_7146046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146046).length < 2 ^ (prefixWord ++ tailWord_7146046).sum := by decide
  have hdescent : baseEnd_7146046 < baseStart_7146046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146076 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 6]
def baseStart_7146076 : Nat := 118140960795 + 7146076 * 2 ^ 59
def prefixEnd_7146076 : Nat := 4983230072969 + 3 ^ 40 * 7146076 * 2
def baseEnd_7146076 : Nat := 407707975728765353165089

theorem tailTrace_7146076 : CollatzResearch.WordTrace tailWord_7146076 prefixEnd_7146076 407707975728765353165089 := by
  unfold tailWord_7146076
  simp only [CollatzResearch.WordTrace]
  refine ⟨130319402029497289730357041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173759202705996386307142721 130319402029497289730357041)
  ·
    refine ⟨97739551522122967297767781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130319402029497289730357041 97739551522122967297767781)
    ·
      refine ⟨18326165910398056368331459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97739551522122967297767781 18326165910398056368331459)
      ·
        refine ⟨27489248865597084552497189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18326165910398056368331459 27489248865597084552497189)
        ·
          refine ⟨5154234162299453353593223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27489248865597084552497189 5154234162299453353593223)
          ·
            refine ⟨7731351243449180030389835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154234162299453353593223 7731351243449180030389835)
            ·
              refine ⟨11597026865173770045584753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731351243449180030389835 11597026865173770045584753)
              ·
                refine ⟨8697770148880327534188565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11597026865173770045584753 8697770148880327534188565)
                ·
                  refine ⟨407707975728765353165089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8697770148880327534188565 407707975728765353165089)
                  ·
                    rfl

theorem cell23_7146076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_7146076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146076 prefixEnd_7146076 := by exact prefixLift 7146076
  have htrace : WordTrace (prefixWord ++ tailWord_7146076) baseStart_7146076 baseEnd_7146076 := by
    simpa [prefixWord, tailWord_7146076, baseEnd_7146076] using wordTrace_append hprefix tailTrace_7146076
  have hstable : (prefixWord ++ tailWord_7146076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146076).length < 2 ^ (prefixWord ++ tailWord_7146076).sum := by decide
  have hdescent : baseEnd_7146076 < baseStart_7146076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146095 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_7146095 : Nat := 118140960795 + 7146095 * 2 ^ 59
def prefixEnd_7146095 : Nat := 4983230072969 + 3 ^ 40 * 7146095 * 2
def baseEnd_7146095 : Nat := 3669381537691323604148213

theorem tailTrace_7146095 : CollatzResearch.WordTrace tailWord_7146095 prefixEnd_7146095 3669381537691323604148213 := by
  unfold tailWord_7146095
  simp only [CollatzResearch.WordTrace]
  refine ⟨260639497045925745705655739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173759664697283830470437159 260639497045925745705655739)
  ·
    refine ⟨390959245568888618558483609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260639497045925745705655739 390959245568888618558483609)
    ·
      refine ⟨293219434176666463918862707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390959245568888618558483609 293219434176666463918862707)
      ·
        refine ⟨439829151264999695878294061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293219434176666463918862707 439829151264999695878294061)
        ·
          refine ⟨164935931724374885954360273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 439829151264999695878294061 164935931724374885954360273)
          ·
            refine ⟨123701948793281164465770205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164935931724374885954360273 123701948793281164465770205)
            ·
              refine ⟨46388230797480436674663827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123701948793281164465770205 46388230797480436674663827)
              ·
                refine ⟨69582346196220655011995741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46388230797480436674663827 69582346196220655011995741)
                ·
                  refine ⟨26093379823582745629498403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69582346196220655011995741 26093379823582745629498403)
                  ·
                    refine ⟨39140069735374118444247605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26093379823582745629498403 39140069735374118444247605)
                    ·
                      refine ⟨3669381537691323604148213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39140069735374118444247605 3669381537691323604148213)
                      ·
                        rfl

theorem cell23_7146095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_7146095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146095 prefixEnd_7146095 := by exact prefixLift 7146095
  have htrace : WordTrace (prefixWord ++ tailWord_7146095) baseStart_7146095 baseEnd_7146095 := by
    simpa [prefixWord, tailWord_7146095, baseEnd_7146095] using wordTrace_append hprefix tailTrace_7146095
  have hstable : (prefixWord ++ tailWord_7146095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146095).length < 2 ^ (prefixWord ++ tailWord_7146095).sum := by decide
  have hdescent : baseEnd_7146095 < baseStart_7146095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146114 : List Nat := [3, 4, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7146114 : Nat := 118140960795 + 7146114 * 2 ^ 59
def prefixEnd_7146114 : Nat := 4983230072969 + 3 ^ 40 * 7146114 * 2
def baseEnd_7146114 : Nat := 1223130431274586343270209

theorem tailTrace_7146114 : CollatzResearch.WordTrace tailWord_7146114 prefixEnd_7146114 1223130431274586343270209 := by
  unfold tailWord_7146114
  simp only [CollatzResearch.WordTrace]
  refine ⟨65160047508214227987649349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173760126688571274633731597 65160047508214227987649349)
  ·
    refine ⟨12217508907790167747684253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65160047508214227987649349 12217508907790167747684253)
    ·
      refine ⟨4581565840421312905381595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12217508907790167747684253 4581565840421312905381595)
      ·
        refine ⟨6872348760631969358072393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581565840421312905381595 6872348760631969358072393)
        ·
          refine ⟨5154261570473977018554295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6872348760631969358072393 5154261570473977018554295)
          ·
            refine ⟨7731392355710965527831443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154261570473977018554295 7731392355710965527831443)
            ·
              refine ⟨11597088533566448291747165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731392355710965527831443 11597088533566448291747165)
              ·
                refine ⟨4348908200087418109405187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11597088533566448291747165 4348908200087418109405187)
                ·
                  refine ⟨6523362300131127164107781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348908200087418109405187 6523362300131127164107781)
                  ·
                    refine ⟨1223130431274586343270209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6523362300131127164107781 1223130431274586343270209)
                    ·
                      rfl

theorem cell23_7146114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7146114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146114 prefixEnd_7146114 := by exact prefixLift 7146114
  have htrace : WordTrace (prefixWord ++ tailWord_7146114) baseStart_7146114 baseEnd_7146114 := by
    simpa [prefixWord, tailWord_7146114, baseEnd_7146114] using wordTrace_append hprefix tailTrace_7146114
  have hstable : (prefixWord ++ tailWord_7146114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146114).length < 2 ^ (prefixWord ++ tailWord_7146114).sum := by decide
  have hdescent : baseEnd_7146114 < baseStart_7146114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146132 : List Nat := [2, 4, 2, 2, 1, 1, 11]
def baseStart_7146132 : Nat := 118140960795 + 7146132 * 2 ^ 59
def prefixEnd_7146132 : Nat := 4983230072969 + 3 ^ 40 * 7146132 * 2
def baseEnd_7146132 : Nat := 45301241191056048881303

theorem tailTrace_7146132 : CollatzResearch.WordTrace tailWord_7146132 prefixEnd_7146132 45301241191056048881303 := by
  unfold tailWord_7146132
  simp only [CollatzResearch.WordTrace]
  refine ⟨130320423273395850512376325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173760564364527800683168433 130320423273395850512376325)
  ·
    refine ⟨24435079363761721971070561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130320423273395850512376325 24435079363761721971070561)
    ·
      refine ⟨18326309522821291478302921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24435079363761721971070561 18326309522821291478302921)
      ·
        refine ⟨13744732142115968608727191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18326309522821291478302921 13744732142115968608727191)
        ·
          refine ⟨20617098213173952913090787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13744732142115968608727191 20617098213173952913090787)
          ·
            refine ⟨30925647319760929369636181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20617098213173952913090787 30925647319760929369636181)
            ·
              refine ⟨45301241191056048881303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30925647319760929369636181 45301241191056048881303)
              ·
                rfl

theorem cell23_7146132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 11].length) (baseStart_7146132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146132 prefixEnd_7146132 := by exact prefixLift 7146132
  have htrace : WordTrace (prefixWord ++ tailWord_7146132) baseStart_7146132 baseEnd_7146132 := by
    simpa [prefixWord, tailWord_7146132, baseEnd_7146132] using wordTrace_append hprefix tailTrace_7146132
  have hstable : (prefixWord ++ tailWord_7146132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146132).length < 2 ^ (prefixWord ++ tailWord_7146132).sum := by decide
  have hdescent : baseEnd_7146132 < baseStart_7146132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146194 : List Nat := [3, 2, 2, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_7146194 : Nat := 118140960795 + 7146194 * 2 ^ 59
def prefixEnd_7146194 : Nat := 4983230072969 + 3 ^ 40 * 7146194 * 2
def baseEnd_7146194 : Nat := 3669432372276118716810259

theorem tailTrace_7146194 : CollatzResearch.WordTrace tailWord_7146194 prefixEnd_7146194 3669432372276118716810259 := by
  unfold tailWord_7146194
  simp only [CollatzResearch.WordTrace]
  refine ⟨65160776968141771403377409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173762071915044723742339757 65160776968141771403377409)
  ·
    refine ⟨48870582726106328552533057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65160776968141771403377409 48870582726106328552533057)
    ·
      refine ⟨36652937044579746414399793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48870582726106328552533057 36652937044579746414399793)
      ·
        refine ⟨27489702783434809810799845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36652937044579746414399793 27489702783434809810799845)
        ·
          refine ⟨5154319271894026839524971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27489702783434809810799845 5154319271894026839524971)
          ·
            refine ⟨7731478907841040259287457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154319271894026839524971 7731478907841040259287457)
            ·
              refine ⟨5798609180880780194465593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731478907841040259287457 5798609180880780194465593)
              ·
                refine ⟨4348956885660585145849195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5798609180880780194465593 4348956885660585145849195)
                ·
                  refine ⟨6523435328490877718773793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348956885660585145849195 6523435328490877718773793)
                  ·
                    refine ⟨4892576496368158289080345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6523435328490877718773793 4892576496368158289080345)
                    ·
                      refine ⟨3669432372276118716810259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4892576496368158289080345 3669432372276118716810259)
                      ·
                        rfl

theorem cell23_7146194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_7146194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146194 prefixEnd_7146194 := by exact prefixLift 7146194
  have htrace : WordTrace (prefixWord ++ tailWord_7146194) baseStart_7146194 baseEnd_7146194 := by
    simpa [prefixWord, tailWord_7146194, baseEnd_7146194] using wordTrace_append hprefix tailTrace_7146194
  have hstable : (prefixWord ++ tailWord_7146194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146194).length < 2 ^ (prefixWord ++ tailWord_7146194).sum := by decide
  have hdescent : baseEnd_7146194 < baseStart_7146194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146202 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_7146202 : Nat := 118140960795 + 7146202 * 2 ^ 59
def prefixEnd_7146202 : Nat := 4983230072969 + 3 ^ 40 * 7146202 * 2
def baseEnd_7146202 : Nat := 3669436480121354685510221

theorem tailTrace_7146202 : CollatzResearch.WordTrace tailWord_7146202 prefixEnd_7146202 3669436480121354685510221 := by
  unfold tailWord_7146202
  simp only [CollatzResearch.WordTrace]
  refine ⟨65160849914134525744950215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173762266437692068653200573 65160849914134525744950215)
  ·
    refine ⟨97741274871201788617425323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65160849914134525744950215 97741274871201788617425323)
    ·
      refine ⟨146611912306802682926137985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97741274871201788617425323 146611912306802682926137985)
      ·
        refine ⟨109958934230102012194603489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146611912306802682926137985 109958934230102012194603489)
        ·
          refine ⟨82469200672576509145952617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109958934230102012194603489 82469200672576509145952617)
          ·
            refine ⟨61851900504432381859464463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82469200672576509145952617 61851900504432381859464463)
            ·
              refine ⟨92777850756648572789196695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61851900504432381859464463 92777850756648572789196695)
              ·
                refine ⟨139166776134972859183795043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92777850756648572789196695 139166776134972859183795043)
                ·
                  refine ⟨208750164202459288775692565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139166776134972859183795043 208750164202459288775692565)
                  ·
                    refine ⟨9785163946990279161360589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208750164202459288775692565 9785163946990279161360589)
                    ·
                      refine ⟨3669436480121354685510221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785163946990279161360589 3669436480121354685510221)
                      ·
                        rfl

theorem cell23_7146202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_7146202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146202 prefixEnd_7146202 := by exact prefixLift 7146202
  have htrace : WordTrace (prefixWord ++ tailWord_7146202) baseStart_7146202 baseEnd_7146202 := by
    simpa [prefixWord, tailWord_7146202, baseEnd_7146202] using wordTrace_append hprefix tailTrace_7146202
  have hstable : (prefixWord ++ tailWord_7146202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146202).length < 2 ^ (prefixWord ++ tailWord_7146202).sum := by decide
  have hdescent : baseEnd_7146202 < baseStart_7146202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146212 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_7146212 : Nat := 118140960795 + 7146212 * 2 ^ 59
def prefixEnd_7146212 : Nat := 4983230072969 + 3 ^ 40 * 7146212 * 2
def baseEnd_7146212 : Nat := 3669441614927899646385175

theorem tailTrace_7146212 : CollatzResearch.WordTrace tailWord_7146212 prefixEnd_7146212 3669441614927899646385175 := by
  unfold tailWord_7146212
  simp only [CollatzResearch.WordTrace]
  refine ⟨130321882193250937343832445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173762509591001249791776593 130321882193250937343832445)
  ·
    refine ⟨48870705822469101503937167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130321882193250937343832445 48870705822469101503937167)
    ·
      refine ⟨73306058733703652255905751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48870705822469101503937167 73306058733703652255905751)
      ·
        refine ⟨109959088100555478383858627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73306058733703652255905751 109959088100555478383858627)
        ·
          refine ⟨164938632150833217575787941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109959088100555478383858627 164938632150833217575787941)
          ·
            refine ⟨30925993528281228295460239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164938632150833217575787941 30925993528281228295460239)
            ·
              refine ⟨46388990292421842443190359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30925993528281228295460239 46388990292421842443190359)
              ·
                refine ⟨69583485438632763664785539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46388990292421842443190359 69583485438632763664785539)
                ·
                  refine ⟨104375228157949145497178309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69583485438632763664785539 104375228157949145497178309)
                  ·
                    refine ⟨19570355279615464780720933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104375228157949145497178309 19570355279615464780720933)
                    ·
                      refine ⟨3669441614927899646385175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19570355279615464780720933 3669441614927899646385175)
                      ·
                        rfl

theorem cell23_7146212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_7146212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146212 prefixEnd_7146212 := by exact prefixLift 7146212
  have htrace : WordTrace (prefixWord ++ tailWord_7146212) baseStart_7146212 baseEnd_7146212 := by
    simpa [prefixWord, tailWord_7146212, baseEnd_7146212] using wordTrace_append hprefix tailTrace_7146212
  have hstable : (prefixWord ++ tailWord_7146212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146212).length < 2 ^ (prefixWord ++ tailWord_7146212).sum := by decide
  have hdescent : baseEnd_7146212 < baseStart_7146212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146222 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_7146222 : Nat := 118140960795 + 7146222 * 2 ^ 59
def prefixEnd_7146222 : Nat := 4983230072969 + 3 ^ 40 * 7146222 * 2
def baseEnd_7146222 : Nat := 407716305526049400806681

theorem tailTrace_7146222 : CollatzResearch.WordTrace tailWord_7146222 prefixEnd_7146222 407716305526049400806681 := by
  unfold tailWord_7146222
  simp only [CollatzResearch.WordTrace]
  refine ⟨32580516139558205799441115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173762752744310430930352613 32580516139558205799441115)
  ·
    refine ⟨48870774209337308699161673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32580516139558205799441115 48870774209337308699161673)
    ·
      refine ⟨36653080657002981524371255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48870774209337308699161673 36653080657002981524371255)
      ·
        refine ⟨54979620985504472286556883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36653080657002981524371255 54979620985504472286556883)
        ·
          refine ⟨82469431478256708429835325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54979620985504472286556883 82469431478256708429835325)
          ·
            refine ⟨30926036804346265661188247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82469431478256708429835325 30926036804346265661188247)
            ·
              refine ⟨46389055206519398491782371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30926036804346265661188247 46389055206519398491782371)
              ·
                refine ⟨69583582809779097737673557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46389055206519398491782371 69583582809779097737673557)
                ·
                  refine ⟨407716305526049400806681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69583582809779097737673557 407716305526049400806681)
                  ·
                    rfl

theorem cell23_7146222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_7146222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146222 prefixEnd_7146222 := by exact prefixLift 7146222
  have htrace : WordTrace (prefixWord ++ tailWord_7146222) baseStart_7146222 baseEnd_7146222 := by
    simpa [prefixWord, tailWord_7146222, baseEnd_7146222] using wordTrace_append hprefix tailTrace_7146222
  have hstable : (prefixWord ++ tailWord_7146222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146222).length < 2 ^ (prefixWord ++ tailWord_7146222).sum := by decide
  have hdescent : baseEnd_7146222 < baseStart_7146222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146232 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_7146232 : Nat := 118140960795 + 7146232 * 2 ^ 59
def prefixEnd_7146232 : Nat := 4983230072969 + 3 ^ 40 * 7146232 * 2
def baseEnd_7146232 : Nat := 3669451884540989568135083

theorem tailTrace_7146232 : CollatzResearch.WordTrace tailWord_7146232 prefixEnd_7146232 3669451884540989568135083 := by
  unfold tailWord_7146232
  simp only [CollatzResearch.WordTrace]
  refine ⟨130322246923214709051696475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173762995897619612068928633 130322246923214709051696475)
  ·
    refine ⟨195483370384822063577544713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130322246923214709051696475 195483370384822063577544713)
    ·
      refine ⟨146612527788616547683158535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195483370384822063577544713 146612527788616547683158535)
      ·
        refine ⟨219918791682924821524737803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146612527788616547683158535 219918791682924821524737803)
        ·
          refine ⟨329878187524387232287106705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219918791682924821524737803 329878187524387232287106705)
          ·
            refine ⟨247408640643290424215330029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329878187524387232287106705 247408640643290424215330029)
            ·
              refine ⟨92778240241233909080748761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247408640643290424215330029 92778240241233909080748761)
              ·
                refine ⟨69583680180925431810561571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92778240241233909080748761 69583680180925431810561571)
                ·
                  refine ⟨104375520271388147715842357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69583680180925431810561571 104375520271388147715842357)
                  ·
                    refine ⟨9785205025442638848360221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104375520271388147715842357 9785205025442638848360221)
                    ·
                      refine ⟨3669451884540989568135083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785205025442638848360221 3669451884540989568135083)
                      ·
                        rfl

theorem cell23_7146232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_7146232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146232 prefixEnd_7146232 := by exact prefixLift 7146232
  have htrace : WordTrace (prefixWord ++ tailWord_7146232) baseStart_7146232 baseEnd_7146232 := by
    simpa [prefixWord, tailWord_7146232, baseEnd_7146232] using wordTrace_append hprefix tailTrace_7146232
  have hstable : (prefixWord ++ tailWord_7146232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146232).length < 2 ^ (prefixWord ++ tailWord_7146232).sum := by decide
  have hdescent : baseEnd_7146232 < baseStart_7146232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146252 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_7146252 : Nat := 118140960795 + 7146252 * 2 ^ 59
def prefixEnd_7146252 : Nat := 4983230072969 + 3 ^ 40 * 7146252 * 2
def baseEnd_7146252 : Nat := 1223154051384693163294997

theorem tailTrace_7146252 : CollatzResearch.WordTrace tailWord_7146252 prefixEnd_7146252 1223154051384693163294997 := by
  unfold tailWord_7146252
  simp only [CollatzResearch.WordTrace]
  refine ⟨130322611653178480759560505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173763482204237974346080673 130322611653178480759560505)
  ·
    refine ⟨97741958739883860569670379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130322611653178480759560505 97741958739883860569670379)
    ·
      refine ⟨146612938109825790854505569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97741958739883860569670379 146612938109825790854505569)
      ·
        refine ⟨109959703582369343140879177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146612938109825790854505569 109959703582369343140879177)
        ·
          refine ⟨82469777686777007355659383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109959703582369343140879177 82469777686777007355659383)
          ·
            refine ⟨123704666530165511033489075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82469777686777007355659383 123704666530165511033489075)
            ·
              refine ⟨185556999795248266550233613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123704666530165511033489075 185556999795248266550233613)
              ·
                refine ⟨69583874923218099956337605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185556999795248266550233613 69583874923218099956337605)
                ·
                  refine ⟨13046976548103393741813301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69583874923218099956337605 13046976548103393741813301)
                  ·
                    refine ⟨1223154051384693163294997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13046976548103393741813301 1223154051384693163294997)
                    ·
                      rfl

theorem cell23_7146252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_7146252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146252 prefixEnd_7146252 := by exact prefixLift 7146252
  have htrace : WordTrace (prefixWord ++ tailWord_7146252) baseStart_7146252 baseEnd_7146252 := by
    simpa [prefixWord, tailWord_7146252, baseEnd_7146252] using wordTrace_append hprefix tailTrace_7146252
  have hstable : (prefixWord ++ tailWord_7146252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146252).length < 2 ^ (prefixWord ++ tailWord_7146252).sum := by decide
  have hdescent : baseEnd_7146252 < baseStart_7146252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146289 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_7146289 : Nat := 118140960795 + 7146289 * 2 ^ 59
def prefixEnd_7146289 : Nat := 4983230072969 + 3 ^ 40 * 7146289 * 2
def baseEnd_7146289 : Nat := 3669481152938295845122321

theorem tailTrace_7146289 : CollatzResearch.WordTrace tailWord_7146289 prefixEnd_7146289 3669481152938295845122321 := by
  unfold tailWord_7146289
  simp only [CollatzResearch.WordTrace]
  refine ⟨260646572807222916838217921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173764381871481944558811947 260646572807222916838217921)
  ·
    refine ⟨195484929605417187628663441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260646572807222916838217921 195484929605417187628663441)
    ·
      refine ⟨146613697204062890721497581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195484929605417187628663441 146613697204062890721497581)
      ·
        refine ⟨54980136451523584020561593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146613697204062890721497581 54980136451523584020561593)
        ·
          refine ⟨41235102338642688015421195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54980136451523584020561593 41235102338642688015421195)
          ·
            refine ⟨61852653507964032023131793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41235102338642688015421195 61852653507964032023131793)
            ·
              refine ⟨46389490130973024017348845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61852653507964032023131793 46389490130973024017348845)
              ·
                refine ⟨17396058799114884006505817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46389490130973024017348845 17396058799114884006505817)
                ·
                  refine ⟨13047044099336163004879363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17396058799114884006505817 13047044099336163004879363)
                  ·
                    refine ⟨19570566149004244507319045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13047044099336163004879363 19570566149004244507319045)
                    ·
                      refine ⟨3669481152938295845122321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19570566149004244507319045 3669481152938295845122321)
                      ·
                        rfl

theorem cell23_7146289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_7146289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146289 prefixEnd_7146289 := by exact prefixLift 7146289
  have htrace : WordTrace (prefixWord ++ tailWord_7146289) baseStart_7146289 baseEnd_7146289 := by
    simpa [prefixWord, tailWord_7146289, baseEnd_7146289] using wordTrace_append hprefix tailTrace_7146289
  have hstable : (prefixWord ++ tailWord_7146289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146289).length < 2 ^ (prefixWord ++ tailWord_7146289).sum := by decide
  have hdescent : baseEnd_7146289 < baseStart_7146289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146312 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 8]
def baseStart_7146312 : Nat := 118140960795 + 7146312 * 2 ^ 59
def prefixEnd_7146312 : Nat := 4983230072969 + 3 ^ 40 * 7146312 * 2
def baseEnd_7146312 : Nat := 407721440332594361681635

theorem tailTrace_7146312 : CollatzResearch.WordTrace tailWord_7146312 prefixEnd_7146312 407721440332594361681635 := by
  unfold tailWord_7146312
  simp only [CollatzResearch.WordTrace]
  refine ⟨130323705843069795883152595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173764941124093061177536793 130323705843069795883152595)
  ·
    refine ⟨195485558764604693824728893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130323705843069795883152595 195485558764604693824728893)
    ·
      refine ⟨73307084536726760184273335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195485558764604693824728893 73307084536726760184273335)
      ·
        refine ⟨109960626805090140276410003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73307084536726760184273335 109960626805090140276410003)
        ·
          refine ⟨164940940207635210414615005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109960626805090140276410003 164940940207635210414615005)
          ·
            refine ⟨61852852577863203905480627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164940940207635210414615005 61852852577863203905480627)
            ·
              refine ⟨92779278866794805858220941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61852852577863203905480627 92779278866794805858220941)
              ·
                refine ⟨34792229575048052196832853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92779278866794805858220941 34792229575048052196832853)
                ·
                  refine ⟨407721440332594361681635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34792229575048052196832853 407721440332594361681635)
                  ·
                    rfl

theorem cell23_7146312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 8].length) (baseStart_7146312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146312 prefixEnd_7146312 := by exact prefixLift 7146312
  have htrace : WordTrace (prefixWord ++ tailWord_7146312) baseStart_7146312 baseEnd_7146312 := by
    simpa [prefixWord, tailWord_7146312, baseEnd_7146312] using wordTrace_append hprefix tailTrace_7146312
  have hstable : (prefixWord ++ tailWord_7146312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146312).length < 2 ^ (prefixWord ++ tailWord_7146312).sum := by decide
  have hdescent : baseEnd_7146312 < baseStart_7146312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146316 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_7146316 : Nat := 118140960795 + 7146316 * 2 ^ 59
def prefixEnd_7146316 : Nat := 4983230072969 + 3 ^ 40 * 7146316 * 2
def baseEnd_7146316 : Nat := 1223165005638655746494899

theorem tailTrace_7146316 : CollatzResearch.WordTrace tailWord_7146316 prefixEnd_7146316 1223165005638655746494899 := by
  unfold tailWord_7146316
  simp only [CollatzResearch.WordTrace]
  refine ⟨130323778789062550224725401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173765038385416733632967201 130323778789062550224725401)
  ·
    refine ⟨97742834091796912668544051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130323778789062550224725401 97742834091796912668544051)
    ·
      refine ⟨146614251137695369002816077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97742834091796912668544051 146614251137695369002816077)
      ·
        refine ⟨54980344176635763376056029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146614251137695369002816077 54980344176635763376056029)
        ·
          refine ⟨20617629066238411266021011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54980344176635763376056029 20617629066238411266021011)
          ·
            refine ⟨30926443599357616899031517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20617629066238411266021011 30926443599357616899031517)
            ·
              refine ⟨11597416349759106337136819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30926443599357616899031517 11597416349759106337136819)
              ·
                refine ⟨17396124524638659505705229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11597416349759106337136819 17396124524638659505705229)
                ·
                  refine ⟨6523546696739497314639461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17396124524638659505705229 6523546696739497314639461)
                  ·
                    refine ⟨1223165005638655746494899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6523546696739497314639461 1223165005638655746494899)
                    ·
                      rfl

theorem cell23_7146316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_7146316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146316 prefixEnd_7146316 := by exact prefixLift 7146316
  have htrace : WordTrace (prefixWord ++ tailWord_7146316) baseStart_7146316 baseEnd_7146316 := by
    simpa [prefixWord, tailWord_7146316, baseEnd_7146316] using wordTrace_append hprefix tailTrace_7146316
  have hstable : (prefixWord ++ tailWord_7146316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146316).length < 2 ^ (prefixWord ++ tailWord_7146316).sum := by decide
  have hdescent : baseEnd_7146316 < baseStart_7146316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146329 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 6]
def baseStart_7146329 : Nat := 118140960795 + 7146329 * 2 ^ 59
def prefixEnd_7146329 : Nat := 4983230072969 + 3 ^ 40 * 7146329 * 2
def baseEnd_7146329 : Nat := 407722410240497298735793

theorem tailTrace_7146329 : CollatzResearch.WordTrace tailWord_7146329 prefixEnd_7146329 407722410240497298735793 := by
  unfold tailWord_7146329
  simp only [CollatzResearch.WordTrace]
  refine ⟨260648031727078003669674041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173765354484718669113116027 260648031727078003669674041)
  ·
    refine ⟨195486023795308502752255531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260648031727078003669674041 195486023795308502752255531)
    ·
      refine ⟨293229035692962754128383297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195486023795308502752255531 293229035692962754128383297)
      ·
        refine ⟨219921776769722065596287473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293229035692962754128383297 219921776769722065596287473)
        ·
          refine ⟨164941332577291549197215605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219921776769722065596287473 164941332577291549197215605)
          ·
            refine ⟨15463249929121082737238963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164941332577291549197215605 15463249929121082737238963)
            ·
              refine ⟨23194874893681624105858445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15463249929121082737238963 23194874893681624105858445)
              ·
                refine ⟨8698078085130609039696917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23194874893681624105858445 8698078085130609039696917)
                ·
                  refine ⟨407722410240497298735793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8698078085130609039696917 407722410240497298735793)
                  ·
                    rfl

theorem cell23_7146329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 6].length) (baseStart_7146329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146329 prefixEnd_7146329 := by exact prefixLift 7146329
  have htrace : WordTrace (prefixWord ++ tailWord_7146329) baseStart_7146329 baseEnd_7146329 := by
    simpa [prefixWord, tailWord_7146329, baseEnd_7146329] using wordTrace_append hprefix tailTrace_7146329
  have hstable : (prefixWord ++ tailWord_7146329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146329).length < 2 ^ (prefixWord ++ tailWord_7146329).sum := by decide
  have hdescent : baseEnd_7146329 < baseStart_7146329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146359 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 1, 5]
def baseStart_7146359 : Nat := 118140960795 + 7146359 * 2 ^ 59
def prefixEnd_7146359 : Nat := 4983230072969 + 3 ^ 40 * 7146359 * 2
def baseEnd_7146359 : Nat := 1223172365528036857082333

theorem tailTrace_7146359 : CollatzResearch.WordTrace tailWord_7146359 prefixEnd_7146359 1223172365528036857082333 := by
  unfold tailWord_7146359
  simp only [CollatzResearch.WordTrace]
  refine ⟨260649125916969318793266131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173766083944646212528844087 260649125916969318793266131)
  ·
    refine ⟨390973688875453978189899197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260649125916969318793266131 390973688875453978189899197)
    ·
      refine ⟨146615133328295241821212199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390973688875453978189899197 146615133328295241821212199)
      ·
        refine ⟨219922699992442862731818299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146615133328295241821212199 219922699992442862731818299)
        ·
          refine ⟨329884049988664294097727449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219922699992442862731818299 329884049988664294097727449)
          ·
            refine ⟨247413037491498220573295587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329884049988664294097727449 247413037491498220573295587)
            ·
              refine ⟨371119556237247330859943381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247413037491498220573295587 371119556237247330859943381)
              ·
                refine ⟨8698114599310484317029923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 371119556237247330859943381 8698114599310484317029923)
                ·
                  refine ⟨13047171898965726475544885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698114599310484317029923 13047171898965726475544885)
                  ·
                    refine ⟨1223172365528036857082333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13047171898965726475544885 1223172365528036857082333)
                    ·
                      rfl

theorem cell23_7146359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_7146359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146359 prefixEnd_7146359 := by exact prefixLift 7146359
  have htrace : WordTrace (prefixWord ++ tailWord_7146359) baseStart_7146359 baseEnd_7146359 := by
    simpa [prefixWord, tailWord_7146359, baseEnd_7146359] using wordTrace_append hprefix tailTrace_7146359
  have hstable : (prefixWord ++ tailWord_7146359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146359).length < 2 ^ (prefixWord ++ tailWord_7146359).sum := by decide
  have hdescent : baseEnd_7146359 < baseStart_7146359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146379 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 4]
def baseStart_7146379 : Nat := 118140960795 + 7146379 * 2 ^ 59
def prefixEnd_7146379 : Nat := 4983230072969 + 3 ^ 40 * 7146379 * 2
def baseEnd_7146379 : Nat := 3669527366197200492996907

theorem tailTrace_7146379 : CollatzResearch.WordTrace tailWord_7146379 prefixEnd_7146379 3669527366197200492996907 := by
  unfold tailWord_7146379
  simp only [CollatzResearch.WordTrace]
  refine ⟨260649855376896862208994191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173766570251264574805996127 260649855376896862208994191)
  ·
    refine ⟨390974783065345293313491287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260649855376896862208994191 390974783065345293313491287)
    ·
      refine ⟨586462174598017939970236931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390974783065345293313491287 586462174598017939970236931)
      ·
        refine ⟨879693261897026909955355397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586462174598017939970236931 879693261897026909955355397)
        ·
          refine ⟨164942486605692545616629137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 879693261897026909955355397 164942486605692545616629137)
          ·
            refine ⟨123706864954269409212471853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164942486605692545616629137 123706864954269409212471853)
            ·
              refine ⟨46390074357851028454676945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123706864954269409212471853 46390074357851028454676945)
              ·
                refine ⟨34792555768388271341007709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46390074357851028454676945 34792555768388271341007709)
                ·
                  refine ⟨13047208413145601752877891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34792555768388271341007709 13047208413145601752877891)
                  ·
                    refine ⟨19570812619718402629316837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13047208413145601752877891 19570812619718402629316837)
                    ·
                      refine ⟨3669527366197200492996907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19570812619718402629316837 3669527366197200492996907)
                      ·
                        rfl

theorem cell23_7146379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 4].length) (baseStart_7146379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146379 prefixEnd_7146379 := by exact prefixLift 7146379
  have htrace : WordTrace (prefixWord ++ tailWord_7146379) baseStart_7146379 baseEnd_7146379 := by
    simpa [prefixWord, tailWord_7146379, baseEnd_7146379] using wordTrace_append hprefix tailTrace_7146379
  have hstable : (prefixWord ++ tailWord_7146379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146379).length < 2 ^ (prefixWord ++ tailWord_7146379).sum := by decide
  have hdescent : baseEnd_7146379 < baseStart_7146379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146389 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_7146389 : Nat := 118140960795 + 7146389 * 2 ^ 59
def prefixEnd_7146389 : Nat := 4983230072969 + 3 ^ 40 * 7146389 * 2
def baseEnd_7146389 : Nat := 1223177500334581817957287

theorem tailTrace_7146389 : CollatzResearch.WordTrace tailWord_7146389 prefixEnd_7146389 1223177500334581817957287 := by
  unfold tailWord_7146389
  simp only [CollatzResearch.WordTrace]
  refine ⟨260650220106860633916858221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173766813404573755944572147 260650220106860633916858221)
  ·
    refine ⟨97743832540072737718821833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260650220106860633916858221 97743832540072737718821833)
    ·
      refine ⟨73307874405054553289116375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97743832540072737718821833 73307874405054553289116375)
      ·
        refine ⟨109961811607581829933674563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73307874405054553289116375 109961811607581829933674563)
        ·
          refine ⟨164942717411372744900511845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109961811607581829933674563 164942717411372744900511845)
          ·
            refine ⟨30926759514632389668845971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164942717411372744900511845 30926759514632389668845971)
            ·
              refine ⟨46390139271948584503268957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30926759514632389668845971 46390139271948584503268957)
              ·
                refine ⟨17396302226980719188725859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46390139271948584503268957 17396302226980719188725859)
                ·
                  refine ⟨26094453340471078783088789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17396302226980719188725859 26094453340471078783088789)
                  ·
                    refine ⟨1223177500334581817957287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26094453340471078783088789 1223177500334581817957287)
                    ·
                      rfl

theorem cell23_7146389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_7146389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146389 prefixEnd_7146389 := by exact prefixLift 7146389
  have htrace : WordTrace (prefixWord ++ tailWord_7146389) baseStart_7146389 baseEnd_7146389 := by
    simpa [prefixWord, tailWord_7146389, baseEnd_7146389] using wordTrace_append hprefix tailTrace_7146389
  have hstable : (prefixWord ++ tailWord_7146389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146389).length < 2 ^ (prefixWord ++ tailWord_7146389).sum := by decide
  have hdescent : baseEnd_7146389 < baseStart_7146389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146407 : List Nat := [1, 1, 6, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_7146407 : Nat := 118140960795 + 7146407 * 2 ^ 59
def prefixEnd_7146407 : Nat := 4983230072969 + 3 ^ 40 * 7146407 * 2
def baseEnd_7146407 : Nat := 3669541743655526383446779

theorem tailTrace_7146407 : CollatzResearch.WordTrace tailWord_7146407 prefixEnd_7146407 3669541743655526383446779 := by
  unfold tailWord_7146407
  simp only [CollatzResearch.WordTrace]
  refine ⟨260650876620795422991013475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173767251080530281994008983 260650876620795422991013475)
  ·
    refine ⟨390976314931193134486520213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260650876620795422991013475 390976314931193134486520213)
    ·
      refine ⟨18327014762399678179055635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 390976314931193134486520213 18327014762399678179055635)
      ·
        refine ⟨27490522143599517268583453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18327014762399678179055635 27490522143599517268583453)
        ·
          refine ⟨10308945803849818975718795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27490522143599517268583453 10308945803849818975718795)
          ·
            refine ⟨15463418705774728463578193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10308945803849818975718795 15463418705774728463578193)
            ·
              refine ⟨11597564029331046347683645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15463418705774728463578193 11597564029331046347683645)
              ·
                refine ⟨4349086510999142380381367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11597564029331046347683645 4349086510999142380381367)
                ·
                  refine ⟨6523629766498713570572051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349086510999142380381367 6523629766498713570572051)
                  ·
                    refine ⟨9785444649748070355858077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6523629766498713570572051 9785444649748070355858077)
                    ·
                      refine ⟨3669541743655526383446779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785444649748070355858077 3669541743655526383446779)
                      ·
                        rfl

theorem cell23_7146407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_7146407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146407 prefixEnd_7146407 := by exact prefixLift 7146407
  have htrace : WordTrace (prefixWord ++ tailWord_7146407) baseStart_7146407 baseEnd_7146407 := by
    simpa [prefixWord, tailWord_7146407, baseEnd_7146407] using wordTrace_append hprefix tailTrace_7146407
  have hstable : (prefixWord ++ tailWord_7146407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146407).length < 2 ^ (prefixWord ++ tailWord_7146407).sum := by decide
  have hdescent : baseEnd_7146407 < baseStart_7146407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146409 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_7146409 : Nat := 118140960795 + 7146409 * 2 ^ 59
def prefixEnd_7146409 : Nat := 4983230072969 + 3 ^ 40 * 7146409 * 2
def baseEnd_7146409 : Nat := 3669542770616835375621769

theorem tailTrace_7146409 : CollatzResearch.WordTrace tailWord_7146409 prefixEnd_7146409 3669542770616835375621769 := by
  unfold tailWord_7146409
  simp only [CollatzResearch.WordTrace]
  refine ⟨260650949566788177332586281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173767299711192118221724187 260650949566788177332586281)
  ·
    refine ⟨195488212175091132999439711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260650949566788177332586281 195488212175091132999439711)
    ·
      refine ⟨293232318262636699499159567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195488212175091132999439711 293232318262636699499159567)
      ·
        refine ⟨439848477393955049248739351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293232318262636699499159567 439848477393955049248739351)
        ·
          refine ⟨659772716090932573873109027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439848477393955049248739351 659772716090932573873109027)
          ·
            refine ⟨989659074136398860809663541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659772716090932573873109027 989659074136398860809663541)
            ·
              refine ⟨92780538200287393200905957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 989659074136398860809663541 92780538200287393200905957)
              ·
                refine ⟨17396350912553886225169867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92780538200287393200905957 17396350912553886225169867)
                ·
                  refine ⟨26094526368830829337754801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17396350912553886225169867 26094526368830829337754801)
                  ·
                    refine ⟨19570894776623122003316101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26094526368830829337754801 19570894776623122003316101)
                    ·
                      refine ⟨3669542770616835375621769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19570894776623122003316101 3669542770616835375621769)
                      ·
                        rfl

theorem cell23_7146409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_7146409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146409 prefixEnd_7146409 := by exact prefixLift 7146409
  have htrace : WordTrace (prefixWord ++ tailWord_7146409) baseStart_7146409 baseEnd_7146409 := by
    simpa [prefixWord, tailWord_7146409, baseEnd_7146409] using wordTrace_append hprefix tailTrace_7146409
  have hstable : (prefixWord ++ tailWord_7146409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146409).length < 2 ^ (prefixWord ++ tailWord_7146409).sum := by decide
  have hdescent : baseEnd_7146409 < baseStart_7146409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146430 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_7146430 : Nat := 118140960795 + 7146430 * 2 ^ 59
def prefixEnd_7146430 : Nat := 4983230072969 + 3 ^ 40 * 7146430 * 2
def baseEnd_7146430 : Nat := 3669553553710579793459173

theorem tailTrace_7146430 : CollatzResearch.WordTrace tailWord_7146430 prefixEnd_7146430 3669553553710579793459173 := by
  unfold tailWord_7146430
  simp only [CollatzResearch.WordTrace]
  refine ⟨32581464437464012239887593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173767810333141398612733829 32581464437464012239887593)
  ·
    refine ⟨24436098328098009179915695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32581464437464012239887593 24436098328098009179915695)
    ·
      refine ⟨36654147492147013769873543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24436098328098009179915695 36654147492147013769873543)
      ·
        refine ⟨54981221238220520654810315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36654147492147013769873543 54981221238220520654810315)
        ·
          refine ⟨82471831857330780982215473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54981221238220520654810315 82471831857330780982215473)
          ·
            refine ⟨61853873892998085736661605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82471831857330780982215473 61853873892998085736661605)
            ·
              refine ⟨11597601354937141075624051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61853873892998085736661605 11597601354937141075624051)
              ·
                refine ⟨17396402032405711613436077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11597601354937141075624051 17396402032405711613436077)
                ·
                  refine ⟨6523650762152141855038529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17396402032405711613436077 6523650762152141855038529)
                  ·
                    refine ⟨4892738071614106391278897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6523650762152141855038529 4892738071614106391278897)
                    ·
                      refine ⟨3669553553710579793459173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4892738071614106391278897 3669553553710579793459173)
                      ·
                        rfl

theorem cell23_7146430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_7146430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146430 prefixEnd_7146430 := by exact prefixLift 7146430
  have htrace : WordTrace (prefixWord ++ tailWord_7146430) baseStart_7146430 baseEnd_7146430 := by
    simpa [prefixWord, tailWord_7146430, baseEnd_7146430] using wordTrace_append hprefix tailTrace_7146430
  have hstable : (prefixWord ++ tailWord_7146430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146430).length < 2 ^ (prefixWord ++ tailWord_7146430).sum := by decide
  have hdescent : baseEnd_7146430 < baseStart_7146430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146440 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 2, 4]
def baseStart_7146440 : Nat := 118140960795 + 7146440 * 2 ^ 59
def prefixEnd_7146440 : Nat := 4983230072969 + 3 ^ 40 * 7146440 * 2
def baseEnd_7146440 : Nat := 1223186229505708251444709

theorem tailTrace_7146440 : CollatzResearch.WordTrace tailWord_7146440 prefixEnd_7146440 1223186229505708251444709 := by
  unfold tailWord_7146440
  simp only [CollatzResearch.WordTrace]
  refine ⟨130326040114837934813482387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173768053486450579751309849 130326040114837934813482387)
  ·
    refine ⟨195489060172256902220223581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130326040114837934813482387 195489060172256902220223581)
    ·
      refine ⟨73308397564596338332583843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195489060172256902220223581 73308397564596338332583843)
      ·
        refine ⟨109962596346894507498875765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73308397564596338332583843 109962596346894507498875765)
        ·
          refine ⟨10308993407521360078019603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109962596346894507498875765 10308993407521360078019603)
          ·
            refine ⟨15463490111282040117029405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10308993407521360078019603 15463490111282040117029405)
            ·
              refine ⟨5798808791730765043886027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15463490111282040117029405 5798808791730765043886027)
              ·
                refine ⟨8698213187596147565829041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798808791730765043886027 8698213187596147565829041)
                ·
                  refine ⟨6523659890697110674371781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8698213187596147565829041 6523659890697110674371781)
                  ·
                    refine ⟨1223186229505708251444709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6523659890697110674371781 1223186229505708251444709)
                    ·
                      rfl

theorem cell23_7146440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_7146440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146440 prefixEnd_7146440 := by exact prefixLift 7146440
  have htrace : WordTrace (prefixWord ++ tailWord_7146440) baseStart_7146440 baseEnd_7146440 := by
    simpa [prefixWord, tailWord_7146440, baseEnd_7146440] using wordTrace_append hprefix tailTrace_7146440
  have hstable : (prefixWord ++ tailWord_7146440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146440).length < 2 ^ (prefixWord ++ tailWord_7146440).sum := by decide
  have hdescent : baseEnd_7146440 < baseStart_7146440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146450 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_7146450 : Nat := 118140960795 + 7146450 * 2 ^ 59
def prefixEnd_7146450 : Nat := 4983230072969 + 3 ^ 40 * 7146450 * 2
def baseEnd_7146450 : Nat := 3669563823323669715209081

theorem tailTrace_7146450 : CollatzResearch.WordTrace tailWord_7146450 prefixEnd_7146450 3669563823323669715209081 := by
  unfold tailWord_7146450
  simp only [CollatzResearch.WordTrace]
  refine ⟨65163111239909910333707201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173768296639759760889885869 65163111239909910333707201)
  ·
    refine ⟨48872333429932432750280401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65163111239909910333707201 48872333429932432750280401)
    ·
      refine ⟨36654250072449324562710301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48872333429932432750280401 36654250072449324562710301)
      ·
        refine ⟨13745343777168496711016363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36654250072449324562710301 13745343777168496711016363)
        ·
          refine ⟨20618015665752745066524545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13745343777168496711016363 20618015665752745066524545)
          ·
            refine ⟨15463511749314558799893409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20618015665752745066524545 15463511749314558799893409)
            ·
              refine ⟨11597633811985919099920057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15463511749314558799893409 11597633811985919099920057)
              ·
                refine ⟨8698225358989439324940043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11597633811985919099920057 8698225358989439324940043)
                ·
                  refine ⟨13047338038484158987410065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698225358989439324940043 13047338038484158987410065)
                  ·
                    refine ⟨9785503528863119240557549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13047338038484158987410065 9785503528863119240557549)
                    ·
                      refine ⟨3669563823323669715209081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785503528863119240557549 3669563823323669715209081)
                      ·
                        rfl

theorem cell23_7146450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_7146450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146450 prefixEnd_7146450 := by exact prefixLift 7146450
  have htrace : WordTrace (prefixWord ++ tailWord_7146450) baseStart_7146450 baseEnd_7146450 := by
    simpa [prefixWord, tailWord_7146450, baseEnd_7146450] using wordTrace_append hprefix tailTrace_7146450
  have hstable : (prefixWord ++ tailWord_7146450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146450).length < 2 ^ (prefixWord ++ tailWord_7146450).sum := by decide
  have hdescent : baseEnd_7146450 < baseStart_7146450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146453 : List Nat := [1, 3, 2, 3, 3, 2, 2, 7]
def baseStart_7146453 : Nat := 118140960795 + 7146453 * 2 ^ 59
def prefixEnd_7146453 : Nat := 4983230072969 + 3 ^ 40 * 7146453 * 2
def baseEnd_7146453 : Nat := 135909828287616044573021

theorem tailTrace_7146453 : CollatzResearch.WordTrace tailWord_7146453 prefixEnd_7146453 135909828287616044573021 := by
  unfold tailWord_7146453
  simp only [CollatzResearch.WordTrace]
  refine ⟨260652554378628772847188013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173768369585752515231458675 260652554378628772847188013)
  ·
    refine ⟨97744707891985789817695505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260652554378628772847188013 97744707891985789817695505)
    ·
      refine ⟨73308530918989342363271629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97744707891985789817695505 73308530918989342363271629)
      ·
        refine ⟨27490699094621003386226861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73308530918989342363271629 27490699094621003386226861)
        ·
          refine ⟨10309012160482876269835073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27490699094621003386226861 10309012160482876269835073)
          ·
            refine ⟨7731759120362157202376305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10309012160482876269835073 7731759120362157202376305)
            ·
              refine ⟨5798819340271617901782229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731759120362157202376305 5798819340271617901782229)
              ·
                refine ⟨135909828287616044573021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5798819340271617901782229 135909828287616044573021)
                ·
                  rfl

theorem cell23_7146453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 7].length) (baseStart_7146453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146453 prefixEnd_7146453 := by exact prefixLift 7146453
  have htrace : WordTrace (prefixWord ++ tailWord_7146453) baseStart_7146453 baseEnd_7146453 := by
    simpa [prefixWord, tailWord_7146453, baseEnd_7146453] using wordTrace_append hprefix tailTrace_7146453
  have hstable : (prefixWord ++ tailWord_7146453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146453).length < 2 ^ (prefixWord ++ tailWord_7146453).sum := by decide
  have hdescent : baseEnd_7146453 < baseStart_7146453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146489 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_7146489 : Nat := 118140960795 + 7146489 * 2 ^ 59
def prefixEnd_7146489 : Nat := 4983230072969 + 3 ^ 40 * 7146489 * 2
def baseEnd_7146489 : Nat := 3669583849069195062621401

theorem tailTrace_7146489 : CollatzResearch.WordTrace tailWord_7146489 prefixEnd_7146489 3669583849069195062621401 := by
  unfold tailWord_7146489
  simp only [CollatzResearch.WordTrace]
  refine ⟨260653867406498350995498521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173769244937665567330332347 260653867406498350995498521)
  ·
    refine ⟨195490400554873763246623891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260653867406498350995498521 195490400554873763246623891)
    ·
      refine ⟨293235600832310644869935837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195490400554873763246623891 293235600832310644869935837)
      ·
        refine ⟨109963350312116491826225939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293235600832310644869935837 109963350312116491826225939)
        ·
          refine ⟨164945025468174737739338909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109963350312116491826225939 164945025468174737739338909)
          ·
            refine ⟨61854384550565526652252091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164945025468174737739338909 61854384550565526652252091)
            ·
              refine ⟨92781576825848289978378137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61854384550565526652252091 92781576825848289978378137)
              ·
                refine ⟨69586182619386217483783603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92781576825848289978378137 69586182619386217483783603)
                ·
                  refine ⟨104379273929079326225675405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69586182619386217483783603 104379273929079326225675405)
                  ·
                    refine ⟨39142227723404747334628277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104379273929079326225675405 39142227723404747334628277)
                    ·
                      refine ⟨3669583849069195062621401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39142227723404747334628277 3669583849069195062621401)
                      ·
                        rfl

theorem cell23_7146489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_7146489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146489 prefixEnd_7146489 := by exact prefixLift 7146489
  have htrace : WordTrace (prefixWord ++ tailWord_7146489) baseStart_7146489 baseEnd_7146489 := by
    simpa [prefixWord, tailWord_7146489, baseEnd_7146489] using wordTrace_append hprefix tailTrace_7146489
  have hstable : (prefixWord ++ tailWord_7146489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146489).length < 2 ^ (prefixWord ++ tailWord_7146489).sum := by decide
  have hdescent : baseEnd_7146489 < baseStart_7146489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146497 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_7146497 : Nat := 118140960795 + 7146497 * 2 ^ 59
def prefixEnd_7146497 : Nat := 4983230072969 + 3 ^ 40 * 7146497 * 2
def baseEnd_7146497 : Nat := 3669587956914431031321365

theorem tailTrace_7146497 : CollatzResearch.WordTrace tailWord_7146497 prefixEnd_7146497 3669587956914431031321365 := by
  unfold tailWord_7146497
  simp only [CollatzResearch.WordTrace]
  refine ⟨260654159190469368361789745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173769439460312912241193163 260654159190469368361789745)
  ·
    refine ⟨195490619392852026271342309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260654159190469368361789745 195490619392852026271342309)
    ·
      refine ⟨36654491136159754925876683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195490619392852026271342309 36654491136159754925876683)
      ·
        refine ⟨54981736704239632388815025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36654491136159754925876683 54981736704239632388815025)
        ·
          refine ⟨41236302528179724291611269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54981736704239632388815025 41236302528179724291611269)
          ·
            refine ⟨7731806724033698304677113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41236302528179724291611269 7731806724033698304677113)
            ·
              refine ⟨5798855043025273728507835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731806724033698304677113 5798855043025273728507835)
              ·
                refine ⟨8698282564537910592761753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798855043025273728507835 8698282564537910592761753)
                ·
                  refine ⟨6523711923403432944571315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8698282564537910592761753 6523711923403432944571315)
                  ·
                    refine ⟨9785567885105149416856973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6523711923403432944571315 9785567885105149416856973)
                    ·
                      refine ⟨3669587956914431031321365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785567885105149416856973 3669587956914431031321365)
                      ·
                        rfl

theorem cell23_7146497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_7146497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146497 prefixEnd_7146497 := by exact prefixLift 7146497
  have htrace : WordTrace (prefixWord ++ tailWord_7146497) baseStart_7146497 baseEnd_7146497 := by
    simpa [prefixWord, tailWord_7146497, baseEnd_7146497] using wordTrace_append hprefix tailTrace_7146497
  have hstable : (prefixWord ++ tailWord_7146497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146497).length < 2 ^ (prefixWord ++ tailWord_7146497).sum := by decide
  have hdescent : baseEnd_7146497 < baseStart_7146497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146503 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_7146503 : Nat := 118140960795 + 7146503 * 2 ^ 59
def prefixEnd_7146503 : Nat := 4983230072969 + 3 ^ 40 * 7146503 * 2
def baseEnd_7146503 : Nat := 3669591037798358007846337

theorem tailTrace_7146503 : CollatzResearch.WordTrace tailWord_7146503 prefixEnd_7146503 3669591037798358007846337 := by
  unfold tailWord_7146503
  simp only [CollatzResearch.WordTrace]
  refine ⟨260654378028447631386508163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173769585352298420924338775 260654378028447631386508163)
  ·
    refine ⟨390981567042671447079762245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260654378028447631386508163 390981567042671447079762245)
    ·
      refine ⟨73309043820500896327455421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390981567042671447079762245 73309043820500896327455421)
      ·
        refine ⟨27490891432687836122795783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73309043820500896327455421 27490891432687836122795783)
        ·
          refine ⟨41236337149031754184193675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27490891432687836122795783 41236337149031754184193675)
          ·
            refine ⟨61854505723547631276290513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41236337149031754184193675 61854505723547631276290513)
            ·
              refine ⟨46390879292660723457217885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61854505723547631276290513 46390879292660723457217885)
              ·
                refine ⟨17396579734747771296456707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46390879292660723457217885 17396579734747771296456707)
                ·
                  refine ⟨26094869602121656944685061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17396579734747771296456707 26094869602121656944685061)
                  ·
                    refine ⟨4892788050397810677128449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26094869602121656944685061 4892788050397810677128449)
                    ·
                      refine ⟨3669591037798358007846337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4892788050397810677128449 3669591037798358007846337)
                      ·
                        rfl

theorem cell23_7146503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_7146503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146503 prefixEnd_7146503 := by exact prefixLift 7146503
  have htrace : WordTrace (prefixWord ++ tailWord_7146503) baseStart_7146503 baseEnd_7146503 := by
    simpa [prefixWord, tailWord_7146503, baseEnd_7146503] using wordTrace_append hprefix tailTrace_7146503
  have hstable : (prefixWord ++ tailWord_7146503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146503).length < 2 ^ (prefixWord ++ tailWord_7146503).sum := by decide
  have hdescent : baseEnd_7146503 < baseStart_7146503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146506 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_7146506 : Nat := 118140960795 + 7146506 * 2 ^ 59
def prefixEnd_7146506 : Nat := 4983230072969 + 3 ^ 40 * 7146506 * 2
def baseEnd_7146506 : Nat := 3669592578240321496108823

theorem tailTrace_7146506 : CollatzResearch.WordTrace tailWord_7146506 prefixEnd_7146506 3669592578240321496108823 := by
  unfold tailWord_7146506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65163621861859190724716843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173769658298291175265911581 65163621861859190724716843)
  ·
    refine ⟨97745432792788786087075265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65163621861859190724716843 97745432792788786087075265)
    ·
      refine ⟨73309074594591589565306449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97745432792788786087075265 73309074594591589565306449)
      ·
        refine ⟨54981805945943692173979837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73309074594591589565306449 54981805945943692173979837)
        ·
          refine ⟨20618177229728884565242439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54981805945943692173979837 20618177229728884565242439)
          ·
            refine ⟨30927265844593326847863659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20618177229728884565242439 30927265844593326847863659)
            ·
              refine ⟨46390898766889990271795489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30927265844593326847863659 46390898766889990271795489)
              ·
                refine ⟨34793174075167492703846617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46390898766889990271795489 34793174075167492703846617)
                ·
                  refine ⟨26094880556375619527884963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34793174075167492703846617 26094880556375619527884963)
                  ·
                    refine ⟨39142320834563429291827445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26094880556375619527884963 39142320834563429291827445)
                    ·
                      refine ⟨3669592578240321496108823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39142320834563429291827445 3669592578240321496108823)
                      ·
                        rfl

theorem cell23_7146506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_7146506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146506 prefixEnd_7146506 := by exact prefixLift 7146506
  have htrace : WordTrace (prefixWord ++ tailWord_7146506) baseStart_7146506 baseEnd_7146506 := by
    simpa [prefixWord, tailWord_7146506, baseEnd_7146506] using wordTrace_append hprefix tailTrace_7146506
  have hstable : (prefixWord ++ tailWord_7146506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146506).length < 2 ^ (prefixWord ++ tailWord_7146506).sum := by decide
  have hdescent : baseEnd_7146506 < baseStart_7146506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146553 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7146553 : Nat := 118140960795 + 7146553 * 2 ^ 59
def prefixEnd_7146553 : Nat := 4983230072969 + 3 ^ 40 * 7146553 * 2
def baseEnd_7146553 : Nat := 3669616711831082812221107

theorem tailTrace_7146553 : CollatzResearch.WordTrace tailWord_7146553 prefixEnd_7146553 3669616711831082812221107 := by
  unfold tailWord_7146553
  simp only [CollatzResearch.WordTrace]
  refine ⟨260656201678266489925828313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173770801118844326617218875 260656201678266489925828313)
  ·
    refine ⟨195492151258699867444371235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260656201678266489925828313 195492151258699867444371235)
    ·
      refine ⟨293238226888049801166556853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195492151258699867444371235 293238226888049801166556853)
      ·
        refine ⟨27491083770754668859364705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293238226888049801166556853 27491083770754668859364705)
        ·
          refine ⟨20618312828066001644523529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27491083770754668859364705 20618312828066001644523529)
          ·
            refine ⟨15463734621049501233392647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20618312828066001644523529 15463734621049501233392647)
            ·
              refine ⟨23195601931574251850088971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15463734621049501233392647 23195601931574251850088971)
              ·
                refine ⟨34793402897361377775133457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23195601931574251850088971 34793402897361377775133457)
                ·
                  refine ⟨26095052173021033331350093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34793402897361377775133457 26095052173021033331350093)
                  ·
                    refine ⟨9785644564882887499256285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26095052173021033331350093 9785644564882887499256285)
                    ·
                      refine ⟨3669616711831082812221107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785644564882887499256285 3669616711831082812221107)
                      ·
                        rfl

theorem cell23_7146553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7146553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146553 prefixEnd_7146553 := by exact prefixLift 7146553
  have htrace : WordTrace (prefixWord ++ tailWord_7146553) baseStart_7146553 baseEnd_7146553 := by
    simpa [prefixWord, tailWord_7146553, baseEnd_7146553] using wordTrace_append hprefix tailTrace_7146553
  have hstable : (prefixWord ++ tailWord_7146553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146553).length < 2 ^ (prefixWord ++ tailWord_7146553).sum := by decide
  have hdescent : baseEnd_7146553 < baseStart_7146553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146569 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 10]
def baseStart_7146569 : Nat := 118140960795 + 7146569 * 2 ^ 59
def prefixEnd_7146569 : Nat := 4983230072969 + 3 ^ 40 * 7146569 * 2
def baseEnd_7146569 : Nat := 1223208309173851583207011

theorem tailTrace_7146569 : CollatzResearch.WordTrace tailWord_7146569 prefixEnd_7146569 1223208309173851583207011 := by
  unfold tailWord_7146569
  simp only [CollatzResearch.WordTrace]
  refine ⟨260656785246208524658410761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173771190164139016438940507 260656785246208524658410761)
  ·
    refine ⟨195492588934656393493808071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260656785246208524658410761 195492588934656393493808071)
    ·
      refine ⟨293238883401984590240712107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195492588934656393493808071 293238883401984590240712107)
      ·
        refine ⟨439858325102976885361068161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293238883401984590240712107 439858325102976885361068161)
        ·
          refine ⟨329893743827232664020801121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439858325102976885361068161 329893743827232664020801121)
          ·
            refine ⟨247420307870424498015600841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329893743827232664020801121 247420307870424498015600841)
            ·
              refine ⟨185565230902818373511700631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247420307870424498015600841 185565230902818373511700631)
              ·
                refine ⟨278347846354227560267550947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185565230902818373511700631 278347846354227560267550947)
                ·
                  refine ⟨417521769531341340401326421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278347846354227560267550947 417521769531341340401326421)
                  ·
                    refine ⟨1223208309173851583207011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 417521769531341340401326421 1223208309173851583207011)
                    ·
                      rfl

theorem cell23_7146569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_7146569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146569 prefixEnd_7146569 := by exact prefixLift 7146569
  have htrace : WordTrace (prefixWord ++ tailWord_7146569) baseStart_7146569 baseEnd_7146569 := by
    simpa [prefixWord, tailWord_7146569, baseEnd_7146569] using wordTrace_append hprefix tailTrace_7146569
  have hstable : (prefixWord ++ tailWord_7146569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146569).length < 2 ^ (prefixWord ++ tailWord_7146569).sum := by decide
  have hdescent : baseEnd_7146569 < baseStart_7146569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146573 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7146573 : Nat := 118140960795 + 7146573 * 2 ^ 59
def prefixEnd_7146573 : Nat := 4983230072969 + 3 ^ 40 * 7146573 * 2
def baseEnd_7146573 : Nat := 1223208993814724244657005

theorem tailTrace_7146573 : CollatzResearch.WordTrace tailWord_7146573 prefixEnd_7146573 1223208993814724244657005 := by
  unfold tailWord_7146573
  simp only [CollatzResearch.WordTrace]
  refine ⟨260656931138194033341556373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173771287425462688894370915 260656931138194033341556373)
  ·
    refine ⟨12218293647102845312885455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260656931138194033341556373 12218293647102845312885455)
    ·
      refine ⟨18327440470654267969328183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12218293647102845312885455 18327440470654267969328183)
      ·
        refine ⟨27491160705981401953992275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18327440470654267969328183 27491160705981401953992275)
        ·
          refine ⟨41236741058972102930988413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27491160705981401953992275 41236741058972102930988413)
          ·
            refine ⟨15463777897114538599120655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41236741058972102930988413 15463777897114538599120655)
            ·
              refine ⟨23195666845671807898680983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15463777897114538599120655 23195666845671807898680983)
              ·
                refine ⟨34793500268507711848021475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23195666845671807898680983 34793500268507711848021475)
                ·
                  refine ⟨52190250402761567772032213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34793500268507711848021475 52190250402761567772032213)
                  ·
                    refine ⟨1223208993814724244657005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52190250402761567772032213 1223208993814724244657005)
                    ·
                      rfl

theorem cell23_7146573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7146573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146573 prefixEnd_7146573 := by exact prefixLift 7146573
  have htrace : WordTrace (prefixWord ++ tailWord_7146573) baseStart_7146573 baseEnd_7146573 := by
    simpa [prefixWord, tailWord_7146573, baseEnd_7146573] using wordTrace_append hprefix tailTrace_7146573
  have hstable : (prefixWord ++ tailWord_7146573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146573).length < 2 ^ (prefixWord ++ tailWord_7146573).sum := by decide
  have hdescent : baseEnd_7146573 < baseStart_7146573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146593 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_7146593 : Nat := 118140960795 + 7146593 * 2 ^ 59
def prefixEnd_7146593 : Nat := 4983230072969 + 3 ^ 40 * 7146593 * 2
def baseEnd_7146593 : Nat := 3669637251057262655720923

theorem tailTrace_7146593 : CollatzResearch.WordTrace tailWord_7146593 prefixEnd_7146593 3669637251057262655720923 := by
  unfold tailWord_7146593
  simp only [CollatzResearch.WordTrace]
  refine ⟨260657660598121576757284433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173771773732081051171522955 260657660598121576757284433)
  ·
    refine ⟨195493245448591182567963325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260657660598121576757284433 195493245448591182567963325)
    ·
      refine ⟨73309967043221693462986247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195493245448591182567963325 73309967043221693462986247)
      ·
        refine ⟨109964950564832540194479371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73309967043221693462986247 109964950564832540194479371)
        ·
          refine ⟨164947425847248810291719057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109964950564832540194479371 164947425847248810291719057)
          ·
            refine ⟨123710569385436607718789293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164947425847248810291719057 123710569385436607718789293)
            ·
              refine ⟨46391463519538727894545985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123710569385436607718789293 46391463519538727894545985)
              ·
                refine ⟨34793597639654045920909489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46391463519538727894545985 34793597639654045920909489)
                ·
                  refine ⟨26095198229740534440682117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34793597639654045920909489 26095198229740534440682117)
                  ·
                    refine ⟨4892849668076350207627897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26095198229740534440682117 4892849668076350207627897)
                    ·
                      refine ⟨3669637251057262655720923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4892849668076350207627897 3669637251057262655720923)
                      ·
                        rfl

theorem cell23_7146593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_7146593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146593 prefixEnd_7146593 := by exact prefixLift 7146593
  have htrace : WordTrace (prefixWord ++ tailWord_7146593) baseStart_7146593 baseEnd_7146593 := by
    simpa [prefixWord, tailWord_7146593, baseEnd_7146593] using wordTrace_append hprefix tailTrace_7146593
  have hstable : (prefixWord ++ tailWord_7146593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146593).length < 2 ^ (prefixWord ++ tailWord_7146593).sum := by decide
  have hdescent : baseEnd_7146593 < baseStart_7146593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146616 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 6]
def baseStart_7146616 : Nat := 118140960795 + 7146616 * 2 ^ 59
def prefixEnd_7146616 : Nat := 4983230072969 + 3 ^ 40 * 7146616 * 2
def baseEnd_7146616 : Nat := 407738784568035118414813

theorem tailTrace_7146616 : CollatzResearch.WordTrace tailWord_7146616 prefixEnd_7146616 407738784568035118414813 := by
  unfold tailWord_7146616
  simp only [CollatzResearch.WordTrace]
  refine ⟨130329249738519125842685851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173772332984692167790247801 130329249738519125842685851)
  ·
    refine ⟨195493874607778688764028777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130329249738519125842685851 195493874607778688764028777)
    ·
      refine ⟨146620405955834016573021583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195493874607778688764028777 146620405955834016573021583)
      ·
        refine ⟨219930608933751024859532375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146620405955834016573021583 219930608933751024859532375)
        ·
          refine ⟨329895913400626537289298563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219930608933751024859532375 329895913400626537289298563)
          ·
            refine ⟨494843870100939805933947845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329895913400626537289298563 494843870100939805933947845)
            ·
              refine ⟨92783225643926213612615221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494843870100939805933947845 92783225643926213612615221)
              ·
                refine ⟨8698427404118082526182677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92783225643926213612615221 8698427404118082526182677)
                ·
                  refine ⟨407738784568035118414813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8698427404118082526182677 407738784568035118414813)
                  ·
                    rfl

theorem cell23_7146616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 6].length) (baseStart_7146616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146616 prefixEnd_7146616 := by exact prefixLift 7146616
  have htrace : WordTrace (prefixWord ++ tailWord_7146616) baseStart_7146616 baseEnd_7146616 := by
    simpa [prefixWord, tailWord_7146616, baseEnd_7146616] using wordTrace_append hprefix tailTrace_7146616
  have hstable : (prefixWord ++ tailWord_7146616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146616).length < 2 ^ (prefixWord ++ tailWord_7146616).sum := by decide
  have hdescent : baseEnd_7146616 < baseStart_7146616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146643 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 3]
def baseStart_7146643 : Nat := 118140960795 + 7146643 * 2 ^ 59
def prefixEnd_7146643 : Nat := 4983230072969 + 3 ^ 40 * 7146643 * 2
def baseEnd_7146643 : Nat := 3669662925089987460095693

theorem tailTrace_7146643 : CollatzResearch.WordTrace tailWord_7146643 prefixEnd_7146643 3669662925089987460095693 := by
  unfold tailWord_7146643
  simp only [CollatzResearch.WordTrace]
  refine ⟨260659484247940435296604583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173772989498626956864403055 260659484247940435296604583)
  ·
    refine ⟨390989226371910652944906875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260659484247940435296604583 390989226371910652944906875)
    ·
      refine ⟨586483839557865979417360313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390989226371910652944906875 586483839557865979417360313)
      ·
        refine ⟨439862879668399484563020235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586483839557865979417360313 439862879668399484563020235)
        ·
          refine ⟨659794319502599226844530353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439862879668399484563020235 659794319502599226844530353)
          ·
            refine ⟨494845739626949420133397765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659794319502599226844530353 494845739626949420133397765)
            ·
              refine ⟨92783576180053016275012081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494845739626949420133397765 92783576180053016275012081)
              ·
                refine ⟨69587682135039762206259061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92783576180053016275012081 69587682135039762206259061)
                ·
                  refine ⟨6523845200159977706836787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69587682135039762206259061 6523845200159977706836787)
                  ·
                    refine ⟨9785767800239966560255181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6523845200159977706836787 9785767800239966560255181)
                    ·
                      refine ⟨3669662925089987460095693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785767800239966560255181 3669662925089987460095693)
                      ·
                        rfl

theorem cell23_7146643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 3].length) (baseStart_7146643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146643 prefixEnd_7146643 := by exact prefixLift 7146643
  have htrace : WordTrace (prefixWord ++ tailWord_7146643) baseStart_7146643 baseEnd_7146643 := by
    simpa [prefixWord, tailWord_7146643, baseEnd_7146643] using wordTrace_append hprefix tailTrace_7146643
  have hstable : (prefixWord ++ tailWord_7146643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146643).length < 2 ^ (prefixWord ++ tailWord_7146643).sum := by decide
  have hdescent : baseEnd_7146643 < baseStart_7146643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146683 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 4]
def baseStart_7146683 : Nat := 118140960795 + 7146683 * 2 ^ 59
def prefixEnd_7146683 : Nat := 4983230072969 + 3 ^ 40 * 7146683 * 2
def baseEnd_7146683 : Nat := 3669683464316167303595509

theorem tailTrace_7146683 : CollatzResearch.WordTrace tailWord_7146683 prefixEnd_7146683 3669683464316167303595509 := by
  unfold tailWord_7146683
  simp only [CollatzResearch.WordTrace]
  refine ⟨260660943167795522128060703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173773962111863681418707135 260660943167795522128060703)
  ·
    refine ⟨390991414751693283192091055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260660943167795522128060703 390991414751693283192091055)
    ·
      refine ⟨586487122127539924788136583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390991414751693283192091055 586487122127539924788136583)
      ·
        refine ⟨879730683191309887182204875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586487122127539924788136583 879730683191309887182204875)
        ·
          refine ⟨1319596024786964830773307313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879730683191309887182204875 1319596024786964830773307313)
          ·
            refine ⟨989697018590223623079980485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319596024786964830773307313 989697018590223623079980485)
            ·
              refine ⟨185568190985666929327496341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 989697018590223623079980485 185568190985666929327496341)
              ·
                refine ⟨8698508952453137312226391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185568190985666929327496341 8698508952453137312226391)
                ·
                  refine ⟨13047763428679705968339587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698508952453137312226391 13047763428679705968339587)
                  ·
                    refine ⟨19571645143019558952509381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13047763428679705968339587 19571645143019558952509381)
                    ·
                      refine ⟨3669683464316167303595509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19571645143019558952509381 3669683464316167303595509)
                      ·
                        rfl

theorem cell23_7146683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 4].length) (baseStart_7146683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146683 prefixEnd_7146683 := by exact prefixLift 7146683
  have htrace : WordTrace (prefixWord ++ tailWord_7146683) baseStart_7146683 baseEnd_7146683 := by
    simpa [prefixWord, tailWord_7146683, baseEnd_7146683] using wordTrace_append hprefix tailTrace_7146683
  have hstable : (prefixWord ++ tailWord_7146683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146683).length < 2 ^ (prefixWord ++ tailWord_7146683).sum := by decide
  have hdescent : baseEnd_7146683 < baseStart_7146683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146730 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_7146730 : Nat := 118140960795 + 7146730 * 2 ^ 59
def prefixEnd_7146730 : Nat := 4983230072969 + 3 ^ 40 * 7146730 * 2
def baseEnd_7146730 : Nat := 3669707597906928619707793

theorem tailTrace_7146730 : CollatzResearch.WordTrace tailWord_7146730 prefixEnd_7146730 3669707597906928619707793 := by
  unfold tailWord_7146730
  simp only [CollatzResearch.WordTrace]
  refine ⟨65165664349656312288755411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173775104932416832770014429 65165664349656312288755411)
  ·
    refine ⟨97748496524484468433133117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65165664349656312288755411 97748496524484468433133117)
    ·
      refine ⟨36655686196681675662424919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97748496524484468433133117 36655686196681675662424919)
      ·
        refine ⟨54983529295022513493637379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36655686196681675662424919 54983529295022513493637379)
        ·
          refine ⟨82475293942533770240456069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54983529295022513493637379 82475293942533770240456069)
          ·
            refine ⟨15464117614225081920085513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82475293942533770240456069 15464117614225081920085513)
            ·
              refine ⟨11598088210668811440064135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15464117614225081920085513 11598088210668811440064135)
              ·
                refine ⟨17397132316003217160096203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11598088210668811440064135 17397132316003217160096203)
                ·
                  refine ⟨26095698474004825740144305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17397132316003217160096203 26095698474004825740144305)
                  ·
                    refine ⟨19571773855503619305108229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26095698474004825740144305 19571773855503619305108229)
                    ·
                      refine ⟨3669707597906928619707793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19571773855503619305108229 3669707597906928619707793)
                      ·
                        rfl

theorem cell23_7146730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_7146730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146730 prefixEnd_7146730 := by exact prefixLift 7146730
  have htrace : WordTrace (prefixWord ++ tailWord_7146730) baseStart_7146730 baseEnd_7146730 := by
    simpa [prefixWord, tailWord_7146730, baseEnd_7146730] using wordTrace_append hprefix tailTrace_7146730
  have hstable : (prefixWord ++ tailWord_7146730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146730).length < 2 ^ (prefixWord ++ tailWord_7146730).sum := by decide
  have hdescent : baseEnd_7146730 < baseStart_7146730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146754 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7146754 : Nat := 118140960795 + 7146754 * 2 ^ 59
def prefixEnd_7146754 : Nat := 4983230072969 + 3 ^ 40 * 7146754 * 2
def baseEnd_7146754 : Nat := 3669719921442636525807683

theorem tailTrace_7146754 : CollatzResearch.WordTrace tailWord_7146754 prefixEnd_7146754 3669719921442636525807683 := by
  unfold tailWord_7146754
  simp only [CollatzResearch.WordTrace]
  refine ⟨65165883187634575313473829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173775688500358867502596877 65165883187634575313473829)
  ·
    refine ⟨12218603097681482871276343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65165883187634575313473829 12218603097681482871276343)
    ·
      refine ⟨18327904646522224306914515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12218603097681482871276343 18327904646522224306914515)
      ·
        refine ⟨27491856969783336460371773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18327904646522224306914515 27491856969783336460371773)
        ·
          refine ⟨10309446363668751172639415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27491856969783336460371773 10309446363668751172639415)
          ·
            refine ⟨15464169545503126758959123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10309446363668751172639415 15464169545503126758959123)
            ·
              refine ⟨23196254318254690138438685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15464169545503126758959123 23196254318254690138438685)
              ·
                refine ⟨8698595369345508801914507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23196254318254690138438685 8698595369345508801914507)
                ·
                  refine ⟨13047893054018263202871761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698595369345508801914507 13047893054018263202871761)
                  ·
                    refine ⟨9785919790513697402153821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13047893054018263202871761 9785919790513697402153821)
                    ·
                      refine ⟨3669719921442636525807683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785919790513697402153821 3669719921442636525807683)
                      ·
                        rfl

theorem cell23_7146754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7146754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146754 prefixEnd_7146754 := by exact prefixLift 7146754
  have htrace : WordTrace (prefixWord ++ tailWord_7146754) baseStart_7146754 baseEnd_7146754 := by
    simpa [prefixWord, tailWord_7146754, baseEnd_7146754] using wordTrace_append hprefix tailTrace_7146754
  have hstable : (prefixWord ++ tailWord_7146754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146754).length < 2 ^ (prefixWord ++ tailWord_7146754).sum := by decide
  have hdescent : baseEnd_7146754 < baseStart_7146754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146784 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 1, 3, 3]
def baseStart_7146784 : Nat := 118140960795 + 7146784 * 2 ^ 59
def prefixEnd_7146784 : Nat := 4983230072969 + 3 ^ 40 * 7146784 * 2
def baseEnd_7146784 : Nat := 3669735325862271408432545

theorem tailTrace_7146784 : CollatzResearch.WordTrace tailWord_7146784 prefixEnd_7146784 3669735325862271408432545 := by
  unfold tailWord_7146784
  simp only [CollatzResearch.WordTrace]
  refine ⟨130332313470214808188743703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173776417960286410918324937 130332313470214808188743703)
  ·
    refine ⟨195498470205322212283115555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130332313470214808188743703 195498470205322212283115555)
    ·
      refine ⟨293247705307983318424673333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195498470205322212283115555 293247705307983318424673333)
      ·
        refine ⟨27491972372623436102313125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293247705307983318424673333 27491972372623436102313125)
        ·
          refine ⟨5154744819866894269183711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27491972372623436102313125 5154744819866894269183711)
          ·
            refine ⟨7732117229800341403775567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154744819866894269183711 7732117229800341403775567)
            ·
              refine ⟨11598175844700512105663351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7732117229800341403775567 11598175844700512105663351)
              ·
                refine ⟨17397263767050768158495027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11598175844700512105663351 17397263767050768158495027)
                ·
                  refine ⟨26095895650576152237742541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17397263767050768158495027 26095895650576152237742541)
                  ·
                    refine ⟨9785960868966057089153453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26095895650576152237742541 9785960868966057089153453)
                    ·
                      refine ⟨3669735325862271408432545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9785960868966057089153453 3669735325862271408432545)
                      ·
                        rfl

theorem cell23_7146784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_7146784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146784 prefixEnd_7146784 := by exact prefixLift 7146784
  have htrace : WordTrace (prefixWord ++ tailWord_7146784) baseStart_7146784 baseEnd_7146784 := by
    simpa [prefixWord, tailWord_7146784, baseEnd_7146784] using wordTrace_append hprefix tailTrace_7146784
  have hstable : (prefixWord ++ tailWord_7146784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146784).length < 2 ^ (prefixWord ++ tailWord_7146784).sum := by decide
  have hdescent : baseEnd_7146784 < baseStart_7146784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146794 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7146794 : Nat := 118140960795 + 7146794 * 2 ^ 59
def prefixEnd_7146794 : Nat := 4983230072969 + 3 ^ 40 * 7146794 * 2
def baseEnd_7146794 : Nat := 3669740460668816369307499

theorem tailTrace_7146794 : CollatzResearch.WordTrace tailWord_7146794 prefixEnd_7146794 3669740460668816369307499 := by
  unfold tailWord_7146794
  simp only [CollatzResearch.WordTrace]
  refine ⟨65166247917598347021337859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173776661113595592056900957 65166247917598347021337859)
  ·
    refine ⟨97749371876397520532006789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65166247917598347021337859 97749371876397520532006789)
    ·
      refine ⟨18328007226824535099751273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97749371876397520532006789 18328007226824535099751273)
      ·
        refine ⟨13746005420118401324813455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18328007226824535099751273 13746005420118401324813455)
        ·
          refine ⟨20619008130177601987220183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13746005420118401324813455 20619008130177601987220183)
          ·
            refine ⟨30928512195266402980830275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20619008130177601987220183 30928512195266402980830275)
            ·
              refine ⟨46392768292899604471245413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30928512195266402980830275 46392768292899604471245413)
              ·
                refine ⟨8698644054918675838358515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46392768292899604471245413 8698644054918675838358515)
                ·
                  refine ⟨13047966082378013757537773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698644054918675838358515 13047966082378013757537773)
                  ·
                    refine ⟨4892987280891755159076665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13047966082378013757537773 4892987280891755159076665)
                    ·
                      refine ⟨3669740460668816369307499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4892987280891755159076665 3669740460668816369307499)
                      ·
                        rfl

theorem cell23_7146794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7146794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146794 prefixEnd_7146794 := by exact prefixLift 7146794
  have htrace : WordTrace (prefixWord ++ tailWord_7146794) baseStart_7146794 baseEnd_7146794 := by
    simpa [prefixWord, tailWord_7146794, baseEnd_7146794] using wordTrace_append hprefix tailTrace_7146794
  have hstable : (prefixWord ++ tailWord_7146794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146794).length < 2 ^ (prefixWord ++ tailWord_7146794).sum := by decide
  have hdescent : baseEnd_7146794 < baseStart_7146794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146845 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7146845 : Nat := 118140960795 + 7146845 * 2 ^ 59
def prefixEnd_7146845 : Nat := 4983230072969 + 3 ^ 40 * 7146845 * 2
def baseEnd_7146845 : Nat := 3669766648182195669769765

theorem tailTrace_7146845 : CollatzResearch.WordTrace tailWord_7146845 prefixEnd_7146845 3669766648182195669769765 := by
  unfold tailWord_7146845
  simp only [CollatzResearch.WordTrace]
  refine ⟨260666851793208623795457989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173777901195472415863638659 260666851793208623795457989)
  ·
    refine ⟨48875034711226616961648373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260666851793208623795457989 48875034711226616961648373)
    ·
      refine ⟨4582034504177495340154535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48875034711226616961648373 4582034504177495340154535)
      ·
        refine ⟨6873051756266243010231803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582034504177495340154535 6873051756266243010231803)
        ·
          refine ⟨10309577634399364515347705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6873051756266243010231803 10309577634399364515347705)
          ·
            refine ⟨7732183225799523386510779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10309577634399364515347705 7732183225799523386510779)
            ·
              refine ⟨11598274838699285079766169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7732183225799523386510779 11598274838699285079766169)
              ·
                refine ⟨8698706129024463809824627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11598274838699285079766169 8698706129024463809824627)
                ·
                  refine ⟨13048059193536695714736941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698706129024463809824627 13048059193536695714736941)
                  ·
                    refine ⟨4893022197576260893026353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13048059193536695714736941 4893022197576260893026353)
                    ·
                      refine ⟨3669766648182195669769765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893022197576260893026353 3669766648182195669769765)
                      ·
                        rfl

theorem cell23_7146845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7146845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146845 prefixEnd_7146845 := by exact prefixLift 7146845
  have htrace : WordTrace (prefixWord ++ tailWord_7146845) baseStart_7146845 baseEnd_7146845 := by
    simpa [prefixWord, tailWord_7146845, baseEnd_7146845] using wordTrace_append hprefix tailTrace_7146845
  have hstable : (prefixWord ++ tailWord_7146845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146845).length < 2 ^ (prefixWord ++ tailWord_7146845).sum := by decide
  have hdescent : baseEnd_7146845 < baseStart_7146845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146853 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_7146853 : Nat := 118140960795 + 7146853 * 2 ^ 59
def prefixEnd_7146853 : Nat := 4983230072969 + 3 ^ 40 * 7146853 * 2
def baseEnd_7146853 : Nat := 3669770756027431638469727

theorem tailTrace_7146853 : CollatzResearch.WordTrace tailWord_7146853 prefixEnd_7146853 3669770756027431638469727 := by
  unfold tailWord_7146853
  simp only [CollatzResearch.WordTrace]
  refine ⟨260667143577179641161749213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173778095718119760774499475 260667143577179641161749213)
  ·
    refine ⟨97750178841442365435655955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260667143577179641161749213 97750178841442365435655955)
    ·
      refine ⟨146625268262163548153483933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97750178841442365435655955 146625268262163548153483933)
      ·
        refine ⟨54984475598311330557556475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146625268262163548153483933 54984475598311330557556475)
        ·
          refine ⟨82476713397466995836334713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54984475598311330557556475 82476713397466995836334713)
          ·
            refine ⟨61857535048100246877251035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82476713397466995836334713 61857535048100246877251035)
            ·
              refine ⟨92786302572150370315876553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61857535048100246877251035 92786302572150370315876553)
              ·
                refine ⟨69589726929112777736907415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92786302572150370315876553 69589726929112777736907415)
                ·
                  refine ⟨104384590393669166605361123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69589726929112777736907415 104384590393669166605361123)
                  ·
                    refine ⟨156576885590503749908041685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104384590393669166605361123 156576885590503749908041685)
                    ·
                      refine ⟨3669770756027431638469727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156576885590503749908041685 3669770756027431638469727)
                      ·
                        rfl

theorem cell23_7146853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_7146853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146853 prefixEnd_7146853 := by exact prefixLift 7146853
  have htrace : WordTrace (prefixWord ++ tailWord_7146853) baseStart_7146853 baseEnd_7146853 := by
    simpa [prefixWord, tailWord_7146853, baseEnd_7146853] using wordTrace_append hprefix tailTrace_7146853
  have hstable : (prefixWord ++ tailWord_7146853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146853).length < 2 ^ (prefixWord ++ tailWord_7146853).sum := by decide
  have hdescent : baseEnd_7146853 < baseStart_7146853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146860 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_7146860 : Nat := 118140960795 + 7146860 * 2 ^ 59
def prefixEnd_7146860 : Nat := 4983230072969 + 3 ^ 40 * 7146860 * 2
def baseEnd_7146860 : Nat := 1223258116797337703694065

theorem tailTrace_7146860 : CollatzResearch.WordTrace tailWord_7146860 prefixEnd_7146860 1223258116797337703694065 := by
  unfold tailWord_7146860
  simp only [CollatzResearch.WordTrace]
  refine ⟨130333699444077140678627017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173778265925436187571502689 130333699444077140678627017)
  ·
    refine ⟨97750274583057855508970263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130333699444077140678627017 97750274583057855508970263)
    ·
      refine ⟨146625411874586783263455395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97750274583057855508970263 146625411874586783263455395)
      ·
        refine ⟨219938117811880174895183093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146625411874586783263455395 219938117811880174895183093)
        ·
          refine ⟨20619198544863766396423415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219938117811880174895183093 20619198544863766396423415)
          ·
            refine ⟨30928797817295649594635123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20619198544863766396423415 30928797817295649594635123)
            ·
              refine ⟨46393196725943474391952685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30928797817295649594635123 46393196725943474391952685)
              ·
                refine ⟨17397448772228802896982257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46393196725943474391952685 17397448772228802896982257)
                ·
                  refine ⟨13048086579171602172736693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17397448772228802896982257 13048086579171602172736693)
                  ·
                    refine ⟨1223258116797337703694065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13048086579171602172736693 1223258116797337703694065)
                    ·
                      rfl

theorem cell23_7146860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_7146860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146860 prefixEnd_7146860 := by exact prefixLift 7146860
  have htrace : WordTrace (prefixWord ++ tailWord_7146860) baseStart_7146860 baseEnd_7146860 := by
    simpa [prefixWord, tailWord_7146860, baseEnd_7146860] using wordTrace_append hprefix tailTrace_7146860
  have hstable : (prefixWord ++ tailWord_7146860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146860).length < 2 ^ (prefixWord ++ tailWord_7146860).sum := by decide
  have hdescent : baseEnd_7146860 < baseStart_7146860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146880 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 3, 6, 2]
def baseStart_7146880 : Nat := 118140960795 + 7146880 * 2 ^ 59
def prefixEnd_7146880 : Nat := 4983230072969 + 3 ^ 40 * 7146880 * 2
def baseEnd_7146880 : Nat := 3669784620005103032832103

theorem tailTrace_7146880 : CollatzResearch.WordTrace tailWord_7146880 prefixEnd_7146880 3669784620005103032832103 := by
  unfold tailWord_7146880
  simp only [CollatzResearch.WordTrace]
  refine ⟨130334064174040912386491047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173778752232054549848654729 130334064174040912386491047)
  ·
    refine ⟨195501096261061368579736571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130334064174040912386491047 195501096261061368579736571)
    ·
      refine ⟨293251644391592052869604857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195501096261061368579736571 293251644391592052869604857)
      ·
        refine ⟨219938733293694039652203643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293251644391592052869604857 219938733293694039652203643)
        ·
          refine ⟨329908099940541059478305465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219938733293694039652203643 329908099940541059478305465)
          ·
            refine ⟨247431074955405794608729099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329908099940541059478305465 247431074955405794608729099)
            ·
              refine ⟨371146612433108691913093649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247431074955405794608729099 371146612433108691913093649)
              ·
                refine ⟨278359959324831518934820237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371146612433108691913093649 278359959324831518934820237)
                ·
                  refine ⟨104384984746811819600557589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278359959324831518934820237 104384984746811819600557589)
                  ·
                    refine ⟨4893046160006804043776137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104384984746811819600557589 4893046160006804043776137)
                    ·
                      refine ⟨3669784620005103032832103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893046160006804043776137 3669784620005103032832103)
                      ·
                        rfl

theorem cell23_7146880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_7146880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146880 prefixEnd_7146880 := by exact prefixLift 7146880
  have htrace : WordTrace (prefixWord ++ tailWord_7146880) baseStart_7146880 baseEnd_7146880 := by
    simpa [prefixWord, tailWord_7146880, baseEnd_7146880] using wordTrace_append hprefix tailTrace_7146880
  have hstable : (prefixWord ++ tailWord_7146880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146880).length < 2 ^ (prefixWord ++ tailWord_7146880).sum := by decide
  have hdescent : baseEnd_7146880 < baseStart_7146880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146881 : List Nat := [1, 2, 4, 3, 2, 2, 2, 2, 5]
def baseStart_7146881 : Nat := 118140960795 + 7146881 * 2 ^ 59
def prefixEnd_7146881 : Nat := 4983230072969 + 3 ^ 40 * 7146881 * 2
def baseEnd_7146881 : Nat := 407753903720639725435511

theorem tailTrace_7146881 : CollatzResearch.WordTrace tailWord_7146881 prefixEnd_7146881 407753903720639725435511 := by
  unfold tailWord_7146881
  simp only [CollatzResearch.WordTrace]
  refine ⟨260668164821078201943768497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173778776547385467962512331 260668164821078201943768497)
  ·
    refine ⟨195501123615808651457826373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260668164821078201943768497 195501123615808651457826373)
    ·
      refine ⟨36656460677964122148342445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195501123615808651457826373 36656460677964122148342445)
      ·
        refine ⟨13746172754236545805628417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36656460677964122148342445 13746172754236545805628417)
        ·
          refine ⟨10309629565677409354221313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13746172754236545805628417 10309629565677409354221313)
          ·
            refine ⟨7732222174258057015665985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10309629565677409354221313 7732222174258057015665985)
            ·
              refine ⟨5799166630693542761749489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7732222174258057015665985 5799166630693542761749489)
              ·
                refine ⟨4349374973020157071312117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5799166630693542761749489 4349374973020157071312117)
                ·
                  refine ⟨407753903720639725435511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4349374973020157071312117 407753903720639725435511)
                  ·
                    rfl

theorem cell23_7146881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 5].length) (baseStart_7146881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146881 prefixEnd_7146881 := by exact prefixLift 7146881
  have htrace : WordTrace (prefixWord ++ tailWord_7146881) baseStart_7146881 baseEnd_7146881 := by
    simpa [prefixWord, tailWord_7146881, baseEnd_7146881] using wordTrace_append hprefix tailTrace_7146881
  have hstable : (prefixWord ++ tailWord_7146881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146881).length < 2 ^ (prefixWord ++ tailWord_7146881).sum := by decide
  have hdescent : baseEnd_7146881 < baseStart_7146881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146903 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 10]
def baseStart_7146903 : Nat := 118140960795 + 7146903 * 2 ^ 59
def prefixEnd_7146903 : Nat := 4983230072969 + 3 ^ 40 * 7146903 * 2
def baseEnd_7146903 : Nat := 407755158895572938093833

theorem tailTrace_7146903 : CollatzResearch.WordTrace tailWord_7146903 prefixEnd_7146903 407755158895572938093833 := by
  unfold tailWord_7146903
  simp only [CollatzResearch.WordTrace]
  refine ⟨260668967226998499701069363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173779311484665666467379575 260668967226998499701069363)
  ·
    refine ⟨391003450840497749551604045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260668967226998499701069363 391003450840497749551604045)
    ·
      refine ⟨146626294065186656081851517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391003450840497749551604045 146626294065186656081851517)
      ·
        refine ⟨54984860274444996030694319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146626294065186656081851517 54984860274444996030694319)
        ·
          refine ⟨82477290411667494046041479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54984860274444996030694319 82477290411667494046041479)
          ·
            refine ⟨123715935617501241069062219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82477290411667494046041479 123715935617501241069062219)
            ·
              refine ⟨185573903426251861603593329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123715935617501241069062219 185573903426251861603593329)
              ·
                refine ⟨139180427569688896202694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185573903426251861603593329 139180427569688896202694997)
                ·
                  refine ⟨407755158895572938093833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 139180427569688896202694997 407755158895572938093833)
                  ·
                    rfl

theorem cell23_7146903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 10].length) (baseStart_7146903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146903 prefixEnd_7146903 := by exact prefixLift 7146903
  have htrace : WordTrace (prefixWord ++ tailWord_7146903) baseStart_7146903 baseEnd_7146903 := by
    simpa [prefixWord, tailWord_7146903, baseEnd_7146903] using wordTrace_append hprefix tailTrace_7146903
  have hstable : (prefixWord ++ tailWord_7146903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146903).length < 2 ^ (prefixWord ++ tailWord_7146903).sum := by decide
  have hdescent : baseEnd_7146903 < baseStart_7146903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146914 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_7146914 : Nat := 118140960795 + 7146914 * 2 ^ 59
def prefixEnd_7146914 : Nat := 4983230072969 + 3 ^ 40 * 7146914 * 2
def baseEnd_7146914 : Nat := 3669802078347355899806947

theorem tailTrace_7146914 : CollatzResearch.WordTrace tailWord_7146914 prefixEnd_7146914 3669802078347355899806947 := by
  unfold tailWord_7146914
  simp only [CollatzResearch.WordTrace]
  refine ⟨65167342107489662144929949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173779578953305765719813197 65167342107489662144929949)
  ·
    refine ⟨24437753290308623304348731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65167342107489662144929949 24437753290308623304348731)
    ·
      refine ⟨36656629935462934956523097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24437753290308623304348731 36656629935462934956523097)
      ·
        refine ⟨27492472451597201217392323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36656629935462934956523097 27492472451597201217392323)
        ·
          refine ⟨41238708677395801826088485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27492472451597201217392323 41238708677395801826088485)
          ·
            refine ⟨7732257877011712842391591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41238708677395801826088485 7732257877011712842391591)
            ·
              refine ⟨11598386815517569263587387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7732257877011712842391591 11598386815517569263587387)
              ·
                refine ⟨17397580223276353895381081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11598386815517569263587387 17397580223276353895381081)
                ·
                  refine ⟨13048185167457265421535811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17397580223276353895381081 13048185167457265421535811)
                  ·
                    refine ⟨19572277751185898132303717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13048185167457265421535811 19572277751185898132303717)
                    ·
                      refine ⟨3669802078347355899806947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19572277751185898132303717 3669802078347355899806947)
                      ·
                        rfl

theorem cell23_7146914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_7146914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146914 prefixEnd_7146914 := by exact prefixLift 7146914
  have htrace : WordTrace (prefixWord ++ tailWord_7146914) baseStart_7146914 baseEnd_7146914 := by
    simpa [prefixWord, tailWord_7146914, baseEnd_7146914] using wordTrace_append hprefix tailTrace_7146914
  have hstable : (prefixWord ++ tailWord_7146914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146914).length < 2 ^ (prefixWord ++ tailWord_7146914).sum := by decide
  have hdescent : baseEnd_7146914 < baseStart_7146914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146947 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 3]
def baseStart_7146947 : Nat := 118140960795 + 7146947 * 2 ^ 59
def prefixEnd_7146947 : Nat := 4983230072969 + 3 ^ 40 * 7146947 * 2
def baseEnd_7146947 : Nat := 3669819023208954270694295

theorem tailTrace_7146947 : CollatzResearch.WordTrace tailWord_7146947 prefixEnd_7146947 3669819023208954270694295 := by
  unfold tailWord_7146947
  simp only [CollatzResearch.WordTrace]
  refine ⟨260670572038839095215671095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173780381359226063477114063 260670572038839095215671095)
  ·
    refine ⟨391005858058258642823506643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260670572038839095215671095 391005858058258642823506643)
    ·
      refine ⟨586508787087387964235259965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391005858058258642823506643 586508787087387964235259965)
      ·
        refine ⟨219940795157770486588222487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 586508787087387964235259965 219940795157770486588222487)
        ·
          refine ⟨329911192736655729882333731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219940795157770486588222487 329911192736655729882333731)
          ·
            refine ⟨494866789104983594823500597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329911192736655729882333731 494866789104983594823500597)
            ·
              refine ⟨46393761478592212014703181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 494866789104983594823500597 46393761478592212014703181)
              ·
                refine ⟨17397660554472079505513693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46393761478592212014703181 17397660554472079505513693)
                ·
                  refine ⟨6524122707927029814567635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17397660554472079505513693 6524122707927029814567635)
                  ·
                    refine ⟨9786184061890544721851453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6524122707927029814567635 9786184061890544721851453)
                    ·
                      refine ⟨3669819023208954270694295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9786184061890544721851453 3669819023208954270694295)
                      ·
                        rfl

theorem cell23_7146947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_7146947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146947 prefixEnd_7146947 := by exact prefixLift 7146947
  have htrace : WordTrace (prefixWord ++ tailWord_7146947) baseStart_7146947 baseEnd_7146947 := by
    simpa [prefixWord, tailWord_7146947, baseEnd_7146947] using wordTrace_append hprefix tailTrace_7146947
  have hstable : (prefixWord ++ tailWord_7146947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146947).length < 2 ^ (prefixWord ++ tailWord_7146947).sum := by decide
  have hdescent : baseEnd_7146947 < baseStart_7146947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7146980 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_7146980 : Nat := 118140960795 + 7146980 * 2 ^ 59
def prefixEnd_7146980 : Nat := 4983230072969 + 3 ^ 40 * 7146980 * 2
def baseEnd_7146980 : Nat := 1223278656023517547193881

theorem tailTrace_7146980 : CollatzResearch.WordTrace tailWord_7146980 prefixEnd_7146980 1223278656023517547193881 := by
  unfold tailWord_7146980
  simp only [CollatzResearch.WordTrace]
  refine ⟨130335887823859770925811197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173781183765146361234414929 130335887823859770925811197)
  ·
    refine ⟨48875957933947414097179199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130335887823859770925811197 48875957933947414097179199)
    ·
      refine ⟨73313936900921121145768799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48875957933947414097179199 73313936900921121145768799)
      ·
        refine ⟨109970905351381681718653199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73313936900921121145768799 109970905351381681718653199)
        ·
          refine ⟨164956358027072522577979799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109970905351381681718653199 164956358027072522577979799)
          ·
            refine ⟨247434537040608783866969699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164956358027072522577979799 247434537040608783866969699)
            ·
              refine ⟨371151805560913175800454549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247434537040608783866969699 371151805560913175800454549)
              ·
                refine ⟨17397740885667805115646307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 371151805560913175800454549 17397740885667805115646307)
                ·
                  refine ⟨26096611328501707673469461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17397740885667805115646307 26096611328501707673469461)
                  ·
                    refine ⟨1223278656023517547193881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26096611328501707673469461 1223278656023517547193881)
                    ·
                      rfl

theorem cell23_7146980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_7146980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7146980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7146980 prefixEnd_7146980 := by exact prefixLift 7146980
  have htrace : WordTrace (prefixWord ++ tailWord_7146980) baseStart_7146980 baseEnd_7146980 := by
    simpa [prefixWord, tailWord_7146980, baseEnd_7146980] using wordTrace_append hprefix tailTrace_7146980
  have hstable : (prefixWord ++ tailWord_7146980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7146980).length < 2 ^ (prefixWord ++ tailWord_7146980).sum := by decide
  have hdescent : baseEnd_7146980 < baseStart_7146980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7146980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147000 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_7147000 : Nat := 118140960795 + 7147000 * 2 ^ 59
def prefixEnd_7147000 : Nat := 4983230072969 + 3 ^ 40 * 7147000 * 2
def baseEnd_7147000 : Nat := 3669846237683642563331551

theorem tailTrace_7147000 : CollatzResearch.WordTrace tailWord_7147000 prefixEnd_7147000 3669846237683642563331551 := by
  unfold tailWord_7147000
  simp only [CollatzResearch.WordTrace]
  refine ⟨130336252553823542633675227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173781670071764723511566969 130336252553823542633675227)
  ·
    refine ⟨195504378830735313950512841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130336252553823542633675227 195504378830735313950512841)
    ·
      refine ⟨146628284123051485462884631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195504378830735313950512841 146628284123051485462884631)
      ·
        refine ⟨219942426184577228194326947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146628284123051485462884631 219942426184577228194326947)
        ·
          refine ⟨329913639276865842291490421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219942426184577228194326947 329913639276865842291490421)
          ·
            refine ⟨30929403682206172714827227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 329913639276865842291490421 30929403682206172714827227)
            ·
              refine ⟨46394105523309259072240841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30929403682206172714827227 46394105523309259072240841)
              ·
                refine ⟨34795579142481944304180631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46394105523309259072240841 34795579142481944304180631)
                ·
                  refine ⟨52193368713722916456270947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34795579142481944304180631 52193368713722916456270947)
                  ·
                    refine ⟨78290053070584374684406421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52193368713722916456270947 78290053070584374684406421)
                    ·
                      refine ⟨3669846237683642563331551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78290053070584374684406421 3669846237683642563331551)
                      ·
                        rfl

theorem cell23_7147000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_7147000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147000 prefixEnd_7147000 := by exact prefixLift 7147000
  have htrace : WordTrace (prefixWord ++ tailWord_7147000) baseStart_7147000 baseEnd_7147000 := by
    simpa [prefixWord, tailWord_7147000, baseEnd_7147000] using wordTrace_append hprefix tailTrace_7147000
  have hstable : (prefixWord ++ tailWord_7147000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147000).length < 2 ^ (prefixWord ++ tailWord_7147000).sum := by decide
  have hdescent : baseEnd_7147000 < baseStart_7147000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147041 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_7147041 : Nat := 118140960795 + 7147041 * 2 ^ 59
def prefixEnd_7147041 : Nat := 4983230072969 + 3 ^ 40 * 7147041 * 2
def baseEnd_7147041 : Nat := 3669867290390476902918863

theorem tailTrace_7147041 : CollatzResearch.WordTrace tailWord_7147041 prefixEnd_7147041 3669867290390476902918863 := by
  unfold tailWord_7147041
  simp only [CollatzResearch.WordTrace]
  refine ⟨260674000500498549269592977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173782667000332366179728651 260674000500498549269592977)
  ·
    refine ⟨195505500375373911952194733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260674000500498549269592977 195505500375373911952194733)
    ·
      refine ⟨73314562640765216982073025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195505500375373911952194733 73314562640765216982073025)
      ·
        refine ⟨54985921980573912736554769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73314562640765216982073025 54985921980573912736554769)
        ·
          refine ⟨41239441485430434552416077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54985921980573912736554769 41239441485430434552416077)
          ·
            refine ⟨15464790557036412957156029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41239441485430434552416077 15464790557036412957156029)
            ·
              refine ⟨5799296458888654858933511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15464790557036412957156029 5799296458888654858933511)
              ·
                refine ⟨8698944688332982288400267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799296458888654858933511 8698944688332982288400267)
                ·
                  refine ⟨13048417032499473432600401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698944688332982288400267 13048417032499473432600401)
                  ·
                    refine ⟨9786312774374605074450301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13048417032499473432600401 9786312774374605074450301)
                    ·
                      refine ⟨3669867290390476902918863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9786312774374605074450301 3669867290390476902918863)
                      ·
                        rfl

theorem cell23_7147041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_7147041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147041 prefixEnd_7147041 := by exact prefixLift 7147041
  have htrace : WordTrace (prefixWord ++ tailWord_7147041) baseStart_7147041 baseEnd_7147041 := by
    simpa [prefixWord, tailWord_7147041, baseEnd_7147041] using wordTrace_append hprefix tailTrace_7147041
  have hstable : (prefixWord ++ tailWord_7147041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147041).length < 2 ^ (prefixWord ++ tailWord_7147041).sum := by decide
  have hdescent : baseEnd_7147041 < baseStart_7147041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147064 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 3, 3, 2]
def baseStart_7147064 : Nat := 118140960795 + 7147064 * 2 ^ 59
def prefixEnd_7147064 : Nat := 4983230072969 + 3 ^ 40 * 7147064 * 2
def baseEnd_7147064 : Nat := 3669879100445530312931257

theorem tailTrace_7147064 : CollatzResearch.WordTrace tailWord_7147064 prefixEnd_7147064 3669879100445530312931257 := by
  unfold tailWord_7147064
  simp only [CollatzResearch.WordTrace]
  refine ⟨130337419689707612098840123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173783226252943482798453497 130337419689707612098840123)
  ·
    refine ⟨195506129534561418148260185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130337419689707612098840123 195506129534561418148260185)
    ·
      refine ⟨146629597150921063611195139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195506129534561418148260185 146629597150921063611195139)
      ·
        refine ⟨219944395726381595416792709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146629597150921063611195139 219944395726381595416792709)
        ·
          refine ⟨41239574198696549140648633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219944395726381595416792709 41239574198696549140648633)
          ·
            refine ⟨30929680649022411855486475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41239574198696549140648633 30929680649022411855486475)
            ·
              refine ⟨46394520973533617783229713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30929680649022411855486475 46394520973533617783229713)
              ·
                refine ⟨34795890730150213337422285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46394520973533617783229713 34795890730150213337422285)
                ·
                  refine ⟨13048459023806330001533357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34795890730150213337422285 13048459023806330001533357)
                  ·
                    refine ⟨4893172133927373750575009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13048459023806330001533357 4893172133927373750575009)
                    ·
                      refine ⟨3669879100445530312931257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893172133927373750575009 3669879100445530312931257)
                      ·
                        rfl

theorem cell23_7147064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_7147064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147064 prefixEnd_7147064 := by exact prefixLift 7147064
  have htrace : WordTrace (prefixWord ++ tailWord_7147064) baseStart_7147064 baseEnd_7147064 := by
    simpa [prefixWord, tailWord_7147064, baseEnd_7147064] using wordTrace_append hprefix tailTrace_7147064
  have hstable : (prefixWord ++ tailWord_7147064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147064).length < 2 ^ (prefixWord ++ tailWord_7147064).sum := by decide
  have hdescent : baseEnd_7147064 < baseStart_7147064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147107 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4]
def baseStart_7147107 : Nat := 118140960795 + 7147107 * 2 ^ 59
def prefixEnd_7147107 : Nat := 4983230072969 + 3 ^ 40 * 7147107 * 2
def baseEnd_7147107 : Nat := 3669901180113673644693559

theorem tailTrace_7147107 : CollatzResearch.WordTrace tailWord_7147107 prefixEnd_7147107 3669901180113673644693559 := by
  unfold tailWord_7147107
  simp only [CollatzResearch.WordTrace]
  refine ⟨260676407718259442541495575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173784271812172961694330383 260676407718259442541495575)
  ·
    refine ⟨391014611577389163812243363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260676407718259442541495575 391014611577389163812243363)
    ·
      refine ⟨586521917366083745718365045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391014611577389163812243363 586521917366083745718365045)
      ·
        refine ⟨54986429753070351161096723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 586521917366083745718365045 54986429753070351161096723)
        ·
          refine ⟨82479644629605526741645085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54986429753070351161096723 82479644629605526741645085)
          ·
            refine ⟨30929866736102072528116907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82479644629605526741645085 30929866736102072528116907)
            ·
              refine ⟨46394800104153108792175361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30929866736102072528116907 46394800104153108792175361)
              ·
                refine ⟨34796100078114831594131521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46394800104153108792175361 34796100078114831594131521)
                ·
                  refine ⟨26097075058586123695598641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34796100078114831594131521 26097075058586123695598641)
                  ·
                    refine ⟨19572806293939592771698981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26097075058586123695598641 19572806293939592771698981)
                    ·
                      refine ⟨3669901180113673644693559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19572806293939592771698981 3669901180113673644693559)
                      ·
                        rfl

theorem cell23_7147107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_7147107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147107 prefixEnd_7147107 := by exact prefixLift 7147107
  have htrace : WordTrace (prefixWord ++ tailWord_7147107) baseStart_7147107 baseEnd_7147107 := by
    simpa [prefixWord, tailWord_7147107, baseEnd_7147107] using wordTrace_append hprefix tailTrace_7147107
  have hstable : (prefixWord ++ tailWord_7147107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147107).length < 2 ^ (prefixWord ++ tailWord_7147107).sum := by decide
  have hdescent : baseEnd_7147107 < baseStart_7147107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147147 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 2, 5]
def baseStart_7147147 : Nat := 118140960795 + 7147147 * 2 ^ 59
def prefixEnd_7147147 : Nat := 4983230072969 + 3 ^ 40 * 7147147 * 2
def baseEnd_7147147 : Nat := 1223307239779951162731125

theorem tailTrace_7147147 : CollatzResearch.WordTrace tailWord_7147147 prefixEnd_7147147 1223307239779951162731125 := by
  unfold tailWord_7147147
  simp only [CollatzResearch.WordTrace]
  refine ⟨260677866638114529372951695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173785244425409686248634463 260677866638114529372951695)
  ·
    refine ⟨391016799957171794059427543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260677866638114529372951695 391016799957171794059427543)
    ·
      refine ⟨586525199935757691089141315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391016799957171794059427543 586525199935757691089141315)
      ·
        refine ⟨879787799903636536633711973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586525199935757691089141315 879787799903636536633711973)
        ·
          refine ⟨164960212481931850618820995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 879787799903636536633711973 164960212481931850618820995)
          ·
            refine ⟨247440318722897775928231493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164960212481931850618820995 247440318722897775928231493)
            ·
              refine ⟨46395059760543332986543405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247440318722897775928231493 46395059760543332986543405)
              ·
                refine ⟨17398147410203749869953777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46395059760543332986543405 17398147410203749869953777)
                ·
                  refine ⟨13048610557652812402465333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17398147410203749869953777 13048610557652812402465333)
                  ·
                    refine ⟨1223307239779951162731125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13048610557652812402465333 1223307239779951162731125)
                    ·
                      rfl

theorem cell23_7147147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 5].length) (baseStart_7147147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147147 prefixEnd_7147147 := by exact prefixLift 7147147
  have htrace : WordTrace (prefixWord ++ tailWord_7147147) baseStart_7147147 baseEnd_7147147 := by
    simpa [prefixWord, tailWord_7147147, baseEnd_7147147] using wordTrace_append hprefix tailTrace_7147147
  have hstable : (prefixWord ++ tailWord_7147147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147147).length < 2 ^ (prefixWord ++ tailWord_7147147).sum := by decide
  have hdescent : baseEnd_7147147 < baseStart_7147147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147184 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 2, 4, 2]
def baseStart_7147184 : Nat := 118140960795 + 7147184 * 2 ^ 59
def prefixEnd_7147184 : Nat := 4983230072969 + 3 ^ 40 * 7147184 * 2
def baseEnd_7147184 : Nat := 3669940718124069843430705

theorem tailTrace_7147184 : CollatzResearch.WordTrace tailWord_7147184 prefixEnd_7147184 3669940718124069843430705 := by
  unfold tailWord_7147184
  simp only [CollatzResearch.WordTrace]
  refine ⟨130339608069490242346024303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173786144092653656461365737 130339608069490242346024303)
  ·
    refine ⟨195509412104235363519036455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130339608069490242346024303 195509412104235363519036455)
    ·
      refine ⟨293264118156353045278554683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195509412104235363519036455 293264118156353045278554683)
      ·
        refine ⟨439896177234529567917832025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293264118156353045278554683 439896177234529567917832025)
        ·
          refine ⟨329922132925897175938374019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439896177234529567917832025 329922132925897175938374019)
          ·
            refine ⟨494883199388845763907561029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329922132925897175938374019 494883199388845763907561029)
            ·
              refine ⟨92790599885408580732667693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494883199388845763907561029 92790599885408580732667693)
              ·
                refine ⟨34796474957028217774750385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92790599885408580732667693 34796474957028217774750385)
                ·
                  refine ⟨26097356217771163331062789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34796474957028217774750385 26097356217771163331062789)
                  ·
                    refine ⟨4893254290832093124574273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26097356217771163331062789 4893254290832093124574273)
                    ·
                      refine ⟨3669940718124069843430705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893254290832093124574273 3669940718124069843430705)
                      ·
                        rfl

theorem cell23_7147184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 4, 2].length) (baseStart_7147184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147184 prefixEnd_7147184 := by exact prefixLift 7147184
  have htrace : WordTrace (prefixWord ++ tailWord_7147184) baseStart_7147184 baseEnd_7147184 := by
    simpa [prefixWord, tailWord_7147184, baseEnd_7147184] using wordTrace_append hprefix tailTrace_7147184
  have hstable : (prefixWord ++ tailWord_7147184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147184).length < 2 ^ (prefixWord ++ tailWord_7147184).sum := by decide
  have hdescent : baseEnd_7147184 < baseStart_7147184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147224 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 6]
def baseStart_7147224 : Nat := 118140960795 + 7147224 * 2 ^ 59
def prefixEnd_7147224 : Nat := 4983230072969 + 3 ^ 40 * 7147224 * 2
def baseEnd_7147224 : Nat := 407773473038916631881169

theorem tailTrace_7147224 : CollatzResearch.WordTrace tailWord_7147224 prefixEnd_7147224 407773473038916631881169 := by
  unfold tailWord_7147224
  simp only [CollatzResearch.WordTrace]
  refine ⟨130340337529417785761752363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173787116705890381015669817 130340337529417785761752363)
  ·
    refine ⟨195510506294126678642628545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130340337529417785761752363 195510506294126678642628545)
    ·
      refine ⟨146632879720595008981971409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195510506294126678642628545 146632879720595008981971409)
      ·
        refine ⟨109974659790446256736478557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146632879720595008981971409 109974659790446256736478557)
        ·
          refine ⟨41240497421417346276179459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109974659790446256736478557 41240497421417346276179459)
          ·
            refine ⟨61860746132126019414269189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41240497421417346276179459 61860746132126019414269189)
            ·
              refine ⟨11598889899773628640175473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61860746132126019414269189 11598889899773628640175473)
              ·
                refine ⟨8699167424830221480131605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11598889899773628640175473 8699167424830221480131605)
                ·
                  refine ⟨407773473038916631881169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8699167424830221480131605 407773473038916631881169)
                  ·
                    rfl

theorem cell23_7147224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 6].length) (baseStart_7147224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147224 prefixEnd_7147224 := by exact prefixLift 7147224
  have htrace : WordTrace (prefixWord ++ tailWord_7147224) baseStart_7147224 baseEnd_7147224 := by
    simpa [prefixWord, tailWord_7147224, baseEnd_7147224] using wordTrace_append hprefix tailTrace_7147224
  have hstable : (prefixWord ++ tailWord_7147224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147224).length < 2 ^ (prefixWord ++ tailWord_7147224).sum := by decide
  have hdescent : baseEnd_7147224 < baseStart_7147224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147247 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_7147247 : Nat := 118140960795 + 7147247 * 2 ^ 59
def prefixEnd_7147247 : Nat := 4983230072969 + 3 ^ 40 * 7147247 * 2
def baseEnd_7147247 : Nat := 3669973067405303096942915

theorem tailTrace_7147247 : CollatzResearch.WordTrace tailWord_7147247 prefixEnd_7147247 3669973067405303096942915 := by
  unfold tailWord_7147247
  simp only [CollatzResearch.WordTrace]
  refine ⟨260681513937752246451591995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173787675958501497634394663 260681513937752246451591995)
  ·
    refine ⟨391022270906628369677387993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260681513937752246451591995 391022270906628369677387993)
    ·
      refine ⟨293266703179971277258040995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391022270906628369677387993 293266703179971277258040995)
      ·
        refine ⟨439900054769956915887061493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293266703179971277258040995 439900054769956915887061493)
        ·
          refine ⟨41240630134683460864412015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 439900054769956915887061493 41240630134683460864412015)
          ·
            refine ⟨61860945202025191296618023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41240630134683460864412015 61860945202025191296618023)
            ·
              refine ⟨92791417803037786944927035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61860945202025191296618023 92791417803037786944927035)
              ·
                refine ⟨139187126704556680417390553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92791417803037786944927035 139187126704556680417390553)
                ·
                  refine ⟨104390345028417510313042915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139187126704556680417390553 104390345028417510313042915)
                  ·
                    refine ⟨156585517542626265469564373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104390345028417510313042915 156585517542626265469564373)
                    ·
                      refine ⟨3669973067405303096942915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156585517542626265469564373 3669973067405303096942915)
                      ·
                        rfl

theorem cell23_7147247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_7147247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147247 prefixEnd_7147247 := by exact prefixLift 7147247
  have htrace : WordTrace (prefixWord ++ tailWord_7147247) baseStart_7147247 baseEnd_7147247 := by
    simpa [prefixWord, tailWord_7147247, baseEnd_7147247] using wordTrace_append hprefix tailTrace_7147247
  have hstable : (prefixWord ++ tailWord_7147247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147247).length < 2 ^ (prefixWord ++ tailWord_7147247).sum := by decide
  have hdescent : baseEnd_7147247 < baseStart_7147247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147261 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_7147261 : Nat := 118140960795 + 7147261 * 2 ^ 59
def prefixEnd_7147261 : Nat := 4983230072969 + 3 ^ 40 * 7147261 * 2
def baseEnd_7147261 : Nat := 3669980256134466042167851

theorem tailTrace_7147261 : CollatzResearch.WordTrace tailWord_7147261 prefixEnd_7147261 3669980256134466042167851 := by
  unfold tailWord_7147261
  simp only [CollatzResearch.WordTrace]
  refine ⟨260682024559701526842601637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173788016373134351228401091 260682024559701526842601637)
  ·
    refine ⟨48877879604944036282987807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260682024559701526842601637 48877879604944036282987807)
    ·
      refine ⟨73316819407416054424481711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48877879604944036282987807 73316819407416054424481711)
      ·
        refine ⟨109975229111124081636722567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73316819407416054424481711 109975229111124081636722567)
        ·
          refine ⟨164962843666686122455083851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109975229111124081636722567 164962843666686122455083851)
          ·
            refine ⟨247444265500029183682625777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164962843666686122455083851 247444265500029183682625777)
            ·
              refine ⟨185583199125021887761969333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247444265500029183682625777 185583199125021887761969333)
              ·
                refine ⟨17398424917970801977684625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185583199125021887761969333 17398424917970801977684625)
                ·
                  refine ⟨13048818688478101483263469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17398424917970801977684625 13048818688478101483263469)
                  ·
                    refine ⟨4893307008179288056223801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13048818688478101483263469 4893307008179288056223801)
                    ·
                      refine ⟨3669980256134466042167851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893307008179288056223801 3669980256134466042167851)
                      ·
                        rfl

theorem cell23_7147261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_7147261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147261 prefixEnd_7147261 := by exact prefixLift 7147261
  have htrace : WordTrace (prefixWord ++ tailWord_7147261) baseStart_7147261 baseEnd_7147261 := by
    simpa [prefixWord, tailWord_7147261, baseEnd_7147261] using wordTrace_append hprefix tailTrace_7147261
  have hstable : (prefixWord ++ tailWord_7147261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147261).length < 2 ^ (prefixWord ++ tailWord_7147261).sum := by decide
  have hdescent : baseEnd_7147261 < baseStart_7147261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147291 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 7, 2, 2]
def baseStart_7147291 : Nat := 118140960795 + 7147291 * 2 ^ 59
def prefixEnd_7147291 : Nat := 4983230072969 + 3 ^ 40 * 7147291 * 2
def baseEnd_7147291 : Nat := 3669995660554100924792713

theorem tailTrace_7147291 : CollatzResearch.WordTrace tailWord_7147291 prefixEnd_7147291 3669995660554100924792713 := by
  unfold tailWord_7147291
  simp only [CollatzResearch.WordTrace]
  refine ⟨260683118749592841966193727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173788745833061894644129151 260683118749592841966193727)
  ·
    refine ⟨391024678124389262949290591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260683118749592841966193727 391024678124389262949290591)
    ·
      refine ⟨586537017186583894423935887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391024678124389262949290591 586537017186583894423935887)
      ·
        refine ⟨879805525779875841635903831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586537017186583894423935887 879805525779875841635903831)
        ·
          refine ⟨1319708288669813762453855747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879805525779875841635903831 1319708288669813762453855747)
          ·
            refine ⟨1979562433004720643680783621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319708288669813762453855747 1979562433004720643680783621)
            ·
              refine ⟨371167956188385120690146929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1979562433004720643680783621 371167956188385120690146929)
              ·
                refine ⟨278375967141288840517610197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371167956188385120690146929 278375967141288840517610197)
                ·
                  refine ⟨6524436729873957199631489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 278375967141288840517610197 6524436729873957199631489)
                  ·
                    refine ⟨4893327547405467899723617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524436729873957199631489 4893327547405467899723617)
                    ·
                      refine ⟨3669995660554100924792713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893327547405467899723617 3669995660554100924792713)
                      ·
                        rfl

theorem cell23_7147291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 2, 2].length) (baseStart_7147291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147291 prefixEnd_7147291 := by exact prefixLift 7147291
  have htrace : WordTrace (prefixWord ++ tailWord_7147291) baseStart_7147291 baseEnd_7147291 := by
    simpa [prefixWord, tailWord_7147291, baseEnd_7147291] using wordTrace_append hprefix tailTrace_7147291
  have hstable : (prefixWord ++ tailWord_7147291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147291).length < 2 ^ (prefixWord ++ tailWord_7147291).sum := by decide
  have hdescent : baseEnd_7147291 < baseStart_7147291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147301 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_7147301 : Nat := 118140960795 + 7147301 * 2 ^ 59
def prefixEnd_7147301 : Nat := 4983230072969 + 3 ^ 40 * 7147301 * 2
def baseEnd_7147301 : Nat := 1223333598453548628555889

theorem tailTrace_7147301 : CollatzResearch.WordTrace tailWord_7147301 prefixEnd_7147301 1223333598453548628555889 := by
  unfold tailWord_7147301
  simp only [CollatzResearch.WordTrace]
  refine ⟨260683483479556613674057757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173788988986371075782705171 260683483479556613674057757)
  ·
    refine ⟨97756306304833730127771659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260683483479556613674057757 97756306304833730127771659)
    ·
      refine ⟨146634459457250595191657489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97756306304833730127771659 146634459457250595191657489)
      ·
        refine ⟨109975844592937946393743117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146634459457250595191657489 109975844592937946393743117)
        ·
          refine ⟨41240941722351729897653669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109975844592937946393743117 41240941722351729897653669)
          ·
            refine ⟨7732676572940949355810063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41240941722351729897653669 7732676572940949355810063)
            ·
              refine ⟨11599014859411424033715095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7732676572940949355810063 11599014859411424033715095)
              ·
                refine ⟨17398522289117136050572643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11599014859411424033715095 17398522289117136050572643)
                ·
                  refine ⟨26097783433675704075858965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17398522289117136050572643 26097783433675704075858965)
                  ·
                    refine ⟨1223333598453548628555889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26097783433675704075858965 1223333598453548628555889)
                    ·
                      rfl

theorem cell23_7147301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_7147301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147301 prefixEnd_7147301 := by exact prefixLift 7147301
  have htrace : WordTrace (prefixWord ++ tailWord_7147301) baseStart_7147301 baseEnd_7147301 := by
    simpa [prefixWord, tailWord_7147301, baseEnd_7147301] using wordTrace_append hprefix tailTrace_7147301
  have hstable : (prefixWord ++ tailWord_7147301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147301).length < 2 ^ (prefixWord ++ tailWord_7147301).sum := by decide
  have hdescent : baseEnd_7147301 < baseStart_7147301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147308 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 3, 2, 2]
def baseStart_7147308 : Nat := 118140960795 + 7147308 * 2 ^ 59
def prefixEnd_7147308 : Nat := 4983230072969 + 3 ^ 40 * 7147308 * 2
def baseEnd_7147308 : Nat := 3670004389725227358280135

theorem tailTrace_7147308 : CollatzResearch.WordTrace tailWord_7147308 prefixEnd_7147308 3670004389725227358280135 := by
  unfold tailWord_7147308
  simp only [CollatzResearch.WordTrace]
  refine ⟨130341869395265626934781289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173789159193687502579708385 130341869395265626934781289)
  ·
    refine ⟨97756402046449220201085967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130341869395265626934781289 97756402046449220201085967)
    ·
      refine ⟨146634603069673830301628951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97756402046449220201085967 146634603069673830301628951)
      ·
        refine ⟨219951904604510745452443427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146634603069673830301628951 219951904604510745452443427)
        ·
          refine ⟨329927856906766118178665141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219951904604510745452443427 329927856906766118178665141)
          ·
            refine ⟨30930736585009323579249857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 329927856906766118178665141 30930736585009323579249857)
            ·
              refine ⟨23198052438756992684437393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30930736585009323579249857 23198052438756992684437393)
              ·
                refine ⟨17398539329067744513328045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23198052438756992684437393 17398539329067744513328045)
                ·
                  refine ⟨6524452248400404192498017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17398539329067744513328045 6524452248400404192498017)
                  ·
                    refine ⟨4893339186300303144373513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524452248400404192498017 4893339186300303144373513)
                    ·
                      refine ⟨3670004389725227358280135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893339186300303144373513 3670004389725227358280135)
                      ·
                        rfl

theorem cell23_7147308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_7147308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147308 prefixEnd_7147308 := by exact prefixLift 7147308
  have htrace : WordTrace (prefixWord ++ tailWord_7147308) baseStart_7147308 baseEnd_7147308 := by
    simpa [prefixWord, tailWord_7147308, baseEnd_7147308] using wordTrace_append hprefix tailTrace_7147308
  have hstable : (prefixWord ++ tailWord_7147308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147308).length < 2 ^ (prefixWord ++ tailWord_7147308).sum := by decide
  have hdescent : baseEnd_7147308 < baseStart_7147308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147314 : List Nat := [3, 2, 1, 1, 3, 3, 1, 9]
def baseStart_7147314 : Nat := 118140960795 + 7147314 * 2 ^ 59
def prefixEnd_7147314 : Nat := 4983230072969 + 3 ^ 40 * 7147314 * 2
def baseEnd_7147314 : Nat := 135926202615153864252041

theorem tailTrace_7147314 : CollatzResearch.WordTrace tailWord_7147314 prefixEnd_7147314 135926202615153864252041 := by
  unfold tailWord_7147314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65170989407127379223570249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173789305085673011262853997 65170989407127379223570249)
  ·
    refine ⟨48878242055345534417677687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65170989407127379223570249 48878242055345534417677687)
    ·
      refine ⟨73317363083018301626516531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48878242055345534417677687 73317363083018301626516531)
      ·
        refine ⟨109976044624527452439774797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73317363083018301626516531 109976044624527452439774797)
        ·
          refine ⟨41241016734197794664915549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109976044624527452439774797 41241016734197794664915549)
          ·
            refine ⟨15465381275324172999343331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41241016734197794664915549 15465381275324172999343331)
            ·
              refine ⟨23198071912986259499014997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15465381275324172999343331 23198071912986259499014997)
              ·
                refine ⟨135926202615153864252041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23198071912986259499014997 135926202615153864252041)
                ·
                  rfl

theorem cell23_7147314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 9].length) (baseStart_7147314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147314 prefixEnd_7147314 := by exact prefixLift 7147314
  have htrace : WordTrace (prefixWord ++ tailWord_7147314) baseStart_7147314 baseEnd_7147314 := by
    simpa [prefixWord, tailWord_7147314, baseEnd_7147314] using wordTrace_append hprefix tailTrace_7147314
  have hstable : (prefixWord ++ tailWord_7147314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147314).length < 2 ^ (prefixWord ++ tailWord_7147314).sum := by decide
  have hdescent : baseEnd_7147314 < baseStart_7147314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147318 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_7147318 : Nat := 118140960795 + 7147318 * 2 ^ 59
def prefixEnd_7147318 : Nat := 4983230072969 + 3 ^ 40 * 7147318 * 2
def baseEnd_7147318 : Nat := 1223336508177257439718363

theorem tailTrace_7147318 : CollatzResearch.WordTrace tailWord_7147318 prefixEnd_7147318 1223336508177257439718363 := by
  unfold tailWord_7147318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292756470030939098589163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173789402346996683718284405 16292756470030939098589163)
  ·
    refine ⟨24439134705046408647883745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16292756470030939098589163 24439134705046408647883745)
    ·
      refine ⟨18329351028784806485912809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24439134705046408647883745 18329351028784806485912809)
      ·
        refine ⟨13747013271588604864434607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18329351028784806485912809 13747013271588604864434607)
        ·
          refine ⟨20620519907382907296651911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13747013271588604864434607 20620519907382907296651911)
          ·
            refine ⟨30930779861074360944977867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20620519907382907296651911 30930779861074360944977867)
            ·
              refine ⟨46396169791611541417466801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30930779861074360944977867 46396169791611541417466801)
              ·
                refine ⟨34797127343708656063100101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46396169791611541417466801 34797127343708656063100101)
                ·
                  refine ⟨6524461376945373011831269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34797127343708656063100101 6524461376945373011831269)
                  ·
                    refine ⟨1223336508177257439718363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6524461376945373011831269 1223336508177257439718363)
                    ·
                      rfl

theorem cell23_7147318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_7147318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147318 prefixEnd_7147318 := by exact prefixLift 7147318
  have htrace : WordTrace (prefixWord ++ tailWord_7147318) baseStart_7147318 baseEnd_7147318 := by
    simpa [prefixWord, tailWord_7147318, baseEnd_7147318] using wordTrace_append hprefix tailTrace_7147318
  have hstable : (prefixWord ++ tailWord_7147318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147318).length < 2 ^ (prefixWord ++ tailWord_7147318).sum := by decide
  have hdescent : baseEnd_7147318 < baseStart_7147318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147368 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7147368 : Nat := 118140960795 + 7147368 * 2 ^ 59
def prefixEnd_7147368 : Nat := 4983230072969 + 3 ^ 40 * 7147368 * 2
def baseEnd_7147368 : Nat := 3670035198564497123529859

theorem tailTrace_7147368 : CollatzResearch.WordTrace tailWord_7147368 prefixEnd_7147368 3670035198564497123529859 := by
  unfold tailWord_7147368
  simp only [CollatzResearch.WordTrace]
  refine ⟨130342963585156942058373379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173790618113542589411164505 130342963585156942058373379)
  ·
    refine ⟨195514445377735413087560069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130342963585156942058373379 195514445377735413087560069)
    ·
      refine ⟨36658958508325389953917513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195514445377735413087560069 36658958508325389953917513)
      ·
        refine ⟨27494218881244042465438135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36658958508325389953917513 27494218881244042465438135)
        ·
          refine ⟨41241328321866063698157203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27494218881244042465438135 41241328321866063698157203)
          ·
            refine ⟨61861992482799095547235805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41241328321866063698157203 61861992482799095547235805)
            ·
              refine ⟨23198247181049660830213427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61861992482799095547235805 23198247181049660830213427)
              ·
                refine ⟨34797370771574491245320141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23198247181049660830213427 34797370771574491245320141)
                ·
                  refine ⟨13049014039340434216995053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34797370771574491245320141 13049014039340434216995053)
                  ·
                    refine ⟨4893380264752662831373145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13049014039340434216995053 4893380264752662831373145)
                    ·
                      refine ⟨3670035198564497123529859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893380264752662831373145 3670035198564497123529859)
                      ·
                        rfl

theorem cell23_7147368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7147368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147368 prefixEnd_7147368 := by exact prefixLift 7147368
  have htrace : WordTrace (prefixWord ++ tailWord_7147368) baseStart_7147368 baseEnd_7147368 := by
    simpa [prefixWord, tailWord_7147368, baseEnd_7147368] using wordTrace_append hprefix tailTrace_7147368
  have hstable : (prefixWord ++ tailWord_7147368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147368).length < 2 ^ (prefixWord ++ tailWord_7147368).sum := by decide
  have hdescent : baseEnd_7147368 < baseStart_7147368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147385 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 1, 3, 2]
def baseStart_7147385 : Nat := 118140960795 + 7147385 * 2 ^ 59
def prefixEnd_7147385 : Nat := 4983230072969 + 3 ^ 40 * 7147385 * 2
def baseEnd_7147385 : Nat := 3670043927735623557017281

theorem tailTrace_7147385 : CollatzResearch.WordTrace tailWord_7147385 prefixEnd_7147385 3670043927735623557017281 := by
  unfold tailWord_7147385
  simp only [CollatzResearch.WordTrace]
  refine ⟨260686547211252296020115609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173791031474168197346743739 260686547211252296020115609)
  ·
    refine ⟨195514910408439222015086707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260686547211252296020115609 195514910408439222015086707)
    ·
      refine ⟨293272365612658833022630061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195514910408439222015086707 293272365612658833022630061)
      ·
        refine ⟨109977137104747062383486273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293272365612658833022630061 109977137104747062383486273)
        ·
          refine ⟨82482852828560296787614705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109977137104747062383486273 82482852828560296787614705)
          ·
            refine ⟨61862139621420222590711029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82482852828560296787614705 61862139621420222590711029)
            ·
              refine ⟨5799575589508145867879159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61862139621420222590711029 5799575589508145867879159)
              ·
                refine ⟨8699363384262218801818739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799575589508145867879159 8699363384262218801818739)
                ·
                  refine ⟨13049045076393328202728109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699363384262218801818739 13049045076393328202728109)
                  ·
                    refine ⟨4893391903647498076023041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13049045076393328202728109 4893391903647498076023041)
                    ·
                      refine ⟨3670043927735623557017281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893391903647498076023041 3670043927735623557017281)
                      ·
                        rfl

theorem cell23_7147385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_7147385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147385 prefixEnd_7147385 := by exact prefixLift 7147385
  have htrace : WordTrace (prefixWord ++ tailWord_7147385) baseStart_7147385 baseEnd_7147385 := by
    simpa [prefixWord, tailWord_7147385, baseEnd_7147385] using wordTrace_append hprefix tailTrace_7147385
  have hstable : (prefixWord ++ tailWord_7147385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147385).length < 2 ^ (prefixWord ++ tailWord_7147385).sum := by decide
  have hdescent : baseEnd_7147385 < baseStart_7147385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147393 : List Nat := [1, 2, 4, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7147393 : Nat := 118140960795 + 7147393 * 2 ^ 59
def prefixEnd_7147393 : Nat := 4983230072969 + 3 ^ 40 * 7147393 * 2
def baseEnd_7147393 : Nat := 3670048035580859525717245

theorem tailTrace_7147393 : CollatzResearch.WordTrace tailWord_7147393 prefixEnd_7147393 3670048035580859525717245 := by
  unfold tailWord_7147393
  simp only [CollatzResearch.WordTrace]
  refine ⟨260686838995223313386406833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173791225996815542257604555 260686838995223313386406833)
  ·
    refine ⟨195515129246417485039805125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260686838995223313386406833 195515129246417485039805125)
    ·
      refine ⟨36659086733703278444963461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195515129246417485039805125 36659086733703278444963461)
      ·
        refine ⟨6873578762569364708430649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36659086733703278444963461 6873578762569364708430649)
        ·
          refine ⟨5155184071927023531322987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6873578762569364708430649 5155184071927023531322987)
          ·
            refine ⟨7732776107890535296984481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155184071927023531322987 7732776107890535296984481)
            ·
              refine ⟨5799582080917901472738361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7732776107890535296984481 5799582080917901472738361)
              ·
                refine ⟨4349686560688426104553771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5799582080917901472738361 4349686560688426104553771)
                ·
                  refine ⟨6524529841032639156830657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349686560688426104553771 6524529841032639156830657)
                  ·
                    refine ⟨4893397380774479367622993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524529841032639156830657 4893397380774479367622993)
                    ·
                      refine ⟨3670048035580859525717245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893397380774479367622993 3670048035580859525717245)
                      ·
                        rfl

theorem cell23_7147393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7147393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147393 prefixEnd_7147393 := by exact prefixLift 7147393
  have htrace : WordTrace (prefixWord ++ tailWord_7147393) baseStart_7147393 baseEnd_7147393 := by
    simpa [prefixWord, tailWord_7147393, baseEnd_7147393] using wordTrace_append hprefix tailTrace_7147393
  have hstable : (prefixWord ++ tailWord_7147393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147393).length < 2 ^ (prefixWord ++ tailWord_7147393).sum := by decide
  have hdescent : baseEnd_7147393 < baseStart_7147393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147404 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 7]
def baseStart_7147404 : Nat := 118140960795 + 7147404 * 2 ^ 59
def prefixEnd_7147404 : Nat := 4983230072969 + 3 ^ 40 * 7147404 * 2
def baseEnd_7147404 : Nat := 407783742652006553631077

theorem tailTrace_7147404 : CollatzResearch.WordTrace tailWord_7147404 prefixEnd_7147404 407783742652006553631077 := by
  unfold tailWord_7147404
  simp only [CollatzResearch.WordTrace]
  refine ⟨130343620099091731132528633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173791493465455641510038177 130343620099091731132528633)
  ·
    refine ⟨97757715074318798349396475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130343620099091731132528633 97757715074318798349396475)
    ·
      refine ⟨146636572611478197524094713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97757715074318798349396475 146636572611478197524094713)
      ·
        refine ⟨109977429458608648143071035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146636572611478197524094713 109977429458608648143071035)
        ·
          refine ⟨164966144187912972214606553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109977429458608648143071035 164966144187912972214606553)
          ·
            refine ⟨123724608140934729160954915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164966144187912972214606553 123724608140934729160954915)
            ·
              refine ⟨185586912211402093741432373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123724608140934729160954915 185586912211402093741432373)
              ·
                refine ⟨17398773019818946288259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185586912211402093741432373 17398773019818946288259285)
                ·
                  refine ⟨407783742652006553631077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17398773019818946288259285 407783742652006553631077)
                  ·
                    rfl

theorem cell23_7147404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_7147404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147404 prefixEnd_7147404 := by exact prefixLift 7147404
  have htrace : WordTrace (prefixWord ++ tailWord_7147404) baseStart_7147404 baseEnd_7147404 := by
    simpa [prefixWord, tailWord_7147404, baseEnd_7147404] using wordTrace_append hprefix tailTrace_7147404
  have hstable : (prefixWord ++ tailWord_7147404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147404).length < 2 ^ (prefixWord ++ tailWord_7147404).sum := by decide
  have hdescent : baseEnd_7147404 < baseStart_7147404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147415 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 2, 2, 2]
def baseStart_7147415 : Nat := 118140960795 + 7147415 * 2 ^ 59
def prefixEnd_7147415 : Nat := 4983230072969 + 3 ^ 40 * 7147415 * 2
def baseEnd_7147415 : Nat := 3670059332155258439642143

theorem tailTrace_7147415 : CollatzResearch.WordTrace tailWord_7147415 prefixEnd_7147415 3670059332155258439642143 := by
  unfold tailWord_7147415
  simp only [CollatzResearch.WordTrace]
  refine ⟨260687641401143611143707699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173791760934095740762471799 260687641401143611143707699)
  ·
    refine ⟨391031462101715416715561549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260687641401143611143707699 391031462101715416715561549)
    ·
      refine ⟨146636798288143281268335581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391031462101715416715561549 146636798288143281268335581)
      ·
        refine ⟨54988799358053730475625843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146636798288143281268335581 54988799358053730475625843)
        ·
          refine ⟨82483199037080595713438765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54988799358053730475625843 82483199037080595713438765)
          ·
            refine ⟨30931199638905223392539537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82483199037080595713438765 30931199638905223392539537)
            ·
              refine ⟨23198399729178917544404653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30931199638905223392539537 23198399729178917544404653)
              ·
                refine ⟨8699399898442094079151745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23198399729178917544404653 8699399898442094079151745)
                ·
                  refine ⟨6524549923831570559363809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8699399898442094079151745 6524549923831570559363809)
                  ·
                    refine ⟨4893412442873677919522857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524549923831570559363809 4893412442873677919522857)
                    ·
                      refine ⟨3670059332155258439642143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893412442873677919522857 3670059332155258439642143)
                      ·
                        rfl

theorem cell23_7147415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_7147415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147415 prefixEnd_7147415 := by exact prefixLift 7147415
  have htrace : WordTrace (prefixWord ++ tailWord_7147415) baseStart_7147415 baseEnd_7147415 := by
    simpa [prefixWord, tailWord_7147415, baseEnd_7147415] using wordTrace_append hprefix tailTrace_7147415
  have hstable : (prefixWord ++ tailWord_7147415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147415).length < 2 ^ (prefixWord ++ tailWord_7147415).sum := by decide
  have hdescent : baseEnd_7147415 < baseStart_7147415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147421 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 7]
def baseStart_7147421 : Nat := 118140960795 + 7147421 * 2 ^ 59
def prefixEnd_7147421 : Nat := 4983230072969 + 3 ^ 40 * 7147421 * 2
def baseEnd_7147421 : Nat := 407784712559909490685235

theorem tailTrace_7147421 : CollatzResearch.WordTrace tailWord_7147421 prefixEnd_7147421 407784712559909490685235 := by
  unfold tailWord_7147421
  simp only [CollatzResearch.WordTrace]
  refine ⟨260687860239121874168426117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173791906826081249445617411 260687860239121874168426117)
  ·
    refine ⟨48878973794835351406579897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260687860239121874168426117 48878973794835351406579897)
    ·
      refine ⟨36659230346126513554934923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48878973794835351406579897 36659230346126513554934923)
      ·
        refine ⟨54988845519189770332402385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36659230346126513554934923 54988845519189770332402385)
        ·
          refine ⟨41241634139392327749301789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54988845519189770332402385 41241634139392327749301789)
          ·
            refine ⟨15465612802272122905988171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41241634139392327749301789 15465612802272122905988171)
            ·
              refine ⟨23198419203408184358982257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15465612802272122905988171 23198419203408184358982257)
              ·
                refine ⟨17398814402556138269236693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23198419203408184358982257 17398814402556138269236693)
                ·
                  refine ⟨407784712559909490685235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17398814402556138269236693 407784712559909490685235)
                  ·
                    rfl

theorem cell23_7147421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_7147421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147421 prefixEnd_7147421 := by exact prefixLift 7147421
  have htrace : WordTrace (prefixWord ++ tailWord_7147421) baseStart_7147421 baseEnd_7147421 := by
    simpa [prefixWord, tailWord_7147421, baseEnd_7147421] using wordTrace_append hprefix tailTrace_7147421
  have hstable : (prefixWord ++ tailWord_7147421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147421).length < 2 ^ (prefixWord ++ tailWord_7147421).sum := by decide
  have hdescent : baseEnd_7147421 < baseStart_7147421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147578 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2]
def baseStart_7147578 : Nat := 118140960795 + 7147578 * 2 ^ 59
def prefixEnd_7147578 : Nat := 4983230072969 + 3 ^ 40 * 7147578 * 2
def baseEnd_7147578 : Nat := 3670143029501941301903893

theorem tailTrace_7147578 : CollatzResearch.WordTrace tailWord_7147578 prefixEnd_7147578 3670143029501941301903893 := by
  unfold tailWord_7147578
  simp only [CollatzResearch.WordTrace]
  refine ⟨65173396624888272495472847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173795724333035393321260925 65173396624888272495472847)
  ·
    refine ⟨97760094937332408743209271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65173396624888272495472847 97760094937332408743209271)
    ·
      refine ⟨146640142405998613114813907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97760094937332408743209271 146640142405998613114813907)
      ·
        refine ⟨219960213608997919672220861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146640142405998613114813907 219960213608997919672220861)
        ·
          refine ⟨82485080103374219877082823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219960213608997919672220861 82485080103374219877082823)
          ·
            refine ⟨123727620155061329815624235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82485080103374219877082823 123727620155061329815624235)
            ·
              refine ⟨185591430232591994723436353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123727620155061329815624235 185591430232591994723436353)
              ·
                refine ⟨139193572674443996042577265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185591430232591994723436353 139193572674443996042577265)
                ·
                  refine ⟨104395179505832997031932949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139193572674443996042577265 104395179505832997031932949)
                  ·
                    refine ⟨4893524039335921735871857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104395179505832997031932949 4893524039335921735871857)
                    ·
                      refine ⟨3670143029501941301903893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893524039335921735871857 3670143029501941301903893)
                      ·
                        rfl

theorem cell23_7147578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_7147578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147578 prefixEnd_7147578 := by exact prefixLift 7147578
  have htrace : WordTrace (prefixWord ++ tailWord_7147578) baseStart_7147578 baseEnd_7147578 := by
    simpa [prefixWord, tailWord_7147578, baseEnd_7147578] using wordTrace_append hprefix tailTrace_7147578
  have hstable : (prefixWord ++ tailWord_7147578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147578).length < 2 ^ (prefixWord ++ tailWord_7147578).sum := by decide
  have hdescent : baseEnd_7147578 < baseStart_7147578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147595 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 3, 2, 2]
def baseStart_7147595 : Nat := 118140960795 + 7147595 * 2 ^ 59
def prefixEnd_7147595 : Nat := 4983230072969 + 3 ^ 40 * 7147595 * 2
def baseEnd_7147595 : Nat := 3670151758673067735391315

theorem tailTrace_7147595 : CollatzResearch.WordTrace tailWord_7147595 prefixEnd_7147595 3670151758673067735391315 := by
  unfold tailWord_7147595
  simp only [CollatzResearch.WordTrace]
  refine ⟨260694206540491501885260239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173796137693661001256840159 260694206540491501885260239)
  ·
    refine ⟨391041309810737252827890359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260694206540491501885260239 391041309810737252827890359)
    ·
      refine ⟨586561964716105879241835539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391041309810737252827890359 586561964716105879241835539)
      ·
        refine ⟨879842947074158818862753309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586561964716105879241835539 879842947074158818862753309)
        ·
          refine ⟨329941105152809557073532491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879842947074158818862753309 329941105152809557073532491)
          ·
            refine ⟨494911657729214335610298737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329941105152809557073532491 494911657729214335610298737)
            ·
              refine ⟨371183743296910751707724053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494911657729214335610298737 371183743296910751707724053)
              ·
                refine ⟨17399237967042691486299565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 371183743296910751707724053 17399237967042691486299565)
                ·
                  refine ⟨6524714237641009307362337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17399237967042691486299565 6524714237641009307362337)
                  ·
                    refine ⟨4893535678230756980521753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524714237641009307362337 4893535678230756980521753)
                    ·
                      refine ⟨3670151758673067735391315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893535678230756980521753 3670151758673067735391315)
                      ·
                        rfl

theorem cell23_7147595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 2, 2].length) (baseStart_7147595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147595 prefixEnd_7147595 := by exact prefixLift 7147595
  have htrace : WordTrace (prefixWord ++ tailWord_7147595) baseStart_7147595 baseEnd_7147595 := by
    simpa [prefixWord, tailWord_7147595, baseEnd_7147595] using wordTrace_append hprefix tailTrace_7147595
  have hstable : (prefixWord ++ tailWord_7147595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147595).length < 2 ^ (prefixWord ++ tailWord_7147595).sum := by decide
  have hdescent : baseEnd_7147595 < baseStart_7147595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147606 : List Nat := [5, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7147606 : Nat := 118140960795 + 7147606 * 2 ^ 59
def prefixEnd_7147606 : Nat := 4983230072969 + 3 ^ 40 * 7147606 * 2
def baseEnd_7147606 : Nat := 3670157406960267192353765

theorem tailTrace_7147606 : CollatzResearch.WordTrace tailWord_7147606 prefixEnd_7147606 3670157406960267192353765 := by
  unfold tailWord_7147606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16293412983965728172744417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173796405162301100509273781 16293412983965728172744417)
  ·
    refine ⟨12220059737974296129558313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16293412983965728172744417 12220059737974296129558313)
    ·
      refine ⟨9165044803480722097168735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12220059737974296129558313 9165044803480722097168735)
      ·
        refine ⟨13747567205221083145753103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9165044803480722097168735 13747567205221083145753103)
        ·
          refine ⟨20621350807831624718629655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13747567205221083145753103 20621350807831624718629655)
          ·
            refine ⟨30932026211747437077944483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20621350807831624718629655 30932026211747437077944483)
            ·
              refine ⟨46398039317621155616916725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30932026211747437077944483 46398039317621155616916725)
              ·
                refine ⟨4349816186026983339085943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46398039317621155616916725 4349816186026983339085943)
                ·
                  refine ⟨6524724279040475008628915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349816186026983339085943 6524724279040475008628915)
                  ·
                    refine ⟨9787086418560712512943373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6524724279040475008628915 9787086418560712512943373)
                    ·
                      refine ⟨3670157406960267192353765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787086418560712512943373 3670157406960267192353765)
                      ·
                        rfl

theorem cell23_7147606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7147606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147606 prefixEnd_7147606 := by exact prefixLift 7147606
  have htrace : WordTrace (prefixWord ++ tailWord_7147606) baseStart_7147606 baseEnd_7147606 := by
    simpa [prefixWord, tailWord_7147606, baseEnd_7147606] using wordTrace_append hprefix tailTrace_7147606
  have hstable : (prefixWord ++ tailWord_7147606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147606).length < 2 ^ (prefixWord ++ tailWord_7147606).sum := by decide
  have hdescent : baseEnd_7147606 < baseStart_7147606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147608 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7147608 : Nat := 118140960795 + 7147608 * 2 ^ 59
def prefixEnd_7147608 : Nat := 4983230072969 + 3 ^ 40 * 7147608 * 2
def baseEnd_7147608 : Nat := 3670158433921576184528755

theorem tailTrace_7147608 : CollatzResearch.WordTrace tailWord_7147608 prefixEnd_7147608 3670158433921576184528755 := by
  unfold tailWord_7147608
  simp only [CollatzResearch.WordTrace]
  refine ⟨130347340344722202552741739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173796453792962936736988985 130347340344722202552741739)
  ·
    refine ⟨195521010517083303829112609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130347340344722202552741739 195521010517083303829112609)
    ·
      refine ⟨146640757887812477871834457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195521010517083303829112609 146640757887812477871834457)
      ·
        refine ⟨109980568415859358403875843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146640757887812477871834457 109980568415859358403875843)
        ·
          refine ⟨164970852623789037605813765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109980568415859358403875843 164970852623789037605813765)
          ·
            refine ⟨30932034866960444551090081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164970852623789037605813765 30932034866960444551090081)
            ·
              refine ⟨23199026150220333413317561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30932034866960444551090081 23199026150220333413317561)
              ·
                refine ⟨17399269612665250059988171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23199026150220333413317561 17399269612665250059988171)
                ·
                  refine ⟨26098904418997875089982257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17399269612665250059988171 26098904418997875089982257)
                  ·
                    refine ⟨19574178314248406317486693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26098904418997875089982257 19574178314248406317486693)
                    ·
                      refine ⟨3670158433921576184528755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19574178314248406317486693 3670158433921576184528755)
                      ·
                        rfl

theorem cell23_7147608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7147608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147608 prefixEnd_7147608 := by exact prefixLift 7147608
  have htrace : WordTrace (prefixWord ++ tailWord_7147608) baseStart_7147608 baseEnd_7147608 := by
    simpa [prefixWord, tailWord_7147608, baseEnd_7147608] using wordTrace_append hprefix tailTrace_7147608
  have hstable : (prefixWord ++ tailWord_7147608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147608).length < 2 ^ (prefixWord ++ tailWord_7147608).sum := by decide
  have hdescent : baseEnd_7147608 < baseStart_7147608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147612 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_7147612 : Nat := 118140960795 + 7147612 * 2 ^ 59
def prefixEnd_7147612 : Nat := 4983230072969 + 3 ^ 40 * 7147612 * 2
def baseEnd_7147612 : Nat := 3670160487844194168878737

theorem tailTrace_7147612 : CollatzResearch.WordTrace tailWord_7147612 prefixEnd_7147612 3670160487844194168878737 := by
  unfold tailWord_7147612
  simp only [CollatzResearch.WordTrace]
  refine ⟨130347413290714956894314545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173796551054286609192419393 130347413290714956894314545)
  ·
    refine ⟨97760559968036217670735909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130347413290714956894314545 97760559968036217670735909)
    ·
      refine ⟨18330104994006790813262983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97760559968036217670735909 18330104994006790813262983)
      ·
        refine ⟨27495157491010186219894475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18330104994006790813262983 27495157491010186219894475)
        ·
          refine ⟨41242736236515279329841713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27495157491010186219894475 41242736236515279329841713)
          ·
            refine ⟨30932052177386459497381285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41242736236515279329841713 30932052177386459497381285)
            ·
              refine ⟨5799759783259961155758991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30932052177386459497381285 5799759783259961155758991)
              ·
                refine ⟨8699639674889941733638487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799759783259961155758991 8699639674889941733638487)
                ·
                  refine ⟨13049459512334912600457731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699639674889941733638487 13049459512334912600457731)
                  ·
                    refine ⟨19574189268502368900686597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13049459512334912600457731 19574189268502368900686597)
                    ·
                      refine ⟨3670160487844194168878737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19574189268502368900686597 3670160487844194168878737)
                      ·
                        rfl

theorem cell23_7147612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_7147612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147612 prefixEnd_7147612 := by exact prefixLift 7147612
  have htrace : WordTrace (prefixWord ++ tailWord_7147612) baseStart_7147612 baseEnd_7147612 := by
    simpa [prefixWord, tailWord_7147612, baseEnd_7147612] using wordTrace_append hprefix tailTrace_7147612
  have hstable : (prefixWord ++ tailWord_7147612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147612).length < 2 ^ (prefixWord ++ tailWord_7147612).sum := by decide
  have hdescent : baseEnd_7147612 < baseStart_7147612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147629 : List Nat := [1, 5, 1, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_7147629 : Nat := 118140960795 + 7147629 * 2 ^ 59
def prefixEnd_7147629 : Nat := 4983230072969 + 3 ^ 40 * 7147629 * 2
def baseEnd_7147629 : Nat := 3670169217015320602366159

theorem tailTrace_7147629 : CollatzResearch.WordTrace tailWord_7147629 prefixEnd_7147629 3670169217015320602366159 := by
  unfold tailWord_7147629
  simp only [CollatzResearch.WordTrace]
  refine ⟨260695446622368325691997941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173796964414912217127998627 260695446622368325691997941)
  ·
    refine ⟨24440198120847030533624807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260695446622368325691997941 24440198120847030533624807)
    ·
      refine ⟨36660297181270545800437211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24440198120847030533624807 36660297181270545800437211)
      ·
        refine ⟨54990445771905818700655817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36660297181270545800437211 54990445771905818700655817)
        ·
          refine ⟨41242834328929364025491863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54990445771905818700655817 41242834328929364025491863)
          ·
            refine ⟨61864251493394046038237795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41242834328929364025491863 61864251493394046038237795)
            ·
              refine ⟨92796377240091069057356693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61864251493394046038237795 92796377240091069057356693)
              ·
                refine ⟨4349830183129268862063595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92796377240091069057356693 4349830183129268862063595)
                ·
                  refine ⟨6524745274693903293095393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349830183129268862063595 6524745274693903293095393)
                  ·
                    refine ⟨4893558956020427469821545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6524745274693903293095393 4893558956020427469821545)
                    ·
                      refine ⟨3670169217015320602366159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893558956020427469821545 3670169217015320602366159)
                      ·
                        rfl

theorem cell23_7147629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_7147629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147629 prefixEnd_7147629 := by exact prefixLift 7147629
  have htrace : WordTrace (prefixWord ++ tailWord_7147629) baseStart_7147629 baseEnd_7147629 := by
    simpa [prefixWord, tailWord_7147629, baseEnd_7147629] using wordTrace_append hprefix tailTrace_7147629
  have hstable : (prefixWord ++ tailWord_7147629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147629).length < 2 ^ (prefixWord ++ tailWord_7147629).sum := by decide
  have hdescent : baseEnd_7147629 < baseStart_7147629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147645 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_7147645 : Nat := 118140960795 + 7147645 * 2 ^ 59
def prefixEnd_7147645 : Nat := 4983230072969 + 3 ^ 40 * 7147645 * 2
def baseEnd_7147645 : Nat := 3670177432705792539766085

theorem tailTrace_7147645 : CollatzResearch.WordTrace tailWord_7147645 prefixEnd_7147645 3670177432705792539766085 := by
  unfold tailWord_7147645
  simp only [CollatzResearch.WordTrace]
  refine ⟨260696030190310360424580389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173797353460206906949720259 260696030190310360424580389)
  ·
    refine ⟨48880505660683192579608823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260696030190310360424580389 48880505660683192579608823)
    ·
      refine ⟨73320758491024788869413235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48880505660683192579608823 73320758491024788869413235)
      ·
        refine ⟨109981137736537183304119853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73320758491024788869413235 109981137736537183304119853)
        ·
          refine ⟨41242926651201443739044945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109981137736537183304119853 41242926651201443739044945)
          ·
            refine ⟨30932194988401082804283709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41242926651201443739044945 30932194988401082804283709)
            ·
              refine ⟨11599573120650406051606391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30932194988401082804283709 11599573120650406051606391)
              ·
                refine ⟨17399359680975609077409587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11599573120650406051606391 17399359680975609077409587)
                ·
                  refine ⟨26099039521463413616114381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17399359680975609077409587 26099039521463413616114381)
                  ·
                    refine ⟨9787139820548780106042893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26099039521463413616114381 9787139820548780106042893)
                    ·
                      refine ⟨3670177432705792539766085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787139820548780106042893 3670177432705792539766085)
                      ·
                        rfl

theorem cell23_7147645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_7147645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147645 prefixEnd_7147645 := by exact prefixLift 7147645
  have htrace : WordTrace (prefixWord ++ tailWord_7147645) baseStart_7147645 baseEnd_7147645 := by
    simpa [prefixWord, tailWord_7147645, baseEnd_7147645] using wordTrace_append hprefix tailTrace_7147645
  have hstable : (prefixWord ++ tailWord_7147645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147645).length < 2 ^ (prefixWord ++ tailWord_7147645).sum := by decide
  have hdescent : baseEnd_7147645 < baseStart_7147645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147655 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_7147655 : Nat := 118140960795 + 7147655 * 2 ^ 59
def prefixEnd_7147655 : Nat := 4983230072969 + 3 ^ 40 * 7147655 * 2
def baseEnd_7147655 : Nat := 3670182567512337500641039

theorem tailTrace_7147655 : CollatzResearch.WordTrace tailWord_7147655 prefixEnd_7147655 3670182567512337500641039 := by
  unfold tailWord_7147655
  simp only [CollatzResearch.WordTrace]
  refine ⟨260696394920274132132444419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173797596613516088088296279 260696394920274132132444419)
  ·
    refine ⟨391044592380411198198666629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260696394920274132132444419 391044592380411198198666629)
    ·
      refine ⟨73320861071327099662249993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391044592380411198198666629 73320861071327099662249993)
      ·
        refine ⟨54990645803495324746687495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73320861071327099662249993 54990645803495324746687495)
        ·
          refine ⟨82485968705242987120031243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54990645803495324746687495 82485968705242987120031243)
          ·
            refine ⟨123728953057864480680046865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82485968705242987120031243 123728953057864480680046865)
            ·
              refine ⟨92796714793398360510035149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123728953057864480680046865 92796714793398360510035149)
              ·
                refine ⟨34798768047524385191263181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92796714793398360510035149 34798768047524385191263181)
                ·
                  refine ⟨13049538017821644446723693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34798768047524385191263181 13049538017821644446723693)
                  ·
                    refine ⟨4893576756683116667521385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13049538017821644446723693 4893576756683116667521385)
                    ·
                      refine ⟨3670182567512337500641039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893576756683116667521385 3670182567512337500641039)
                      ·
                        rfl

theorem cell23_7147655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_7147655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147655 prefixEnd_7147655 := by exact prefixLift 7147655
  have htrace : WordTrace (prefixWord ++ tailWord_7147655) baseStart_7147655 baseEnd_7147655 := by
    simpa [prefixWord, tailWord_7147655, baseEnd_7147655] using wordTrace_append hprefix tailTrace_7147655
  have hstable : (prefixWord ++ tailWord_7147655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147655).length < 2 ^ (prefixWord ++ tailWord_7147655).sum := by decide
  have hdescent : baseEnd_7147655 < baseStart_7147655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147658 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_7147658 : Nat := 118140960795 + 7147658 * 2 ^ 59
def prefixEnd_7147658 : Nat := 4983230072969 + 3 ^ 40 * 7147658 * 2
def baseEnd_7147658 : Nat := 3670184107954300988903525

theorem tailTrace_7147658 : CollatzResearch.WordTrace tailWord_7147658 prefixEnd_7147658 3670184107954300988903525 := by
  unfold tailWord_7147658
  simp only [CollatzResearch.WordTrace]
  refine ⟨65174126084815815911200907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173797669559508842429869085 65174126084815815911200907)
  ·
    refine ⟨97761189127223723866801361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65174126084815815911200907 97761189127223723866801361)
    ·
      refine ⟨73320891845417792900101021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97761189127223723866801361 73320891845417792900101021)
      ·
        refine ⟨27495334442031672337537883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73320891845417792900101021 27495334442031672337537883)
        ·
          refine ⟨41243001663047508506306825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27495334442031672337537883 41243001663047508506306825)
          ·
            refine ⟨30932251247285631379730119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41243001663047508506306825 30932251247285631379730119)
            ·
              refine ⟨46398376870928447069595179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30932251247285631379730119 46398376870928447069595179)
              ·
                refine ⟨69597565306392670604392769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46398376870928447069595179 69597565306392670604392769)
                ·
                  refine ⟨52198173979794502953294577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69597565306392670604392769 52198173979794502953294577)
                  ·
                    refine ⟨39148630484845877214970933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52198173979794502953294577 39148630484845877214970933)
                    ·
                      refine ⟨3670184107954300988903525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39148630484845877214970933 3670184107954300988903525)
                      ·
                        rfl

theorem cell23_7147658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_7147658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147658 prefixEnd_7147658 := by exact prefixLift 7147658
  have htrace : WordTrace (prefixWord ++ tailWord_7147658) baseStart_7147658 baseEnd_7147658 := by
    simpa [prefixWord, tailWord_7147658, baseEnd_7147658] using wordTrace_append hprefix tailTrace_7147658
  have hstable : (prefixWord ++ tailWord_7147658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147658).length < 2 ^ (prefixWord ++ tailWord_7147658).sum := by decide
  have hdescent : baseEnd_7147658 < baseStart_7147658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147698 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_7147698 : Nat := 118140960795 + 7147698 * 2 ^ 59
def prefixEnd_7147698 : Nat := 4983230072969 + 3 ^ 40 * 7147698 * 2
def baseEnd_7147698 : Nat := 3670204647180480832403341

theorem tailTrace_7147698 : CollatzResearch.WordTrace tailWord_7147698 prefixEnd_7147698 3670204647180480832403341 := by
  unfold tailWord_7147698
  simp only [CollatzResearch.WordTrace]
  refine ⟨65174490814779587619064937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173798642172745566984173165 65174490814779587619064937)
  ·
    refine ⟨48880868111084690714298703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65174490814779587619064937 48880868111084690714298703)
    ·
      refine ⟨73321302166627036071448055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48880868111084690714298703 73321302166627036071448055)
      ·
        refine ⟨109981953249940554107172083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73321302166627036071448055 109981953249940554107172083)
        ·
          refine ⟨164972929874910831160758125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109981953249940554107172083 164972929874910831160758125)
          ·
            refine ⟨61864848703091561685284297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164972929874910831160758125 61864848703091561685284297)
            ·
              refine ⟨46398636527318671263963223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61864848703091561685284297 46398636527318671263963223)
              ·
                refine ⟨69597954790978006895944835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46398636527318671263963223 69597954790978006895944835)
                ·
                  refine ⟨104396932186467010343917253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69597954790978006895944835 104396932186467010343917253)
                  ·
                    refine ⟨19574424784962564439484485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104396932186467010343917253 19574424784962564439484485)
                    ·
                      refine ⟨3670204647180480832403341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19574424784962564439484485 3670204647180480832403341)
                      ·
                        rfl

theorem cell23_7147698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_7147698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147698 prefixEnd_7147698 := by exact prefixLift 7147698
  have htrace : WordTrace (prefixWord ++ tailWord_7147698) baseStart_7147698 baseEnd_7147698 := by
    simpa [prefixWord, tailWord_7147698, baseEnd_7147698] using wordTrace_append hprefix tailTrace_7147698
  have hstable : (prefixWord ++ tailWord_7147698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147698).length < 2 ^ (prefixWord ++ tailWord_7147698).sum := by decide
  have hdescent : baseEnd_7147698 < baseStart_7147698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147700 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7147700 : Nat := 118140960795 + 7147700 * 2 ^ 59
def prefixEnd_7147700 : Nat := 4983230072969 + 3 ^ 40 * 7147700 * 2
def baseEnd_7147700 : Nat := 3670205674141789824578333

theorem tailTrace_7147700 : CollatzResearch.WordTrace tailWord_7147700 prefixEnd_7147700 3670205674141789824578333 := by
  unfold tailWord_7147700
  simp only [CollatzResearch.WordTrace]
  refine ⟨130349018102555552408916277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173798690803407403211888369 130349018102555552408916277)
  ·
    refine ⟨12220220447114583038335901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130349018102555552408916277 12220220447114583038335901)
    ·
      refine ⟨4582582667667968639375963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12220220447114583038335901 4582582667667968639375963)
      ·
        refine ⟨6873874001501952959063945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582582667667968639375963 6873874001501952959063945)
        ·
          refine ⟨5155405501126464719297959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6873874001501952959063945 5155405501126464719297959)
          ·
            refine ⟨7733108251689697078946939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155405501126464719297959 7733108251689697078946939)
            ·
              refine ⟨11599662377534545618420409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733108251689697078946939 11599662377534545618420409)
              ·
                refine ⟨8699746783150909213815307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11599662377534545618420409 8699746783150909213815307)
                ·
                  refine ⟨13049620174726363820722961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699746783150909213815307 13049620174726363820722961)
                  ·
                    refine ⟨9787215131044772865542221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13049620174726363820722961 9787215131044772865542221)
                    ·
                      refine ⟨3670205674141789824578333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787215131044772865542221 3670205674141789824578333)
                      ·
                        rfl

theorem cell23_7147700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7147700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147700 prefixEnd_7147700 := by exact prefixLift 7147700
  have htrace : WordTrace (prefixWord ++ tailWord_7147700) baseStart_7147700 baseEnd_7147700 := by
    simpa [prefixWord, tailWord_7147700, baseEnd_7147700] using wordTrace_append hprefix tailTrace_7147700
  have hstable : (prefixWord ++ tailWord_7147700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147700).length < 2 ^ (prefixWord ++ tailWord_7147700).sum := by decide
  have hdescent : baseEnd_7147700 < baseStart_7147700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147745 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_7147745 : Nat := 118140960795 + 7147745 * 2 ^ 59
def prefixEnd_7147745 : Nat := 4983230072969 + 3 ^ 40 * 7147745 * 2
def baseEnd_7147745 : Nat := 3670228780771242148515625

theorem tailTrace_7147745 : CollatzResearch.WordTrace tailWord_7147745 prefixEnd_7147745 3670228780771242148515625 := by
  unfold tailWord_7147745
  simp only [CollatzResearch.WordTrace]
  refine ⟨260699677489948077503220689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173799784993298718335480459 260699677489948077503220689)
  ·
    refine ⟨195524758117461058127415517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260699677489948077503220689 195524758117461058127415517)
    ·
      refine ⟨73321784294047896797780819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195524758117461058127415517 73321784294047896797780819)
      ·
        refine ⟨109982676441071845196671229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73321784294047896797780819 109982676441071845196671229)
        ·
          refine ⟨41243503665401941948751711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109982676441071845196671229 41243503665401941948751711)
          ·
            refine ⟨61865255498102912923127567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41243503665401941948751711 61865255498102912923127567)
            ·
              refine ⟨92797883247154369384691351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61865255498102912923127567 92797883247154369384691351)
              ·
                refine ⟨139196824870731554077037027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92797883247154369384691351 139196824870731554077037027)
                ·
                  refine ⟨208795237306097331115555541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139196824870731554077037027 208795237306097331115555541)
                  ·
                    refine ⟨4893638374361656198020833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 208795237306097331115555541 4893638374361656198020833)
                    ·
                      refine ⟨3670228780771242148515625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893638374361656198020833 3670228780771242148515625)
                      ·
                        rfl

theorem cell23_7147745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_7147745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147745 prefixEnd_7147745 := by exact prefixLift 7147745
  have htrace : WordTrace (prefixWord ++ tailWord_7147745) baseStart_7147745 baseEnd_7147745 := by
    simpa [prefixWord, tailWord_7147745, baseEnd_7147745] using wordTrace_append hprefix tailTrace_7147745
  have hstable : (prefixWord ++ tailWord_7147745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147745).length < 2 ^ (prefixWord ++ tailWord_7147745).sum := by decide
  have hdescent : baseEnd_7147745 < baseStart_7147745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147772 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_7147772 : Nat := 118140960795 + 7147772 * 2 ^ 59
def prefixEnd_7147772 : Nat := 4983230072969 + 3 ^ 40 * 7147772 * 2
def baseEnd_7147772 : Nat := 1223414214916304514292667

theorem tailTrace_7147772 : CollatzResearch.WordTrace tailWord_7147772 prefixEnd_7147772 1223414214916304514292667 := by
  unfold tailWord_7147772
  simp only [CollatzResearch.WordTrace]
  refine ⟨130350331130425130557226785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173800441507233507409635713 130350331130425130557226785)
  ·
    refine ⟨97762748347818847917920089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130350331130425130557226785 97762748347818847917920089)
    ·
      refine ⟨73322061260864135938440067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97762748347818847917920089 73322061260864135938440067)
      ·
        refine ⟨109983091891296203907660101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73322061260864135938440067 109983091891296203907660101)
        ·
          refine ⟨20621829729618038232686269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109983091891296203907660101 20621829729618038232686269)
          ·
            refine ⟨7733186148606764337257351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20621829729618038232686269 7733186148606764337257351)
            ·
              refine ⟨11599779222910146505886027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733186148606764337257351 11599779222910146505886027)
              ·
                refine ⟨17399668834365219758829041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11599779222910146505886027 17399668834365219758829041)
                ·
                  refine ⟨13049751625773914819121781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17399668834365219758829041 13049751625773914819121781)
                  ·
                    refine ⟨1223414214916304514292667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13049751625773914819121781 1223414214916304514292667)
                    ·
                      rfl

theorem cell23_7147772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_7147772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147772 prefixEnd_7147772 := by exact prefixLift 7147772
  have htrace : WordTrace (prefixWord ++ tailWord_7147772) baseStart_7147772 baseEnd_7147772 := by
    simpa [prefixWord, tailWord_7147772, baseEnd_7147772] using wordTrace_append hprefix tailTrace_7147772
  have hstable : (prefixWord ++ tailWord_7147772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147772).length < 2 ^ (prefixWord ++ tailWord_7147772).sum := by decide
  have hdescent : baseEnd_7147772 < baseStart_7147772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147775 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 1, 6, 2]
def baseStart_7147775 : Nat := 118140960795 + 7147775 * 2 ^ 59
def prefixEnd_7147775 : Nat := 4983230072969 + 3 ^ 40 * 7147775 * 2
def baseEnd_7147775 : Nat := 3670244185190877031140487

theorem tailTrace_7147775 : CollatzResearch.WordTrace tailWord_7147775 prefixEnd_7147775 3670244185190877031140487 := by
  unfold tailWord_7147775
  simp only [CollatzResearch.WordTrace]
  refine ⟨260700771679839392626812779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173800514453226261751208519 260700771679839392626812779)
  ·
    refine ⟨391051157519759088940219169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260700771679839392626812779 391051157519759088940219169)
    ·
      refine ⟨293288368139819316705164377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391051157519759088940219169 293288368139819316705164377)
      ·
        refine ⟨219966276104864487528873283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293288368139819316705164377 219966276104864487528873283)
        ·
          refine ⟨329949414157296731293309925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219966276104864487528873283 329949414157296731293309925)
          ·
            refine ⟨61865515154493137117495611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329949414157296731293309925 61865515154493137117495611)
            ·
              refine ⟨92798272731739705676243417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61865515154493137117495611 92798272731739705676243417)
              ·
                refine ⟨69598704548804779257182563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92798272731739705676243417 69598704548804779257182563)
                ·
                  refine ⟨104398056823207168885773845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69598704548804779257182563 104398056823207168885773845)
                  ·
                    refine ⟨4893658913587836041520649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104398056823207168885773845 4893658913587836041520649)
                    ·
                      refine ⟨3670244185190877031140487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893658913587836041520649 3670244185190877031140487)
                      ·
                        rfl

theorem cell23_7147775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_7147775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147775 prefixEnd_7147775 := by exact prefixLift 7147775
  have htrace : WordTrace (prefixWord ++ tailWord_7147775) baseStart_7147775 baseEnd_7147775 := by
    simpa [prefixWord, tailWord_7147775, baseEnd_7147775] using wordTrace_append hprefix tailTrace_7147775
  have hstable : (prefixWord ++ tailWord_7147775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147775).length < 2 ^ (prefixWord ++ tailWord_7147775).sum := by decide
  have hdescent : baseEnd_7147775 < baseStart_7147775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147788 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7147788 : Nat := 118140960795 + 7147788 * 2 ^ 59
def prefixEnd_7147788 : Nat := 4983230072969 + 3 ^ 40 * 7147788 * 2
def baseEnd_7147788 : Nat := 3670250860439385480277927

theorem tailTrace_7147788 : CollatzResearch.WordTrace tailWord_7147788 prefixEnd_7147788 3670250860439385480277927 := by
  unfold tailWord_7147788
  simp only [CollatzResearch.WordTrace]
  refine ⟨130350622914396147923518009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173800830552528197231357345 130350622914396147923518009)
  ·
    refine ⟨97762967185797110942638507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130350622914396147923518009 97762967185797110942638507)
    ·
      refine ⟨146644450778695666413957761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97762967185797110942638507 146644450778695666413957761)
      ·
        refine ⟨109983338084021749810468321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146644450778695666413957761 109983338084021749810468321)
        ·
          refine ⟨82487503563016312357851241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109983338084021749810468321 82487503563016312357851241)
          ·
            refine ⟨61865627672262234268388431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82487503563016312357851241 61865627672262234268388431)
            ·
              refine ⟨92798441508393351402582647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61865627672262234268388431 92798441508393351402582647)
              ·
                refine ⟨139197662262590027103873971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92798441508393351402582647 139197662262590027103873971)
                ·
                  refine ⟨208796493393885040655810957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139197662262590027103873971 208796493393885040655810957)
                  ·
                    refine ⟨78298685022706890245929109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208796493393885040655810957 78298685022706890245929109)
                    ·
                      refine ⟨3670250860439385480277927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78298685022706890245929109 3670250860439385480277927)
                      ·
                        rfl

theorem cell23_7147788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7147788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147788 prefixEnd_7147788 := by exact prefixLift 7147788
  have htrace : WordTrace (prefixWord ++ tailWord_7147788) baseStart_7147788 baseEnd_7147788 := by
    simpa [prefixWord, tailWord_7147788, baseEnd_7147788] using wordTrace_append hprefix tailTrace_7147788
  have hstable : (prefixWord ++ tailWord_7147788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147788).length < 2 ^ (prefixWord ++ tailWord_7147788).sum := by decide
  have hdescent : baseEnd_7147788 < baseStart_7147788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147795 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 3]
def baseStart_7147795 : Nat := 118140960795 + 7147795 * 2 ^ 59
def prefixEnd_7147795 : Nat := 4983230072969 + 3 ^ 40 * 7147795 * 2
def baseEnd_7147795 : Nat := 3670254454803966952890395

theorem tailTrace_7147795 : CollatzResearch.WordTrace tailWord_7147795 prefixEnd_7147795 3670254454803966952890395 := by
  unfold tailWord_7147795
  simp only [CollatzResearch.WordTrace]
  refine ⟨260701501139766936042540839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173801000759844624028360559 260701501139766936042540839)
  ·
    refine ⟨391052251709650404063811259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260701501139766936042540839 391052251709650404063811259)
    ·
      refine ⟨586578377564475606095716889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391052251709650404063811259 586578377564475606095716889)
      ·
        refine ⟨439933783173356704571787667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586578377564475606095716889 439933783173356704571787667)
        ·
          refine ⟨659900674760035056857681501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439933783173356704571787667 659900674760035056857681501)
          ·
            refine ⟨247462753035013146321630563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 659900674760035056857681501 247462753035013146321630563)
            ·
              refine ⟨371194129552519719482445845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247462753035013146321630563 371194129552519719482445845)
              ·
                refine ⟨17399724822774361850739649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 371194129552519719482445845 17399724822774361850739649)
                ·
                  refine ⟨13049793617080771388054737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17399724822774361850739649 13049793617080771388054737)
                  ·
                    refine ⟨9787345212810578541041053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13049793617080771388054737 9787345212810578541041053)
                    ·
                      refine ⟨3670254454803966952890395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787345212810578541041053 3670254454803966952890395)
                      ·
                        rfl

theorem cell23_7147795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_7147795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147795 prefixEnd_7147795 := by exact prefixLift 7147795
  have htrace : WordTrace (prefixWord ++ tailWord_7147795) baseStart_7147795 baseEnd_7147795 := by
    simpa [prefixWord, tailWord_7147795, baseEnd_7147795] using wordTrace_append hprefix tailTrace_7147795
  have hstable : (prefixWord ++ tailWord_7147795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147795).length < 2 ^ (prefixWord ++ tailWord_7147795).sum := by decide
  have hdescent : baseEnd_7147795 < baseStart_7147795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147865 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_7147865 : Nat := 118140960795 + 7147865 * 2 ^ 59
def prefixEnd_7147865 : Nat := 4983230072969 + 3 ^ 40 * 7147865 * 2
def baseEnd_7147865 : Nat := 3670290398449781679015073

theorem tailTrace_7147865 : CollatzResearch.WordTrace tailWord_7147865 prefixEnd_7147865 3670290398449781679015073 := by
  unfold tailWord_7147865
  simp only [CollatzResearch.WordTrace]
  refine ⟨260704054249513337997589049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173802702833008891998392699 260704054249513337997589049)
  ·
    refine ⟨195528040687135003498191787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260704054249513337997589049 195528040687135003498191787)
    ·
      refine ⟨293292061030702505247287681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195528040687135003498191787 293292061030702505247287681)
      ·
        refine ⟨219969045773026878935465761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293292061030702505247287681 219969045773026878935465761)
        ·
          refine ⟨164976784329770159201599321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219969045773026878935465761 164976784329770159201599321)
          ·
            refine ⟨123732588247327619401199491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164976784329770159201599321 123732588247327619401199491)
            ·
              refine ⟨185598882370991429101799237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123732588247327619401199491 185598882370991429101799237)
              ·
                refine ⟨34799790444560892956587357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185598882370991429101799237 34799790444560892956587357)
                ·
                  refine ⟨13049921416710334858720259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34799790444560892956587357 13049921416710334858720259)
                  ·
                    refine ⟨19574882125065502288080389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13049921416710334858720259 19574882125065502288080389)
                    ·
                      refine ⟨3670290398449781679015073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19574882125065502288080389 3670290398449781679015073)
                      ·
                        rfl

theorem cell23_7147865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_7147865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147865 prefixEnd_7147865 := by exact prefixLift 7147865
  have htrace : WordTrace (prefixWord ++ tailWord_7147865) baseStart_7147865 baseEnd_7147865 := by
    simpa [prefixWord, tailWord_7147865, baseEnd_7147865] using wordTrace_append hprefix tailTrace_7147865
  have hstable : (prefixWord ++ tailWord_7147865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147865).length < 2 ^ (prefixWord ++ tailWord_7147865).sum := by decide
  have hdescent : baseEnd_7147865 < baseStart_7147865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147875 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 1, 6]
def baseStart_7147875 : Nat := 118140960795 + 7147875 * 2 ^ 59
def prefixEnd_7147875 : Nat := 4983230072969 + 3 ^ 40 * 7147875 * 2
def baseEnd_7147875 : Nat := 1223431844418775546630009

theorem tailTrace_7147875 : CollatzResearch.WordTrace tailWord_7147875 prefixEnd_7147875 1223431844418775546630009 := by
  unfold tailWord_7147875
  simp only [CollatzResearch.WordTrace]
  refine ⟨260704418979477109705453079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173802945986318073136968719 260704418979477109705453079)
  ·
    refine ⟨391056628469215664558179619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260704418979477109705453079 391056628469215664558179619)
    ·
      refine ⟨586584942703823496837269429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391056628469215664558179619 586584942703823496837269429)
      ·
        refine ⟨54992338378483452828494009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 586584942703823496837269429 54992338378483452828494009)
        ·
          refine ⟨41244253783862589621370507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54992338378483452828494009 41244253783862589621370507)
          ·
            refine ⟨61866380675793884432055761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41244253783862589621370507 61866380675793884432055761)
            ·
              refine ⟨46399785506845413324041821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61866380675793884432055761 46399785506845413324041821)
              ·
                refine ⟨17399919565067029996515683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46399785506845413324041821 17399919565067029996515683)
                ·
                  refine ⟨26099879347600544994773525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17399919565067029996515683 26099879347600544994773525)
                  ·
                    refine ⟨1223431844418775546630009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26099879347600544994773525 1223431844418775546630009)
                    ·
                      rfl

theorem cell23_7147875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 6].length) (baseStart_7147875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147875 prefixEnd_7147875 := by exact prefixLift 7147875
  have htrace : WordTrace (prefixWord ++ tailWord_7147875) baseStart_7147875 baseEnd_7147875 := by
    simpa [prefixWord, tailWord_7147875, baseEnd_7147875] using wordTrace_append hprefix tailTrace_7147875
  have hstable : (prefixWord ++ tailWord_7147875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147875).length < 2 ^ (prefixWord ++ tailWord_7147875).sum := by decide
  have hdescent : baseEnd_7147875 < baseStart_7147875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147879 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 1, 5]
def baseStart_7147879 : Nat := 118140960795 + 7147879 * 2 ^ 59
def prefixEnd_7147879 : Nat := 4983230072969 + 3 ^ 40 * 7147879 * 2
def baseEnd_7147879 : Nat := 1223432529059648208080003

theorem tailTrace_7147879 : CollatzResearch.WordTrace tailWord_7147879 prefixEnd_7147879 1223432529059648208080003 := by
  unfold tailWord_7147879
  simp only [CollatzResearch.WordTrace]
  refine ⟨260704564871462618388598691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173803043247641745592399127 260704564871462618388598691)
  ·
    refine ⟨391056847307193927582898037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260704564871462618388598691 391056847307193927582898037)
    ·
      refine ⟨36661579435049430710896691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 391056847307193927582898037 36661579435049430710896691)
      ·
        refine ⟨54992369152574146066345037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36661579435049430710896691 54992369152574146066345037)
        ·
          refine ⟨20622138432215304774879389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54992369152574146066345037 20622138432215304774879389)
          ·
            refine ⟨7733301912080739290579771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20622138432215304774879389 7733301912080739290579771)
            ·
              refine ⟨11599952868121108935869657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733301912080739290579771 11599952868121108935869657)
              ·
                refine ⟨8699964651090831701902243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11599952868121108935869657 8699964651090831701902243)
                ·
                  refine ⟨13049946976636247552853365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699964651090831701902243 13049946976636247552853365)
                  ·
                    refine ⟨1223432529059648208080003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13049946976636247552853365 1223432529059648208080003)
                    ·
                      rfl

theorem cell23_7147879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_7147879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147879 prefixEnd_7147879 := by exact prefixLift 7147879
  have htrace : WordTrace (prefixWord ++ tailWord_7147879) baseStart_7147879 baseEnd_7147879 := by
    simpa [prefixWord, tailWord_7147879, baseEnd_7147879] using wordTrace_append hprefix tailTrace_7147879
  have hstable : (prefixWord ++ tailWord_7147879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147879).length < 2 ^ (prefixWord ++ tailWord_7147879).sum := by decide
  have hdescent : baseEnd_7147879 < baseStart_7147879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147899 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 1, 1, 4]
def baseStart_7147899 : Nat := 118140960795 + 7147899 * 2 ^ 59
def prefixEnd_7147899 : Nat := 4983230072969 + 3 ^ 40 * 7147899 * 2
def baseEnd_7147899 : Nat := 3670307856792034545989917

theorem tailTrace_7147899 : CollatzResearch.WordTrace tailWord_7147899 prefixEnd_7147899 3670307856792034545989917 := by
  unfold tailWord_7147899
  simp only [CollatzResearch.WordTrace]
  refine ⟨260705294331390161804326751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173803529554260107869551167 260705294331390161804326751)
  ·
    refine ⟨391057941497085242706490127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260705294331390161804326751 391057941497085242706490127)
    ·
      refine ⟨586586912245627864059735191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391057941497085242706490127 586586912245627864059735191)
      ·
        refine ⟨879880368368441796089602787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586586912245627864059735191 879880368368441796089602787)
        ·
          refine ⟨1319820552552662694134404181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879880368368441796089602787 1319820552552662694134404181)
          ·
            refine ⟨15466647100226515946887549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1319820552552662694134404181 15466647100226515946887549)
            ·
              refine ⟨5799992662584943480082831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15466647100226515946887549 5799992662584943480082831)
              ·
                refine ⟨8699988993877415220124247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799992662584943480082831 8699988993877415220124247)
                ·
                  refine ⟨13049983490816122830186371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699988993877415220124247 13049983490816122830186371)
                  ·
                    refine ⟨19574975236224184245279557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13049983490816122830186371 19574975236224184245279557)
                    ·
                      refine ⟨3670307856792034545989917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19574975236224184245279557 3670307856792034545989917)
                      ·
                        rfl

theorem cell23_7147899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 1, 4].length) (baseStart_7147899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147899 prefixEnd_7147899 := by exact prefixLift 7147899
  have htrace : WordTrace (prefixWord ++ tailWord_7147899) baseStart_7147899 baseEnd_7147899 := by
    simpa [prefixWord, tailWord_7147899, baseEnd_7147899] using wordTrace_append hprefix tailTrace_7147899
  have hstable : (prefixWord ++ tailWord_7147899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147899).length < 2 ^ (prefixWord ++ tailWord_7147899).sum := by decide
  have hdescent : baseEnd_7147899 < baseStart_7147899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147905 : List Nat := [1, 2, 4, 3, 1, 12]
def baseStart_7147905 : Nat := 118140960795 + 7147905 * 2 ^ 59
def prefixEnd_7147905 : Nat := 4983230072969 + 3 ^ 40 * 7147905 * 2
def baseEnd_7147905 : Nat := 15104160237349635895123

theorem tailTrace_7147905 : CollatzResearch.WordTrace tailWord_7147905 prefixEnd_7147905 15104160237349635895123 := by
  unfold tailWord_7147905
  simp only [CollatzResearch.WordTrace]
  refine ⟨260705513169368424829045169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173803675446245616552696779 260705513169368424829045169)
  ·
    refine ⟨195529134877026318621783877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260705513169368424829045169 195529134877026318621783877)
    ·
      refine ⟨36661712789442434741584477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195529134877026318621783877 36661712789442434741584477)
      ·
        refine ⟨13748142296040913028094179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36661712789442434741584477 13748142296040913028094179)
        ·
          refine ⟨20622213444061369542141269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13748142296040913028094179 20622213444061369542141269)
          ·
            refine ⟨15104160237349635895123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20622213444061369542141269 15104160237349635895123)
            ·
              rfl

theorem cell23_7147905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 12].length) (baseStart_7147905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147905 prefixEnd_7147905 := by exact prefixLift 7147905
  have htrace : WordTrace (prefixWord ++ tailWord_7147905) baseStart_7147905 baseEnd_7147905 := by
    simpa [prefixWord, tailWord_7147905, baseEnd_7147905] using wordTrace_append hprefix tailTrace_7147905
  have hstable : (prefixWord ++ tailWord_7147905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147905).length < 2 ^ (prefixWord ++ tailWord_7147905).sum := by decide
  have hdescent : baseEnd_7147905 < baseStart_7147905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147935 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 2, 7]
def baseStart_7147935 : Nat := 118140960795 + 7147935 * 2 ^ 59
def prefixEnd_7147935 : Nat := 4983230072969 + 3 ^ 40 * 7147935 * 2
def baseEnd_7147935 : Nat := 1223442114031865468379917

theorem tailTrace_7147935 : CollatzResearch.WordTrace tailWord_7147935 prefixEnd_7147935 1223442114031865468379917 := by
  unfold tailWord_7147935
  simp only [CollatzResearch.WordTrace]
  refine ⟨260706607359259739952637259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173804404906173159968424839 260706607359259739952637259)
  ·
    refine ⟨391059911038889609928955889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260706607359259739952637259 391059911038889609928955889)
    ·
      refine ⟨293294933279167207446716917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391059911038889609928955889 293294933279167207446716917)
      ·
        refine ⟨27496399994921925698129711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293294933279167207446716917 27496399994921925698129711)
        ·
          refine ⟨41244599992382888547194567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27496399994921925698129711 41244599992382888547194567)
          ·
            refine ⟨61866899988574332820791851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41244599992382888547194567 61866899988574332820791851)
            ·
              refine ⟨92800349982861499231187777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61866899988574332820791851 92800349982861499231187777)
              ·
                refine ⟨69600262487146124423390833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92800349982861499231187777 69600262487146124423390833)
                ·
                  refine ⟨52200196865359593317543125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69600262487146124423390833 52200196865359593317543125)
                  ·
                    refine ⟨1223442114031865468379917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52200196865359593317543125 1223442114031865468379917)
                    ·
                      rfl

theorem cell23_7147935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_7147935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147935 prefixEnd_7147935 := by exact prefixLift 7147935
  have htrace : WordTrace (prefixWord ++ tailWord_7147935) baseStart_7147935 baseEnd_7147935 := by
    simpa [prefixWord, tailWord_7147935, baseEnd_7147935] using wordTrace_append hprefix tailTrace_7147935
  have hstable : (prefixWord ++ tailWord_7147935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147935).length < 2 ^ (prefixWord ++ tailWord_7147935).sum := by decide
  have hdescent : baseEnd_7147935 < baseStart_7147935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7147966 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_7147966 : Nat := 118140960795 + 7147966 * 2 ^ 59
def prefixEnd_7147966 : Nat := 4983230072969 + 3 ^ 40 * 7147966 * 2
def baseEnd_7147966 : Nat := 3670342259995885783852109

theorem tailTrace_7147966 : CollatzResearch.WordTrace tailWord_7147966 prefixEnd_7147966 3670342259995885783852109 := by
  unfold tailWord_7147966
  simp only [CollatzResearch.WordTrace]
  refine ⟨32588467252768429030876969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173805158681431621498010501 32588467252768429030876969)
  ·
    refine ⟨24441350439576321773157727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32588467252768429030876969 24441350439576321773157727)
    ·
      refine ⟨36662025659364482659736591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24441350439576321773157727 36662025659364482659736591)
      ·
        refine ⟨54993038489046723989604887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36662025659364482659736591 54993038489046723989604887)
        ·
          refine ⟨82489557733570085984407331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54993038489046723989604887 82489557733570085984407331)
          ·
            refine ⟨123734336600355128976610997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82489557733570085984407331 123734336600355128976610997)
            ·
              refine ⟨11600094056283293341557281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123734336600355128976610997 11600094056283293341557281)
              ·
                refine ⟨8700070542212470006167961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600094056283293341557281 8700070542212470006167961)
                ·
                  refine ⟨6525052906659352504625971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8700070542212470006167961 6525052906659352504625971)
                  ·
                    refine ⟨9787579359989028756938957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6525052906659352504625971 9787579359989028756938957)
                    ·
                      refine ⟨3670342259995885783852109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787579359989028756938957 3670342259995885783852109)
                      ·
                        rfl

theorem cell23_7147966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_7147966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7147966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7147966 prefixEnd_7147966 := by exact prefixLift 7147966
  have htrace : WordTrace (prefixWord ++ tailWord_7147966) baseStart_7147966 baseEnd_7147966 := by
    simpa [prefixWord, tailWord_7147966, baseEnd_7147966] using wordTrace_append hprefix tailTrace_7147966
  have hstable : (prefixWord ++ tailWord_7147966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7147966).length < 2 ^ (prefixWord ++ tailWord_7147966).sum := by decide
  have hdescent : baseEnd_7147966 < baseStart_7147966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7147966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148022 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7148022 : Nat := 118140960795 + 7148022 * 2 ^ 59
def prefixEnd_7148022 : Nat := 4983230072969 + 3 ^ 40 * 7148022 * 2
def baseEnd_7148022 : Nat := 3670371014912537564751851

theorem tailTrace_7148022 : CollatzResearch.WordTrace tailWord_7148022 prefixEnd_7148022 3670371014912537564751851 := by
  unfold tailWord_7148022
  simp only [CollatzResearch.WordTrace]
  refine ⟨16294361281871534613190895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173806520339963035874036213 16294361281871534613190895)
  ·
    refine ⟨24441541922807301919786343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16294361281871534613190895 24441541922807301919786343)
    ·
      refine ⟨36662312884210952879679515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24441541922807301919786343 36662312884210952879679515)
      ·
        refine ⟨54993469326316429319519273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36662312884210952879679515 54993469326316429319519273)
        ·
          refine ⟨41245101994737321989639455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54993469326316429319519273 41245101994737321989639455)
          ·
            refine ⟨61867652992105982984459183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41245101994737321989639455 61867652992105982984459183)
            ·
              refine ⟨92801479488158974476688775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61867652992105982984459183 92801479488158974476688775)
              ·
                refine ⟨139202219232238461715033163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92801479488158974476688775 139202219232238461715033163)
                ·
                  refine ⟨208803328848357692572549745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139202219232238461715033163 208803328848357692572549745)
                  ·
                    refine ⟨156602496636268269429412309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208803328848357692572549745 156602496636268269429412309)
                    ·
                      refine ⟨3670371014912537564751851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156602496636268269429412309 3670371014912537564751851)
                      ·
                        rfl

theorem cell23_7148022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7148022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148022 prefixEnd_7148022 := by exact prefixLift 7148022
  have htrace : WordTrace (prefixWord ++ tailWord_7148022) baseStart_7148022 baseEnd_7148022 := by
    simpa [prefixWord, tailWord_7148022, baseEnd_7148022] using wordTrace_append hprefix tailTrace_7148022
  have hstable : (prefixWord ++ tailWord_7148022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148022).length < 2 ^ (prefixWord ++ tailWord_7148022).sum := by decide
  have hdescent : baseEnd_7148022 < baseStart_7148022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148042 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_7148042 : Nat := 118140960795 + 7148042 * 2 ^ 59
def prefixEnd_7148042 : Nat := 4983230072969 + 3 ^ 40 * 7148042 * 2
def baseEnd_7148042 : Nat := 1223460428175209162167253

theorem tailTrace_7148042 : CollatzResearch.WordTrace tailWord_7148042 prefixEnd_7148042 1223460428175209162167253 := by
  unfold tailWord_7148042
  simp only [CollatzResearch.WordTrace]
  refine ⟨65177627492468024306695595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173807006646581398151188253 65177627492468024306695595)
  ·
    refine ⟨97766441238702036460043393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65177627492468024306695595 97766441238702036460043393)
    ·
      refine ⟨73324830929026527345032545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97766441238702036460043393 73324830929026527345032545)
      ·
        refine ⟨54993623196769895508774409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73324830929026527345032545 54993623196769895508774409)
        ·
          refine ⟨41245217397577421631580807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54993623196769895508774409 41245217397577421631580807)
          ·
            refine ⟨61867826096366132447371211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41245217397577421631580807 61867826096366132447371211)
            ·
              refine ⟨92801739144549198671056817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61867826096366132447371211 92801739144549198671056817)
              ·
                refine ⟨69601304358411899003292613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92801739144549198671056817 69601304358411899003292613)
                ·
                  refine ⟨13050244567202231063117365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69601304358411899003292613 13050244567202231063117365)
                  ·
                    refine ⟨1223460428175209162167253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13050244567202231063117365 1223460428175209162167253)
                    ·
                      rfl

theorem cell23_7148042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_7148042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148042 prefixEnd_7148042 := by exact prefixLift 7148042
  have htrace : WordTrace (prefixWord ++ tailWord_7148042) baseStart_7148042 baseEnd_7148042 := by
    simpa [prefixWord, tailWord_7148042, baseEnd_7148042] using wordTrace_append hprefix tailTrace_7148042
  have hstable : (prefixWord ++ tailWord_7148042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148042).length < 2 ^ (prefixWord ++ tailWord_7148042).sum := by decide
  have hdescent : baseEnd_7148042 < baseStart_7148042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148089 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 3, 4]
def baseStart_7148089 : Nat := 118140960795 + 7148089 * 2 ^ 59
def prefixEnd_7148089 : Nat := 4983230072969 + 3 ^ 40 * 7148089 * 2
def baseEnd_7148089 : Nat := 1223468472705462934204681

theorem tailTrace_7148089 : CollatzResearch.WordTrace tailWord_7148089 prefixEnd_7148089 1223468472705462934204681 := by
  unfold tailWord_7148089
  simp only [CollatzResearch.WordTrace]
  refine ⟨260712224200701824253743321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173808149467134549502495547 260712224200701824253743321)
  ·
    refine ⟨195534168150526368190307491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260712224200701824253743321 195534168150526368190307491)
    ·
      refine ⟨293301252225789552285461237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195534168150526368190307491 293301252225789552285461237)
      ·
        refine ⟨27496992396167770526761991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293301252225789552285461237 27496992396167770526761991)
        ·
          refine ⟨41245488594251655790142987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27496992396167770526761991 41245488594251655790142987)
          ·
            refine ⟨61868232891377483685214481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41245488594251655790142987 61868232891377483685214481)
            ·
              refine ⟨46401174668533112763910861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61868232891377483685214481 46401174668533112763910861)
              ·
                refine ⟨17400440500699917286466573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46401174668533112763910861 17400440500699917286466573)
                ·
                  refine ⟨6525165187762468982424965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17400440500699917286466573 6525165187762468982424965)
                  ·
                    refine ⟨1223468472705462934204681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6525165187762468982424965 1223468472705462934204681)
                    ·
                      rfl

theorem cell23_7148089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_7148089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148089 prefixEnd_7148089 := by exact prefixLift 7148089
  have htrace : WordTrace (prefixWord ++ tailWord_7148089) baseStart_7148089 baseEnd_7148089 := by
    simpa [prefixWord, tailWord_7148089, baseEnd_7148089] using wordTrace_append hprefix tailTrace_7148089
  have hstable : (prefixWord ++ tailWord_7148089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148089).length < 2 ^ (prefixWord ++ tailWord_7148089).sum := by decide
  have hdescent : baseEnd_7148089 < baseStart_7148089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148112 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3]
def baseStart_7148112 : Nat := 118140960795 + 7148112 * 2 ^ 59
def prefixEnd_7148112 : Nat := 4983230072969 + 3 ^ 40 * 7148112 * 2
def baseEnd_7148112 : Nat := 3670417228171442212626437

theorem tailTrace_7148112 : CollatzResearch.WordTrace tailWord_7148112 prefixEnd_7148112 3670417228171442212626437 := by
  unfold tailWord_7148112
  simp only [CollatzResearch.WordTrace]
  refine ⟨130356531539809249590915295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173808708719745666121220393 130356531539809249590915295)
  ·
    refine ⟨195534797309713874386372943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130356531539809249590915295 195534797309713874386372943)
    ·
      refine ⟨293302195964570811579559415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195534797309713874386372943 293302195964570811579559415)
      ·
        refine ⟨439953293946856217369339123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293302195964570811579559415 439953293946856217369339123)
        ·
          refine ⟨659929940920284326054008685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439953293946856217369339123 659929940920284326054008685)
          ·
            refine ⟨247473727845106622270253257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 659929940920284326054008685 247473727845106622270253257)
            ·
              refine ⟨185605295883829966702689943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247473727845106622270253257 185605295883829966702689943)
              ·
                refine ⟨278407943825744950054034915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185605295883829966702689943 278407943825744950054034915)
                ·
                  refine ⟨417611915738617425081052373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278407943825744950054034915 417611915738617425081052373)
                  ·
                    refine ⟨9787779275123845900337165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 417611915738617425081052373 9787779275123845900337165)
                    ·
                      refine ⟨3670417228171442212626437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787779275123845900337165 3670417228171442212626437)
                      ·
                        rfl

theorem cell23_7148112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_7148112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148112 prefixEnd_7148112 := by exact prefixLift 7148112
  have htrace : WordTrace (prefixWord ++ tailWord_7148112) baseStart_7148112 baseEnd_7148112 := by
    simpa [prefixWord, tailWord_7148112, baseEnd_7148112] using wordTrace_append hprefix tailTrace_7148112
  have hstable : (prefixWord ++ tailWord_7148112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148112).length < 2 ^ (prefixWord ++ tailWord_7148112).sum := by decide
  have hdescent : baseEnd_7148112 < baseStart_7148112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148116 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_7148116 : Nat := 118140960795 + 7148116 * 2 ^ 59
def prefixEnd_7148116 : Nat := 4983230072969 + 3 ^ 40 * 7148116 * 2
def baseEnd_7148116 : Nat := 3670419282094060196976419

theorem tailTrace_7148116 : CollatzResearch.WordTrace tailWord_7148116 prefixEnd_7148116 3670419282094060196976419 := by
  unfold tailWord_7148116
  simp only [CollatzResearch.WordTrace]
  refine ⟨130356604485802003932488101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173808805981069338576650801 130356604485802003932488101)
  ·
    refine ⟨24441863341087875737341519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130356604485802003932488101 24441863341087875737341519)
    ·
      refine ⟨36662795011631813606012279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24441863341087875737341519 36662795011631813606012279)
      ·
        refine ⟨54994192517447720409018419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36662795011631813606012279 54994192517447720409018419)
        ·
          refine ⟨82491288776171580613527629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54994192517447720409018419 82491288776171580613527629)
          ·
            refine ⟨30934233291064342730072861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82491288776171580613527629 30934233291064342730072861)
            ·
              refine ⟨11600337484149128523777323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30934233291064342730072861 11600337484149128523777323)
              ·
                refine ⟨17400506226223692785665985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11600337484149128523777323 17400506226223692785665985)
                ·
                  refine ⟨13050379669667769589249489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17400506226223692785665985 13050379669667769589249489)
                  ·
                    refine ⟨9787784752250827191937117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13050379669667769589249489 9787784752250827191937117)
                    ·
                      refine ⟨3670419282094060196976419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787784752250827191937117 3670419282094060196976419)
                      ·
                        rfl

theorem cell23_7148116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_7148116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148116 prefixEnd_7148116 := by exact prefixLift 7148116
  have htrace : WordTrace (prefixWord ++ tailWord_7148116) baseStart_7148116 baseEnd_7148116 := by
    simpa [prefixWord, tailWord_7148116, baseEnd_7148116] using wordTrace_append hprefix tailTrace_7148116
  have hstable : (prefixWord ++ tailWord_7148116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148116).length < 2 ^ (prefixWord ++ tailWord_7148116).sum := by decide
  have hdescent : baseEnd_7148116 < baseStart_7148116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148169 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 8, 2]
def baseStart_7148169 : Nat := 118140960795 + 7148169 * 2 ^ 59
def prefixEnd_7148169 : Nat := 4983230072969 + 3 ^ 40 * 7148169 * 2
def baseEnd_7148169 : Nat := 3670446496568748489613675

theorem tailTrace_7148169 : CollatzResearch.WordTrace tailWord_7148169 prefixEnd_7148169 3670446496568748489613675 := by
  unfold tailWord_7148169
  simp only [CollatzResearch.WordTrace]
  refine ⟨260715142040411997916655561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173810094693607998611103707 260715142040411997916655561)
  ·
    refine ⟨195536356530308998437491671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260715142040411997916655561 195536356530308998437491671)
    ·
      refine ⟨293304534795463497656237507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195536356530308998437491671 293304534795463497656237507)
      ·
        refine ⟨439956802193195246484356261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293304534795463497656237507 439956802193195246484356261)
        ·
          refine ⟨82491900411224108715816799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439956802193195246484356261 82491900411224108715816799)
          ·
            refine ⟨123737850616836163073725199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82491900411224108715816799 123737850616836163073725199)
            ·
              refine ⟨185606775925254244610587799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123737850616836163073725199 185606775925254244610587799)
              ·
                refine ⟨278410163887881366915881699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185606775925254244610587799 278410163887881366915881699)
                ·
                  refine ⟨417615245831822050373822549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278410163887881366915881699 417615245831822050373822549)
                  ·
                    refine ⟨4893928662091664652818233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 417615245831822050373822549 4893928662091664652818233)
                    ·
                      refine ⟨3670446496568748489613675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4893928662091664652818233 3670446496568748489613675)
                      ·
                        rfl

theorem cell23_7148169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 8, 2].length) (baseStart_7148169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148169 prefixEnd_7148169 := by exact prefixLift 7148169
  have htrace : WordTrace (prefixWord ++ tailWord_7148169) baseStart_7148169 baseEnd_7148169 := by
    simpa [prefixWord, tailWord_7148169, baseEnd_7148169] using wordTrace_append hprefix tailTrace_7148169
  have hstable : (prefixWord ++ tailWord_7148169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148169).length < 2 ^ (prefixWord ++ tailWord_7148169).sum := by decide
  have hdescent : baseEnd_7148169 < baseStart_7148169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148189 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_7148189 : Nat := 118140960795 + 7148189 * 2 ^ 59
def prefixEnd_7148189 : Nat := 4983230072969 + 3 ^ 40 * 7148189 * 2
def baseEnd_7148189 : Nat := 3670456766181838411363583

theorem tailTrace_7148189 : CollatzResearch.WordTrace tailWord_7148189 prefixEnd_7148189 3670456766181838411363583 := by
  unfold tailWord_7148189
  simp only [CollatzResearch.WordTrace]
  refine ⟨260715871500339541332383621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173810581000226360888255747 260715871500339541332383621)
  ·
    refine ⟨48884225906313663999821929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260715871500339541332383621 48884225906313663999821929)
    ·
      refine ⟨36663169429735247999866447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48884225906313663999821929 36663169429735247999866447)
      ·
        refine ⟨54994754144602871999799671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36663169429735247999866447 54994754144602871999799671)
        ·
          refine ⟨82492131216904307999699507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54994754144602871999799671 82492131216904307999699507)
          ·
            refine ⟨123738196825356461999549261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82492131216904307999699507 123738196825356461999549261)
            ·
              refine ⟨46401823809508673249830973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123738196825356461999549261 46401823809508673249830973)
              ·
                refine ⟨17400683928565752468686615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46401823809508673249830973 17400683928565752468686615)
                ·
                  refine ⟨26101025892848628703029923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17400683928565752468686615 26101025892848628703029923)
                  ·
                    refine ⟨39151538839272943054544885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26101025892848628703029923 39151538839272943054544885)
                    ·
                      refine ⟨3670456766181838411363583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39151538839272943054544885 3670456766181838411363583)
                      ·
                        rfl

theorem cell23_7148189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_7148189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148189 prefixEnd_7148189 := by exact prefixLift 7148189
  have htrace : WordTrace (prefixWord ++ tailWord_7148189) baseStart_7148189 baseEnd_7148189 := by
    simpa [prefixWord, tailWord_7148189, baseEnd_7148189] using wordTrace_append hprefix tailTrace_7148189
  have hstable : (prefixWord ++ tailWord_7148189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148189).length < 2 ^ (prefixWord ++ tailWord_7148189).sum := by decide
  have hdescent : baseEnd_7148189 < baseStart_7148189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148196 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_7148196 : Nat := 118140960795 + 7148196 * 2 ^ 59
def prefixEnd_7148196 : Nat := 4983230072969 + 3 ^ 40 * 7148196 * 2
def baseEnd_7148196 : Nat := 1223486786848806627992017

theorem tailTrace_7148196 : CollatzResearch.WordTrace tailWord_7148196 prefixEnd_7148196 1223486786848806627992017 := by
  unfold tailWord_7148196
  simp only [CollatzResearch.WordTrace]
  refine ⟨130358063405657090763944221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173810751207542787685258961 130358063405657090763944221)
  ·
    refine ⟨48884273777121409036479083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130358063405657090763944221 48884273777121409036479083)
    ·
      refine ⟨73326410665682113554718625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48884273777121409036479083 73326410665682113554718625)
      ·
        refine ⟨54994807999261585166038969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73326410665682113554718625 54994807999261585166038969)
        ·
          refine ⟨41246105999446188874529227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54994807999261585166038969 41246105999446188874529227)
          ·
            refine ⟨61869158999169283311793841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41246105999446188874529227 61869158999169283311793841)
            ·
              refine ⟨46401869249376962483845381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61869158999169283311793841 46401869249376962483845381)
              ·
                refine ⟨8700350484258180465721009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46401869249376962483845381 8700350484258180465721009)
                ·
                  refine ⟨6525262863193635349290757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8700350484258180465721009 6525262863193635349290757)
                  ·
                    refine ⟨1223486786848806627992017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6525262863193635349290757 1223486786848806627992017)
                    ·
                      rfl

theorem cell23_7148196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_7148196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148196 prefixEnd_7148196 := by exact prefixLift 7148196
  have htrace : WordTrace (prefixWord ++ tailWord_7148196) baseStart_7148196 baseEnd_7148196 := by
    simpa [prefixWord, tailWord_7148196, baseEnd_7148196] using wordTrace_append hprefix tailTrace_7148196
  have hstable : (prefixWord ++ tailWord_7148196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148196).length < 2 ^ (prefixWord ++ tailWord_7148196).sum := by decide
  have hdescent : baseEnd_7148196 < baseStart_7148196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148213 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_7148213 : Nat := 118140960795 + 7148213 * 2 ^ 59
def prefixEnd_7148213 : Nat := 4983230072969 + 3 ^ 40 * 7148213 * 2
def baseEnd_7148213 : Nat := 1223489696572515439154491

theorem tailTrace_7148213 : CollatzResearch.WordTrace tailWord_7148213 prefixEnd_7148213 1223489696572515439154491 := by
  unfold tailWord_7148213
  simp only [CollatzResearch.WordTrace]
  refine ⟨260716746852252593431257293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173811164568168395620838195 260716746852252593431257293)
  ·
    refine ⟨97768780069594722536721485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260716746852252593431257293 97768780069594722536721485)
    ·
      refine ⟨36663292526098020951270557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97768780069594722536721485 36663292526098020951270557)
      ·
        refine ⟨13748734697286757856726459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36663292526098020951270557 13748734697286757856726459)
        ·
          refine ⟨20623102045930136785089689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13748734697286757856726459 20623102045930136785089689)
          ·
            refine ⟨15467326534447602588817267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20623102045930136785089689 15467326534447602588817267)
            ·
              refine ⟨23200989801671403883225901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15467326534447602588817267 23200989801671403883225901)
              ·
                refine ⟨8700371175626776456209713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23200989801671403883225901 8700371175626776456209713)
                ·
                  refine ⟨6525278381720082342157285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8700371175626776456209713 6525278381720082342157285)
                  ·
                    refine ⟨1223489696572515439154491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6525278381720082342157285 1223489696572515439154491)
                    ·
                      rfl

theorem cell23_7148213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_7148213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148213 prefixEnd_7148213 := by exact prefixLift 7148213
  have htrace : WordTrace (prefixWord ++ tailWord_7148213) baseStart_7148213 baseEnd_7148213 := by
    simpa [prefixWord, tailWord_7148213, baseEnd_7148213] using wordTrace_append hprefix tailTrace_7148213
  have hstable : (prefixWord ++ tailWord_7148213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148213).length < 2 ^ (prefixWord ++ tailWord_7148213).sum := by decide
  have hdescent : baseEnd_7148213 < baseStart_7148213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148223 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 3]
def baseStart_7148223 : Nat := 118140960795 + 7148223 * 2 ^ 59
def prefixEnd_7148223 : Nat := 4983230072969 + 3 ^ 40 * 7148223 * 2
def baseEnd_7148223 : Nat := 3670474224524091278338427

theorem tailTrace_7148223 : CollatzResearch.WordTrace tailWord_7148223 prefixEnd_7148223 3670474224524091278338427 := by
  unfold tailWord_7148223
  simp only [CollatzResearch.WordTrace]
  refine ⟨260717111582216365139121323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173811407721477576759414215 260717111582216365139121323)
  ·
    refine ⟨391075667373324547708681985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260717111582216365139121323 391075667373324547708681985)
    ·
      refine ⟨293306750529993410781511489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391075667373324547708681985 293306750529993410781511489)
      ·
        refine ⟨219980062897495058086133617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293306750529993410781511489 219980062897495058086133617)
        ·
          refine ⟨164985047173121293564600213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219980062897495058086133617 164985047173121293564600213)
          ·
            refine ⟨7733674086240060635840635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164985047173121293564600213 7733674086240060635840635)
            ·
              refine ⟨11600511129360090953760953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733674086240060635840635 11600511129360090953760953)
              ·
                refine ⟨8700383347020068215320715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600511129360090953760953 8700383347020068215320715)
                ·
                  refine ⟨13050575020530102322981073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8700383347020068215320715 13050575020530102322981073)
                  ·
                    refine ⟨9787931265397576742235805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13050575020530102322981073 9787931265397576742235805)
                    ·
                      refine ⟨3670474224524091278338427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787931265397576742235805 3670474224524091278338427)
                      ·
                        rfl

theorem cell23_7148223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_7148223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148223 prefixEnd_7148223 := by exact prefixLift 7148223
  have htrace : WordTrace (prefixWord ++ tailWord_7148223) baseStart_7148223 baseEnd_7148223 := by
    simpa [prefixWord, tailWord_7148223, baseEnd_7148223] using wordTrace_append hprefix tailTrace_7148223
  have hstable : (prefixWord ++ tailWord_7148223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148223).length < 2 ^ (prefixWord ++ tailWord_7148223).sum := by decide
  have hdescent : baseEnd_7148223 < baseStart_7148223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148230 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7148230 : Nat := 118140960795 + 7148230 * 2 ^ 59
def prefixEnd_7148230 : Nat := 4983230072969 + 3 ^ 40 * 7148230 * 2
def baseEnd_7148230 : Nat := 1223492606296224250316965

theorem tailTrace_7148230 : CollatzResearch.WordTrace tailWord_7148230 prefixEnd_7148230 1223492606296224250316965 := by
  unfold tailWord_7148230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147417715412218916707067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173811577928794003556417429 8147417715412218916707067)
  ·
    refine ⟨12221126573118328375060601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8147417715412218916707067 12221126573118328375060601)
    ·
      refine ⟨9165844929838746281295451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12221126573118328375060601 9165844929838746281295451)
      ·
        refine ⟨13748767394758119421943177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9165844929838746281295451 13748767394758119421943177)
        ·
          refine ⟨10311575546068589566457383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13748767394758119421943177 10311575546068589566457383)
          ·
            refine ⟨15467363319102884349686075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10311575546068589566457383 15467363319102884349686075)
            ·
              refine ⟨23201044978654326524529113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15467363319102884349686075 23201044978654326524529113)
              ·
                refine ⟨17400783733990744893396835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23201044978654326524529113 17400783733990744893396835)
                ·
                  refine ⟨26101175600986117340095253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17400783733990744893396835 26101175600986117340095253)
                  ·
                    refine ⟨1223492606296224250316965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26101175600986117340095253 1223492606296224250316965)
                    ·
                      rfl

theorem cell23_7148230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7148230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148230 prefixEnd_7148230 := by exact prefixLift 7148230
  have htrace : WordTrace (prefixWord ++ tailWord_7148230) baseStart_7148230 baseEnd_7148230 := by
    simpa [prefixWord, tailWord_7148230, baseEnd_7148230] using wordTrace_append hprefix tailTrace_7148230
  have hstable : (prefixWord ++ tailWord_7148230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148230).length < 2 ^ (prefixWord ++ tailWord_7148230).sum := by decide
  have hdescent : baseEnd_7148230 < baseStart_7148230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148236 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7148236 : Nat := 118140960795 + 7148236 * 2 ^ 59
def prefixEnd_7148236 : Nat := 4983230072969 + 3 ^ 40 * 7148236 * 2
def baseEnd_7148236 : Nat := 3670480899772599727475867

theorem tailTrace_7148236 : CollatzResearch.WordTrace tailWord_7148236 prefixEnd_7148236 3670480899772599727475867 := by
  unfold tailWord_7148236
  simp only [CollatzResearch.WordTrace]
  refine ⟨130358792865584634179672281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173811723820779512239563041 130358792865584634179672281)
  ·
    refine ⟨97769094649188475634754211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130358792865584634179672281 97769094649188475634754211)
    ·
      refine ⟨146653641973782713452131317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97769094649188475634754211 146653641973782713452131317)
      ·
        refine ⟨13748778935042129386137311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146653641973782713452131317 13748778935042129386137311)
        ·
          refine ⟨20623168402563194079205967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13748778935042129386137311 20623168402563194079205967)
          ·
            refine ⟨30934752603844791118808951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20623168402563194079205967 30934752603844791118808951)
            ·
              refine ⟨46402128905767186678213427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30934752603844791118808951 46402128905767186678213427)
              ·
                refine ⟨69603193358650780017320141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46402128905767186678213427 69603193358650780017320141)
                ·
                  refine ⟨26101197509494042506495053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69603193358650780017320141 26101197509494042506495053)
                  ·
                    refine ⟨9787949066060265939935645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26101197509494042506495053 9787949066060265939935645)
                    ·
                      refine ⟨3670480899772599727475867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9787949066060265939935645 3670480899772599727475867)
                      ·
                        rfl

theorem cell23_7148236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7148236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148236 prefixEnd_7148236 := by exact prefixLift 7148236
  have htrace : WordTrace (prefixWord ++ tailWord_7148236) baseStart_7148236 baseEnd_7148236 := by
    simpa [prefixWord, tailWord_7148236, baseEnd_7148236] using wordTrace_append hprefix tailTrace_7148236
  have hstable : (prefixWord ++ tailWord_7148236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148236).length < 2 ^ (prefixWord ++ tailWord_7148236).sum := by decide
  have hdescent : baseEnd_7148236 < baseStart_7148236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148237 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7148237 : Nat := 118140960795 + 7148237 * 2 ^ 59
def prefixEnd_7148237 : Nat := 4983230072969 + 3 ^ 40 * 7148237 * 2
def baseEnd_7148237 : Nat := 3670481413253254223563363

theorem tailTrace_7148237 : CollatzResearch.WordTrace tailWord_7148237 prefixEnd_7148237 3670481413253254223563363 := by
  unfold tailWord_7148237
  simp only [CollatzResearch.WordTrace]
  refine ⟨260717622204165645530130965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173811748136110430353420643 260717622204165645530130965)
  ·
    refine ⟨12221138540820264634224889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260717622204165645530130965 12221138540820264634224889)
    ·
      refine ⟨9165853905615198475668667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12221138540820264634224889 9165853905615198475668667)
      ·
        refine ⟨13748780858422797713503001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9165853905615198475668667 13748780858422797713503001)
        ·
          refine ⟨10311585643817098285127251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13748780858422797713503001 10311585643817098285127251)
          ·
            refine ⟨15467378465725647427690877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10311585643817098285127251 15467378465725647427690877)
            ·
              refine ⟨5800266924647117785384079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15467378465725647427690877 5800266924647117785384079)
              ·
                refine ⟨8700400386970676678076119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800266924647117785384079 8700400386970676678076119)
                ·
                  refine ⟨13050600580456015017114179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8700400386970676678076119 13050600580456015017114179)
                  ·
                    refine ⟨19575900870684022525671269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13050600580456015017114179 19575900870684022525671269)
                    ·
                      refine ⟨3670481413253254223563363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19575900870684022525671269 3670481413253254223563363)
                      ·
                        rfl

theorem cell23_7148237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7148237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148237 prefixEnd_7148237 := by exact prefixLift 7148237
  have htrace : WordTrace (prefixWord ++ tailWord_7148237) baseStart_7148237 baseEnd_7148237 := by
    simpa [prefixWord, tailWord_7148237, baseEnd_7148237] using wordTrace_append hprefix tailTrace_7148237
  have hstable : (prefixWord ++ tailWord_7148237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148237).length < 2 ^ (prefixWord ++ tailWord_7148237).sum := by decide
  have hdescent : baseEnd_7148237 < baseStart_7148237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148279 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_7148279 : Nat := 118140960795 + 7148279 * 2 ^ 59
def prefixEnd_7148279 : Nat := 4983230072969 + 3 ^ 40 * 7148279 * 2
def baseEnd_7148279 : Nat := 3670502979440743059238169

theorem tailTrace_7148279 : CollatzResearch.WordTrace tailWord_7148279 prefixEnd_7148279 3670502979440743059238169 := by
  unfold tailWord_7148279
  simp only [CollatzResearch.WordTrace]
  refine ⟨260719154070013486703159891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173812769380008991135439927 260719154070013486703159891)
  ·
    refine ⟨391078731105020230054739837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260719154070013486703159891 391078731105020230054739837)
    ·
      refine ⟨146654524164382586270527439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391078731105020230054739837 146654524164382586270527439)
      ·
        refine ⟨219981786246573879405791159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146654524164382586270527439 219981786246573879405791159)
        ·
          refine ⟨329972679369860819108686739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219981786246573879405791159 329972679369860819108686739)
          ·
            refine ⟨494959019054791228663030109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329972679369860819108686739 494959019054791228663030109)
            ·
              refine ⟨185609632145546710748636291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494959019054791228663030109 185609632145546710748636291)
              ·
                refine ⟨278414448218320066122954437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185609632145546710748636291 278414448218320066122954437)
                ·
                  refine ⟨52202709040935012398053957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278414448218320066122954437 52202709040935012398053957)
                  ·
                    refine ⟨9788007945175314824635117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52202709040935012398053957 9788007945175314824635117)
                    ·
                      refine ⟨3670502979440743059238169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9788007945175314824635117 3670502979440743059238169)
                      ·
                        rfl

theorem cell23_7148279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_7148279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148279 prefixEnd_7148279 := by exact prefixLift 7148279
  have htrace : WordTrace (prefixWord ++ tailWord_7148279) baseStart_7148279 baseEnd_7148279 := by
    simpa [prefixWord, tailWord_7148279, baseEnd_7148279] using wordTrace_append hprefix tailTrace_7148279
  have hstable : (prefixWord ++ tailWord_7148279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148279).length < 2 ^ (prefixWord ++ tailWord_7148279).sum := by decide
  have hdescent : baseEnd_7148279 < baseStart_7148279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148289 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7148289 : Nat := 118140960795 + 7148289 * 2 ^ 59
def prefixEnd_7148289 : Nat := 4983230072969 + 3 ^ 40 * 7148289 * 2
def baseEnd_7148289 : Nat := 3670508114247288020113123

theorem tailTrace_7148289 : CollatzResearch.WordTrace tailWord_7148289 prefixEnd_7148289 3670508114247288020113123 := by
  unfold tailWord_7148289
  simp only [CollatzResearch.WordTrace]
  refine ⟨260719518799977258411023921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173813012533318172274015947 260719518799977258411023921)
  ·
    refine ⟨195539639099982943808267941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260719518799977258411023921 195539639099982943808267941)
    ·
      refine ⟨36663682331246801964050239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195539639099982943808267941 36663682331246801964050239)
      ·
        refine ⟨54995523496870202946075359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36663682331246801964050239 54995523496870202946075359)
        ·
          refine ⟨82493285245305304419113039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54995523496870202946075359 82493285245305304419113039)
          ·
            refine ⟨123739927867957956628669559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82493285245305304419113039 123739927867957956628669559)
            ·
              refine ⟨185609891801936934943004339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123739927867957956628669559 185609891801936934943004339)
              ·
                refine ⟨278414837702905402414506509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185609891801936934943004339 278414837702905402414506509)
                ·
                  refine ⟨104405564138589525905439941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278414837702905402414506509 104405564138589525905439941)
                  ·
                    refine ⟨19576043275985536107269989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104405564138589525905439941 19576043275985536107269989)
                    ·
                      refine ⟨3670508114247288020113123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19576043275985536107269989 3670508114247288020113123)
                      ·
                        rfl

theorem cell23_7148289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7148289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148289 prefixEnd_7148289 := by exact prefixLift 7148289
  have htrace : WordTrace (prefixWord ++ tailWord_7148289) baseStart_7148289 baseEnd_7148289 := by
    simpa [prefixWord, tailWord_7148289, baseEnd_7148289] using wordTrace_append hprefix tailTrace_7148289
  have hstable : (prefixWord ++ tailWord_7148289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148289).length < 2 ^ (prefixWord ++ tailWord_7148289).sum := by decide
  have hdescent : baseEnd_7148289 < baseStart_7148289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148316 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 7]
def baseStart_7148316 : Nat := 118140960795 + 7148316 * 2 ^ 59
def prefixEnd_7148316 : Nat := 4983230072969 + 3 ^ 40 * 7148316 * 2
def baseEnd_7148316 : Nat := 407835775358328823830611

theorem tailTrace_7148316 : CollatzResearch.WordTrace tailWord_7148316 prefixEnd_7148316 407835775358328823830611 := by
  unfold tailWord_7148316
  simp only [CollatzResearch.WordTrace]
  refine ⟨130360251785439721011128401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173813669047252961348171201 130360251785439721011128401)
  ·
    refine ⟨97770188839079790758346301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130360251785439721011128401 97770188839079790758346301)
    ·
      refine ⟨36663820814654921534379863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97770188839079790758346301 36663820814654921534379863)
      ·
        refine ⟨54995731221982382301569795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36663820814654921534379863 54995731221982382301569795)
        ·
          refine ⟨82493596832973573452354693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54995731221982382301569795 82493596832973573452354693)
          ·
            refine ⟨15467549406182545022316505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82493596832973573452354693 15467549406182545022316505)
            ·
              refine ⟨11600662054636908766737379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467549406182545022316505 11600662054636908766737379)
              ·
                refine ⟨17400993081955363150106069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11600662054636908766737379 17400993081955363150106069)
                ·
                  refine ⟨407835775358328823830611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17400993081955363150106069 407835775358328823830611)
                  ·
                    rfl

theorem cell23_7148316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_7148316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148316 prefixEnd_7148316 := by exact prefixLift 7148316
  have htrace : WordTrace (prefixWord ++ tailWord_7148316) baseStart_7148316 baseEnd_7148316 := by
    simpa [prefixWord, tailWord_7148316, baseEnd_7148316] using wordTrace_append hprefix tailTrace_7148316
  have hstable : (prefixWord ++ tailWord_7148316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148316).length < 2 ^ (prefixWord ++ tailWord_7148316).sum := by decide
  have hdescent : baseEnd_7148316 < baseStart_7148316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148329 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 4, 5]
def baseStart_7148329 : Nat := 118140960795 + 7148329 * 2 ^ 59
def prefixEnd_7148329 : Nat := 4983230072969 + 3 ^ 40 * 7148329 * 2
def baseEnd_7148329 : Nat := 1223509551157822621204313

theorem tailTrace_7148329 : CollatzResearch.WordTrace tailWord_7148329 prefixEnd_7148329 1223509551157822621204313 := by
  unfold tailWord_7148329
  simp only [CollatzResearch.WordTrace]
  refine ⟨260720977719832345242480041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173813985146554896828320027 260720977719832345242480041)
  ·
    refine ⟨195540733289874258931860031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260720977719832345242480041 195540733289874258931860031)
    ·
      refine ⟨293311099934811388397790047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195540733289874258931860031 293311099934811388397790047)
      ·
        refine ⟨439966649902217082596685071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293311099934811388397790047 439966649902217082596685071)
        ·
          refine ⟨659949974853325623895027607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439966649902217082596685071 659949974853325623895027607)
          ·
            refine ⟨989924962279988435842541411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659949974853325623895027607 989924962279988435842541411)
            ·
              refine ⟨1484887443419982653763812117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989924962279988435842541411 1484887443419982653763812117)
              ·
                refine ⟨69604098910311686895178693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1484887443419982653763812117 69604098910311686895178693)
                ·
                  refine ⟨13050768545683441292846005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69604098910311686895178693 13050768545683441292846005)
                  ·
                    refine ⟨1223509551157822621204313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13050768545683441292846005 1223509551157822621204313)
                    ·
                      rfl

theorem cell23_7148329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_7148329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148329 prefixEnd_7148329 := by exact prefixLift 7148329
  have htrace : WordTrace (prefixWord ++ tailWord_7148329) baseStart_7148329 baseEnd_7148329 := by
    simpa [prefixWord, tailWord_7148329, baseEnd_7148329] using wordTrace_append hprefix tailTrace_7148329
  have hstable : (prefixWord ++ tailWord_7148329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148329).length < 2 ^ (prefixWord ++ tailWord_7148329).sum := by decide
  have hdescent : baseEnd_7148329 < baseStart_7148329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148336 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 2, 5, 2]
def baseStart_7148336 : Nat := 118140960795 + 7148336 * 2 ^ 59
def prefixEnd_7148336 : Nat := 4983230072969 + 3 ^ 40 * 7148336 * 2
def baseEnd_7148336 : Nat := 3670532247838049336225407

theorem tailTrace_7148336 : CollatzResearch.WordTrace tailWord_7148336 prefixEnd_7148336 3670532247838049336225407 := by
  unfold tailWord_7148336
  simp only [CollatzResearch.WordTrace]
  refine ⟨130360616515403492718992431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173814155353871323625323241 130360616515403492718992431)
  ·
    refine ⟨195540924773105239078488647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130360616515403492718992431 195540924773105239078488647)
    ·
      refine ⟨293311387159657858617732971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195540924773105239078488647 293311387159657858617732971)
      ·
        refine ⟨439967080739486787926599457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293311387159657858617732971 439967080739486787926599457)
        ·
          refine ⟨329975310554615090944949593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439967080739486787926599457 329975310554615090944949593)
          ·
            refine ⟨247481482915961318208712195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329975310554615090944949593 247481482915961318208712195)
            ·
              refine ⟨371222224373941977313068293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247481482915961318208712195 371222224373941977313068293)
              ·
                refine ⟨69604167070114120746200305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371222224373941977313068293 69604167070114120746200305)
                ·
                  refine ⟨52203125302585590559650229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69604167070114120746200305 52203125302585590559650229)
                  ·
                    refine ⟨4894042997117399114967209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52203125302585590559650229 4894042997117399114967209)
                    ·
                      refine ⟨3670532247838049336225407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894042997117399114967209 3670532247838049336225407)
                      ·
                        rfl

theorem cell23_7148336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 5, 2].length) (baseStart_7148336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148336 prefixEnd_7148336 := by exact prefixLift 7148336
  have htrace : WordTrace (prefixWord ++ tailWord_7148336) baseStart_7148336 baseEnd_7148336 := by
    simpa [prefixWord, tailWord_7148336, baseEnd_7148336] using wordTrace_append hprefix tailTrace_7148336
  have hstable : (prefixWord ++ tailWord_7148336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148336).length < 2 ^ (prefixWord ++ tailWord_7148336).sum := by decide
  have hdescent : baseEnd_7148336 < baseStart_7148336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148379 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4]
def baseStart_7148379 : Nat := 118140960795 + 7148379 * 2 ^ 59
def prefixEnd_7148379 : Nat := 4983230072969 + 3 ^ 40 * 7148379 * 2
def baseEnd_7148379 : Nat := 3670554327506192667987709

theorem tailTrace_7148379 : CollatzResearch.WordTrace tailWord_7148379 prefixEnd_7148379 3670554327506192667987709 := by
  unfold tailWord_7148379
  simp only [CollatzResearch.WordTrace]
  refine ⟨260722801369651203781800191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173815200913100802521200127 260722801369651203781800191)
  ·
    refine ⟨391084202054476805672700287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260722801369651203781800191 391084202054476805672700287)
    ·
      refine ⟨586626303081715208509050431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391084202054476805672700287 586626303081715208509050431)
      ·
        refine ⟨879939454622572812763575647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586626303081715208509050431 879939454622572812763575647)
        ·
          refine ⟨1319909181933859219145363471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879939454622572812763575647 1319909181933859219145363471)
          ·
            refine ⟨1979863772900788828718045207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319909181933859219145363471 1979863772900788828718045207)
            ·
              refine ⟨2969795659351183243077067811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979863772900788828718045207 2969795659351183243077067811)
              ·
                refine ⟨4454693489026774864615601717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969795659351183243077067811 4454693489026774864615601717)
                ·
                  refine ⟨417627514596260143557712661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4454693489026774864615601717 417627514596260143557712661)
                  ·
                    refine ⟨19576289746699694229267781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 417627514596260143557712661 19576289746699694229267781)
                    ·
                      refine ⟨3670554327506192667987709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19576289746699694229267781 3670554327506192667987709)
                      ·
                        rfl

theorem cell23_7148379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_7148379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148379 prefixEnd_7148379 := by exact prefixLift 7148379
  have htrace : WordTrace (prefixWord ++ tailWord_7148379) baseStart_7148379 baseEnd_7148379 := by
    simpa [prefixWord, tailWord_7148379, baseEnd_7148379] using wordTrace_append hprefix tailTrace_7148379
  have hstable : (prefixWord ++ tailWord_7148379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148379).length < 2 ^ (prefixWord ++ tailWord_7148379).sum := by decide
  have hdescent : baseEnd_7148379 < baseStart_7148379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148423 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 6]
def baseStart_7148423 : Nat := 118140960795 + 7148423 * 2 ^ 59
def prefixEnd_7148423 : Nat := 4983230072969 + 3 ^ 40 * 7148423 * 2
def baseEnd_7148423 : Nat := 407841880072776721759723

theorem tailTrace_7148423 : CollatzResearch.WordTrace tailWord_7148423 prefixEnd_7148423 407841880072776721759723 := by
  unfold tailWord_7148423
  simp only [CollatzResearch.WordTrace]
  refine ⟨260724406181491799296401923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173816270787661199530934615 260724406181491799296401923)
  ·
    refine ⟨391086609272237698944602885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260724406181491799296401923 391086609272237698944602885)
    ·
      refine ⟨73328739238544568552113041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391086609272237698944602885 73328739238544568552113041)
      ·
        refine ⟨54996554428908426414084781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73328739238544568552113041 54996554428908426414084781)
        ·
          refine ⟨20623707910840659905281793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54996554428908426414084781 20623707910840659905281793)
          ·
            refine ⟨15467780933130494928961345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20623707910840659905281793 15467780933130494928961345)
            ·
              refine ⟨11600835699847871196721009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467780933130494928961345 11600835699847871196721009)
              ·
                refine ⟨8700626774885903397540757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600835699847871196721009 8700626774885903397540757)
                ·
                  refine ⟨407841880072776721759723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8700626774885903397540757 407841880072776721759723)
                  ·
                    rfl

theorem cell23_7148423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 6].length) (baseStart_7148423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148423 prefixEnd_7148423 := by exact prefixLift 7148423
  have htrace : WordTrace (prefixWord ++ tailWord_7148423) baseStart_7148423 baseEnd_7148423 := by
    simpa [prefixWord, tailWord_7148423, baseEnd_7148423] using wordTrace_append hprefix tailTrace_7148423
  have hstable : (prefixWord ++ tailWord_7148423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148423).length < 2 ^ (prefixWord ++ tailWord_7148423).sum := by decide
  have hdescent : baseEnd_7148423 < baseStart_7148423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148433 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_7148433 : Nat := 118140960795 + 7148433 * 2 ^ 59
def prefixEnd_7148433 : Nat := 4983230072969 + 3 ^ 40 * 7148433 * 2
def baseEnd_7148433 : Nat := 3670582055461535456712461

theorem tailTrace_7148433 : CollatzResearch.WordTrace tailWord_7148433 prefixEnd_7148433 3670582055461535456712461 := by
  unfold tailWord_7148433
  simp only [CollatzResearch.WordTrace]
  refine ⟨260724770911455571004265953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173816513940970380669510635 260724770911455571004265953)
  ·
    refine ⟨195543578183591678253199465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260724770911455571004265953 195543578183591678253199465)
    ·
      refine ⟨146657683637693758689899599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195543578183591678253199465 146657683637693758689899599)
      ·
        refine ⟨219986525456540638034849399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146657683637693758689899599 219986525456540638034849399)
        ·
          refine ⟨329979788184810957052274099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219986525456540638034849399 329979788184810957052274099)
          ·
            refine ⟨494969682277216435578411149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329979788184810957052274099 494969682277216435578411149)
            ·
              refine ⟨185613630853956163341904181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494969682277216435578411149 185613630853956163341904181)
              ·
                refine ⟨17401277892558390313303517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185613630853956163341904181 17401277892558390313303517)
                ·
                  refine ⟨6525479209709396367488819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17401277892558390313303517 6525479209709396367488819)
                  ·
                    refine ⟨9788218814564094551233229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6525479209709396367488819 9788218814564094551233229)
                    ·
                      refine ⟨3670582055461535456712461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9788218814564094551233229 3670582055461535456712461)
                      ·
                        rfl

theorem cell23_7148433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_7148433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148433 prefixEnd_7148433 := by exact prefixLift 7148433
  have htrace : WordTrace (prefixWord ++ tailWord_7148433) baseStart_7148433 baseEnd_7148433 := by
    simpa [prefixWord, tailWord_7148433, baseEnd_7148433] using wordTrace_append hprefix tailTrace_7148433
  have hstable : (prefixWord ++ tailWord_7148433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148433).length < 2 ^ (prefixWord ++ tailWord_7148433).sum := by decide
  have hdescent : baseEnd_7148433 < baseStart_7148433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148450 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_7148450 : Nat := 118140960795 + 7148450 * 2 ^ 59
def prefixEnd_7148450 : Nat := 4983230072969 + 3 ^ 40 * 7148450 * 2
def baseEnd_7148450 : Nat := 3670590784632661890199883

theorem tailTrace_7148450 : CollatzResearch.WordTrace tailWord_7148450 prefixEnd_7148450 3670590784632661890199883 := by
  unfold tailWord_7148450
  simp only [CollatzResearch.WordTrace]
  refine ⟨65181347738098495726908701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173816927301595988605089869 65181347738098495726908701)
  ·
    refine ⟨24443005401786935897590763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65181347738098495726908701 24443005401786935897590763)
    ·
      refine ⟨36664508102680403846386145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24443005401786935897590763 36664508102680403846386145)
      ·
        refine ⟨27498381077010302884789609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36664508102680403846386145 27498381077010302884789609)
        ·
          refine ⟨20623785807757727163592207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27498381077010302884789609 20623785807757727163592207)
          ·
            refine ⟨30935678711636590745388311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20623785807757727163592207 30935678711636590745388311)
            ·
              refine ⟨46403518067454886118082467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30935678711636590745388311 46403518067454886118082467)
              ·
                refine ⟨69605277101182329177123701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46403518067454886118082467 69605277101182329177123701)
                ·
                  refine ⟨6525494728235843360355347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69605277101182329177123701 6525494728235843360355347)
                  ·
                    refine ⟨9788242092353765040533021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6525494728235843360355347 9788242092353765040533021)
                    ·
                      refine ⟨3670590784632661890199883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9788242092353765040533021 3670590784632661890199883)
                      ·
                        rfl

theorem cell23_7148450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_7148450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148450 prefixEnd_7148450 := by exact prefixLift 7148450
  have htrace : WordTrace (prefixWord ++ tailWord_7148450) baseStart_7148450 baseEnd_7148450 := by
    simpa [prefixWord, tailWord_7148450, baseEnd_7148450] using wordTrace_append hprefix tailTrace_7148450
  have hstable : (prefixWord ++ tailWord_7148450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148450).length < 2 ^ (prefixWord ++ tailWord_7148450).sum := by decide
  have hdescent : baseEnd_7148450 < baseStart_7148450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148484 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7148484 : Nat := 118140960795 + 7148484 * 2 ^ 59
def prefixEnd_7148484 : Nat := 4983230072969 + 3 ^ 40 * 7148484 * 2
def baseEnd_7148484 : Nat := 3670608242974914757174727

theorem tailTrace_7148484 : CollatzResearch.WordTrace tailWord_7148484 prefixEnd_7148484 3670608242974914757174727 := by
  unfold tailWord_7148484
  simp only [CollatzResearch.WordTrace]
  refine ⟨130363315517135403357186253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173817754022847204476248337 130363315517135403357186253)
  ·
    refine ⟨48886243318925776258944845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130363315517135403357186253 48886243318925776258944845)
    ·
      refine ⟨18332341244597166097104317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48886243318925776258944845 18332341244597166097104317)
      ·
        refine ⟨6874627966723937286414119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18332341244597166097104317 6874627966723937286414119)
        ·
          refine ⟨10311941950085905929621179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874627966723937286414119 10311941950085905929621179)
          ·
            refine ⟨15467912925128858894431769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10311941950085905929621179 15467912925128858894431769)
            ·
              refine ⟨11600934693846644170823827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467912925128858894431769 11600934693846644170823827)
              ·
                refine ⟨17401402040769966256235741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11600934693846644170823827 17401402040769966256235741)
                ·
                  refine ⟨6525525765288737346088403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17401402040769966256235741 6525525765288737346088403)
                  ·
                    refine ⟨9788288647933106019132605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6525525765288737346088403 9788288647933106019132605)
                    ·
                      refine ⟨3670608242974914757174727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9788288647933106019132605 3670608242974914757174727)
                      ·
                        rfl

theorem cell23_7148484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7148484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148484 prefixEnd_7148484 := by exact prefixLift 7148484
  have htrace : WordTrace (prefixWord ++ tailWord_7148484) baseStart_7148484 baseEnd_7148484 := by
    simpa [prefixWord, tailWord_7148484, baseEnd_7148484] using wordTrace_append hprefix tailTrace_7148484
  have hstable : (prefixWord ++ tailWord_7148484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148484).length < 2 ^ (prefixWord ++ tailWord_7148484).sum := by decide
  have hdescent : baseEnd_7148484 < baseStart_7148484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148500 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_7148500 : Nat := 118140960795 + 7148500 * 2 ^ 59
def prefixEnd_7148500 : Nat := 4983230072969 + 3 ^ 40 * 7148500 * 2
def baseEnd_7148500 : Nat := 1223538819555128898191551

theorem tailTrace_7148500 : CollatzResearch.WordTrace tailWord_7148500 prefixEnd_7148500 1223538819555128898191551 := by
  unfold tailWord_7148500
  simp only [CollatzResearch.WordTrace]
  refine ⟨130363607301106420723477477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173818143068141894297969969 130363607301106420723477477)
  ·
    refine ⟨24443176368957453885652027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130363607301106420723477477 24443176368957453885652027)
    ·
      refine ⟨36664764553436180828478041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24443176368957453885652027 36664764553436180828478041)
      ·
        refine ⟨27498573415077135621358531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36664764553436180828478041 27498573415077135621358531)
        ·
          refine ⟨41247860122615703432037797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27498573415077135621358531 41247860122615703432037797)
          ·
            refine ⟨7733973772990444393507087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41247860122615703432037797 7733973772990444393507087)
            ·
              refine ⟨11600960659485666590260631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733973772990444393507087 11600960659485666590260631)
              ·
                refine ⟨17401440989228499885390947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11600960659485666590260631 17401440989228499885390947)
                ·
                  refine ⟨26102161483842749828086421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17401440989228499885390947 26102161483842749828086421)
                  ·
                    refine ⟨1223538819555128898191551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26102161483842749828086421 1223538819555128898191551)
                    ·
                      rfl

theorem cell23_7148500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_7148500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148500 prefixEnd_7148500 := by exact prefixLift 7148500
  have htrace : WordTrace (prefixWord ++ tailWord_7148500) baseStart_7148500 baseEnd_7148500 := by
    simpa [prefixWord, tailWord_7148500, baseEnd_7148500] using wordTrace_append hprefix tailTrace_7148500
  have hstable : (prefixWord ++ tailWord_7148500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148500).length < 2 ^ (prefixWord ++ tailWord_7148500).sum := by decide
  have hdescent : baseEnd_7148500 < baseStart_7148500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148530 : List Nat := [3, 2, 1, 5, 1, 2, 9]
def baseStart_7148530 : Nat := 118140960795 + 7148530 * 2 ^ 59
def prefixEnd_7148530 : Nat := 4983230072969 + 3 ^ 40 * 7148530 * 2
def baseEnd_7148530 : Nat := 45316442754136068854315

theorem tailTrace_7148530 : CollatzResearch.WordTrace tailWord_7148530 prefixEnd_7148530 45316442754136068854315 := by
  unfold tailWord_7148530
  simp only [CollatzResearch.WordTrace]
  refine ⟨65182077198026039142636761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173818872528069437713698029 65182077198026039142636761)
  ·
    refine ⟨48886557898519529356977571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65182077198026039142636761 48886557898519529356977571)
    ·
      refine ⟨73329836847779294035466357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48886557898519529356977571 73329836847779294035466357)
      ·
        refine ⟨6874672204479308815824971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73329836847779294035466357 6874672204479308815824971)
        ·
          refine ⟨10312008306718963223737457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874672204479308815824971 10312008306718963223737457)
          ·
            refine ⟨7734006230039222417803093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10312008306718963223737457 7734006230039222417803093)
            ·
              refine ⟨45316442754136068854315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7734006230039222417803093 45316442754136068854315)
              ·
                rfl

theorem cell23_7148530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 9].length) (baseStart_7148530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148530 prefixEnd_7148530 := by exact prefixLift 7148530
  have htrace : WordTrace (prefixWord ++ tailWord_7148530) baseStart_7148530 baseEnd_7148530 := by
    simpa [prefixWord, tailWord_7148530, baseEnd_7148530] using wordTrace_append hprefix tailTrace_7148530
  have hstable : (prefixWord ++ tailWord_7148530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148530).length < 2 ^ (prefixWord ++ tailWord_7148530).sum := by decide
  have hdescent : baseEnd_7148530 < baseStart_7148530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148536 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_7148536 : Nat := 118140960795 + 7148536 * 2 ^ 59
def prefixEnd_7148536 : Nat := 4983230072969 + 3 ^ 40 * 7148536 * 2
def baseEnd_7148536 : Nat := 3670634943968948553724487

theorem tailTrace_7148536 : CollatzResearch.WordTrace tailWord_7148536 prefixEnd_7148536 3670634943968948553724487 := by
  unfold tailWord_7148536
  simp only [CollatzResearch.WordTrace]
  refine ⟨130364263815041209797632731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173819018420054946396843641 130364263815041209797632731)
  ·
    refine ⟨195546395722561814696449097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130364263815041209797632731 195546395722561814696449097)
    ·
      refine ⟨146659796791921361022336823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195546395722561814696449097 146659796791921361022336823)
      ·
        refine ⟨219989695187882041533505235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146659796791921361022336823 219989695187882041533505235)
        ·
          refine ⟨329984542781823062300257853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219989695187882041533505235 329984542781823062300257853)
          ·
            refine ⟨123744203543183648362596695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329984542781823062300257853 123744203543183648362596695)
            ·
              refine ⟨185616305314775472543895043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123744203543183648362596695 185616305314775472543895043)
              ·
                refine ⟨278424457972163208815842565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185616305314775472543895043 278424457972163208815842565)
                ·
                  refine ⟨52204585869780601652970481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278424457972163208815842565 52204585869780601652970481)
                  ·
                    refine ⟨39153439402335451239727861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52204585869780601652970481 39153439402335451239727861)
                    ·
                      refine ⟨3670634943968948553724487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39153439402335451239727861 3670634943968948553724487)
                      ·
                        rfl

theorem cell23_7148536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_7148536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148536 prefixEnd_7148536 := by exact prefixLift 7148536
  have htrace : WordTrace (prefixWord ++ tailWord_7148536) baseStart_7148536 baseEnd_7148536 := by
    simpa [prefixWord, tailWord_7148536, baseEnd_7148536] using wordTrace_append hprefix tailTrace_7148536
  have hstable : (prefixWord ++ tailWord_7148536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148536).length < 2 ^ (prefixWord ++ tailWord_7148536).sum := by decide
  have hdescent : baseEnd_7148536 < baseStart_7148536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148540 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_7148540 : Nat := 118140960795 + 7148540 * 2 ^ 59
def prefixEnd_7148540 : Nat := 4983230072969 + 3 ^ 40 * 7148540 * 2
def baseEnd_7148540 : Nat := 3670636997891566538074469

theorem tailTrace_7148540 : CollatzResearch.WordTrace tailWord_7148540 prefixEnd_7148540 3670636997891566538074469 := by
  unfold tailWord_7148540
  simp only [CollatzResearch.WordTrace]
  refine ⟨130364336761033964139205537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173819115681378618852274049 130364336761033964139205537)
  ·
    refine ⟨97773252570775473104404153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130364336761033964139205537 97773252570775473104404153)
    ·
      refine ⟨73329939428081604828303115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97773252570775473104404153 73329939428081604828303115)
      ·
        refine ⟨109994909142122407242454673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73329939428081604828303115 109994909142122407242454673)
        ·
          refine ⟨82496181856591805431841005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109994909142122407242454673 82496181856591805431841005)
          ·
            refine ⟨30936068196221927036940377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82496181856591805431841005 30936068196221927036940377)
            ·
              refine ⟨23202051147166445277705283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30936068196221927036940377 23202051147166445277705283)
              ·
                refine ⟨34803076720749667916557925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23202051147166445277705283 34803076720749667916557925)
                ·
                  refine ⟨6525576885140562734354611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34803076720749667916557925 6525576885140562734354611)
                  ·
                    refine ⟨9788365327710844101531917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6525576885140562734354611 9788365327710844101531917)
                    ·
                      refine ⟨3670636997891566538074469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9788365327710844101531917 3670636997891566538074469)
                      ·
                        rfl

theorem cell23_7148540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_7148540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148540 prefixEnd_7148540 := by exact prefixLift 7148540
  have htrace : WordTrace (prefixWord ++ tailWord_7148540) baseStart_7148540 baseEnd_7148540 := by
    simpa [prefixWord, tailWord_7148540, baseEnd_7148540] using wordTrace_append hprefix tailTrace_7148540
  have hstable : (prefixWord ++ tailWord_7148540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148540).length < 2 ^ (prefixWord ++ tailWord_7148540).sum := by decide
  have hdescent : baseEnd_7148540 < baseStart_7148540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148567 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7148567 : Nat := 118140960795 + 7148567 * 2 ^ 59
def prefixEnd_7148567 : Nat := 4983230072969 + 3 ^ 40 * 7148567 * 2
def baseEnd_7148567 : Nat := 3670650861869237932436845

theorem tailTrace_7148567 : CollatzResearch.WordTrace tailWord_7148567 prefixEnd_7148567 3670650861869237932436845 := by
  unfold tailWord_7148567
  simp only [CollatzResearch.WordTrace]
  refine ⟨260729658292970111889643955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173819772195313407926429303 260729658292970111889643955)
  ·
    refine ⟨391094487439455167834465933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260729658292970111889643955 391094487439455167834465933)
    ·
      refine ⟨146660432789795687937924725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391094487439455167834465933 146660432789795687937924725)
      ·
        refine ⟨13749415574043345744180443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146660432789795687937924725 13749415574043345744180443)
        ·
          refine ⟨20624123361065018616270665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13749415574043345744180443 20624123361065018616270665)
          ·
            refine ⟨15468092520798763962202999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20624123361065018616270665 15468092520798763962202999)
            ·
              refine ⟨23202138781198145943304499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15468092520798763962202999 23202138781198145943304499)
              ·
                refine ⟨34803208171797218914956749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23202138781198145943304499 34803208171797218914956749)
                ·
                  refine ⟨13051203064423957093108781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34803208171797218914956749 13051203064423957093108781)
                  ·
                    refine ⟨4894201149158983909915793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13051203064423957093108781 4894201149158983909915793)
                    ·
                      refine ⟨3670650861869237932436845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894201149158983909915793 3670650861869237932436845)
                      ·
                        rfl

theorem cell23_7148567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7148567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148567 prefixEnd_7148567 := by exact prefixLift 7148567
  have htrace : WordTrace (prefixWord ++ tailWord_7148567) baseStart_7148567 baseEnd_7148567 := by
    simpa [prefixWord, tailWord_7148567, baseEnd_7148567] using wordTrace_append hprefix tailTrace_7148567
  have hstable : (prefixWord ++ tailWord_7148567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148567).length < 2 ^ (prefixWord ++ tailWord_7148567).sum := by decide
  have hdescent : baseEnd_7148567 < baseStart_7148567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148593 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_7148593 : Nat := 118140960795 + 7148593 * 2 ^ 59
def prefixEnd_7148593 : Nat := 4983230072969 + 3 ^ 40 * 7148593 * 2
def baseEnd_7148593 : Nat := 3670664212366254830711725

theorem tailTrace_7148593 : CollatzResearch.WordTrace tailWord_7148593 prefixEnd_7148593 3670664212366254830711725 := by
  unfold tailWord_7148593
  simp only [CollatzResearch.WordTrace]
  refine ⟨260730606590875918330090433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173820404393917278886726955 260730606590875918330090433)
  ·
    refine ⟨195547954943156938747567825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260730606590875918330090433 195547954943156938747567825)
    ·
      refine ⟨146660966207367704060675869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195547954943156938747567825 146660966207367704060675869)
      ·
        refine ⟨54997862327762889022753451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146660966207367704060675869 54997862327762889022753451)
        ·
          refine ⟨82496793491644333534130177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54997862327762889022753451 82496793491644333534130177)
          ·
            refine ⟨61872595118733250150597633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82496793491644333534130177 61872595118733250150597633)
            ·
              refine ⟨46404446339049937612948225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61872595118733250150597633 46404446339049937612948225)
              ·
                refine ⟨34803334754287453209711169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46404446339049937612948225 34803334754287453209711169)
                ·
                  refine ⟨26102501065715589907283377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34803334754287453209711169 26102501065715589907283377)
                  ·
                    refine ⟨19576875799286692430462533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26102501065715589907283377 19576875799286692430462533)
                    ·
                      refine ⟨3670664212366254830711725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19576875799286692430462533 3670664212366254830711725)
                      ·
                        rfl

theorem cell23_7148593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_7148593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148593 prefixEnd_7148593 := by exact prefixLift 7148593
  have htrace : WordTrace (prefixWord ++ tailWord_7148593) baseStart_7148593 baseEnd_7148593 := by
    simpa [prefixWord, tailWord_7148593, baseEnd_7148593] using wordTrace_append hprefix tailTrace_7148593
  have hstable : (prefixWord ++ tailWord_7148593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148593).length < 2 ^ (prefixWord ++ tailWord_7148593).sum := by decide
  have hdescent : baseEnd_7148593 < baseStart_7148593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148613 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_7148613 : Nat := 118140960795 + 7148613 * 2 ^ 59
def prefixEnd_7148613 : Nat := 4983230072969 + 3 ^ 40 * 7148613 * 2
def baseEnd_7148613 : Nat := 3670674481979344752461633

theorem tailTrace_7148613 : CollatzResearch.WordTrace tailWord_7148613 prefixEnd_7148613 3670674481979344752461633 := by
  unfold tailWord_7148613
  simp only [CollatzResearch.WordTrace]
  refine ⟨260731336050803461745818493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173820890700535641163878995 260731336050803461745818493)
  ·
    refine ⟨97774251019051298154681935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260731336050803461745818493 97774251019051298154681935)
    ·
      refine ⟨146661376528576947232022903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97774251019051298154681935 146661376528576947232022903)
      ·
        refine ⟨219992064792865420848034355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146661376528576947232022903 219992064792865420848034355)
        ·
          refine ⟨329988097189298131272051533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219992064792865420848034355 329988097189298131272051533)
          ·
            refine ⟨123745536445986799227019325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329988097189298131272051533 123745536445986799227019325)
            ·
              refine ⟨46404576167245049710132247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123745536445986799227019325 46404576167245049710132247)
              ·
                refine ⟨69606864250867574565198371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46404576167245049710132247 69606864250867574565198371)
                ·
                  refine ⟨104410296376301361847797557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69606864250867574565198371 104410296376301361847797557)
                  ·
                    refine ⟨9788465285278252673231021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104410296376301361847797557 9788465285278252673231021)
                    ·
                      refine ⟨3670674481979344752461633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9788465285278252673231021 3670674481979344752461633)
                      ·
                        rfl

theorem cell23_7148613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_7148613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148613 prefixEnd_7148613 := by exact prefixLift 7148613
  have htrace : WordTrace (prefixWord ++ tailWord_7148613) baseStart_7148613 baseEnd_7148613 := by
    simpa [prefixWord, tailWord_7148613, baseEnd_7148613] using wordTrace_append hprefix tailTrace_7148613
  have hstable : (prefixWord ++ tailWord_7148613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148613).length < 2 ^ (prefixWord ++ tailWord_7148613).sum := by decide
  have hdescent : baseEnd_7148613 < baseStart_7148613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148614 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7148614 : Nat := 118140960795 + 7148614 * 2 ^ 59
def prefixEnd_7148614 : Nat := 4983230072969 + 3 ^ 40 * 7148614 * 2
def baseEnd_7148614 : Nat := 3670674995459999248549129

theorem tailTrace_7148614 : CollatzResearch.WordTrace tailWord_7148614 prefixEnd_7148614 3670674995459999248549129 := by
  unfold tailWord_7148614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147855391368744966143903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173820915015866559277736597 8147855391368744966143903)
  ·
    refine ⟨12221783087053117449215855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8147855391368744966143903 12221783087053117449215855)
    ·
      refine ⟨18332674630579676173823783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12221783087053117449215855 18332674630579676173823783)
      ·
        refine ⟨27499011945869514260735675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18332674630579676173823783 27499011945869514260735675)
        ·
          refine ⟨41248517918804271391103513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27499011945869514260735675 41248517918804271391103513)
          ·
            refine ⟨30936388439103203543327635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41248517918804271391103513 30936388439103203543327635)
            ·
              refine ⟨46404582658654805314991453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30936388439103203543327635 46404582658654805314991453)
              ·
                refine ⟨17401718496995551993121795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46404582658654805314991453 17401718496995551993121795)
                ·
                  refine ⟨26102577745493327989682693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17401718496995551993121795 26102577745493327989682693)
                  ·
                    refine ⟨4894233327279998998065505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26102577745493327989682693 4894233327279998998065505)
                    ·
                      refine ⟨3670674995459999248549129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894233327279998998065505 3670674995459999248549129)
                      ·
                        rfl

theorem cell23_7148614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7148614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148614 prefixEnd_7148614 := by exact prefixLift 7148614
  have htrace : WordTrace (prefixWord ++ tailWord_7148614) baseStart_7148614 baseEnd_7148614 := by
    simpa [prefixWord, tailWord_7148614, baseEnd_7148614] using wordTrace_append hprefix tailTrace_7148614
  have hstable : (prefixWord ++ tailWord_7148614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148614).length < 2 ^ (prefixWord ++ tailWord_7148614).sum := by decide
  have hdescent : baseEnd_7148614 < baseStart_7148614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148633 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 2, 5]
def baseStart_7148633 : Nat := 118140960795 + 7148633 * 2 ^ 59
def prefixEnd_7148633 : Nat := 4983230072969 + 3 ^ 40 * 7148633 * 2
def baseEnd_7148633 : Nat := 1223561583864144891403847

theorem tailTrace_7148633 : CollatzResearch.WordTrace tailWord_7148633 prefixEnd_7148633 1223561583864144891403847 := by
  unfold tailWord_7148633
  simp only [CollatzResearch.WordTrace]
  refine ⟨260732065510731005161546553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173821377007154003441031035 260732065510731005161546553)
  ·
    refine ⟨195549049133048253871159915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260732065510731005161546553 195549049133048253871159915)
    ·
      refine ⟨293323573699572380806739873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195549049133048253871159915 293323573699572380806739873)
      ·
        refine ⟨219992680274679285605054905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293323573699572380806739873 219992680274679285605054905)
        ·
          refine ⟨164994510206009464203791179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219992680274679285605054905 164994510206009464203791179)
          ·
            refine ⟨247491765309014196305686769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164994510206009464203791179 247491765309014196305686769)
            ·
              refine ⟨185618823981760647229265077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247491765309014196305686769 185618823981760647229265077)
              ·
                refine ⟨17401764748290060677743601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185618823981760647229265077 17401764748290060677743601)
                ·
                  refine ⟨13051323561217545508307701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17401764748290060677743601 13051323561217545508307701)
                  ·
                    refine ⟨1223561583864144891403847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13051323561217545508307701 1223561583864144891403847)
                    ·
                      rfl

theorem cell23_7148633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_7148633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148633 prefixEnd_7148633 := by exact prefixLift 7148633
  have htrace : WordTrace (prefixWord ++ tailWord_7148633) baseStart_7148633 baseEnd_7148633 := by
    simpa [prefixWord, tailWord_7148633, baseEnd_7148633] using wordTrace_append hprefix tailTrace_7148633
  have hstable : (prefixWord ++ tailWord_7148633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148633).length < 2 ^ (prefixWord ++ tailWord_7148633).sum := by decide
  have hdescent : baseEnd_7148633 < baseStart_7148633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148648 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7148648 : Nat := 118140960795 + 7148648 * 2 ^ 59
def prefixEnd_7148648 : Nat := 4983230072969 + 3 ^ 40 * 7148648 * 2
def baseEnd_7148648 : Nat := 3670692453802252115523973

theorem tailTrace_7148648 : CollatzResearch.WordTrace tailWord_7148648 prefixEnd_7148648 3670692453802252115523973 := by
  unfold tailWord_7148648
  simp only [CollatzResearch.WordTrace]
  refine ⟨130366306302838331361671299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173821741737117775148895065 130366306302838331361671299)
  ·
    refine ⟨195549459454257497042506949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130366306302838331361671299 195549459454257497042506949)
    ·
      refine ⟨36665523647673280695470053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195549459454257497042506949 36665523647673280695470053)
      ·
        refine ⟨6874785683938740130400635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36665523647673280695470053 6874785683938740130400635)
        ·
          refine ⟨10312178525908110195600953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874785683938740130400635 10312178525908110195600953)
          ·
            refine ⟨7734133894431082646700715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10312178525908110195600953 7734133894431082646700715)
            ·
              refine ⟨11601200841646623970051073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7734133894431082646700715 11601200841646623970051073)
              ·
                refine ⟨8700900631234967977538305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11601200841646623970051073 8700900631234967977538305)
                ·
                  refine ⟨6525675473426225983153729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8700900631234967977538305 6525675473426225983153729)
                  ·
                    refine ⟨4894256605069669487365297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525675473426225983153729 4894256605069669487365297)
                    ·
                      refine ⟨3670692453802252115523973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894256605069669487365297 3670692453802252115523973)
                      ·
                        rfl

theorem cell23_7148648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7148648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148648 prefixEnd_7148648 := by exact prefixLift 7148648
  have htrace : WordTrace (prefixWord ++ tailWord_7148648) baseStart_7148648 baseEnd_7148648 := by
    simpa [prefixWord, tailWord_7148648, baseEnd_7148648] using wordTrace_append hprefix tailTrace_7148648
  have hstable : (prefixWord ++ tailWord_7148648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148648).length < 2 ^ (prefixWord ++ tailWord_7148648).sum := by decide
  have hdescent : baseEnd_7148648 < baseStart_7148648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148714 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7148714 : Nat := 118140960795 + 7148714 * 2 ^ 59
def prefixEnd_7148714 : Nat := 4983230072969 + 3 ^ 40 * 7148714 * 2
def baseEnd_7148714 : Nat := 1223575447841816285766223

theorem tailTrace_7148714 : CollatzResearch.WordTrace tailWord_7148714 prefixEnd_7148714 1223575447841816285766223 := by
  unfold tailWord_7148714
  simp only [CollatzResearch.WordTrace]
  refine ⟨65183754955859388998811299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173823346548958370663496797 65183754955859388998811299)
  ·
    refine ⟨97775632433789083498216949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65183754955859388998811299 97775632433789083498216949)
    ·
      refine ⟨9166465540667726577957839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97775632433789083498216949 9166465540667726577957839)
      ·
        refine ⟨13749698311001589866936759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9166465540667726577957839 13749698311001589866936759)
        ·
          refine ⟨20624547466502384800405139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13749698311001589866936759 20624547466502384800405139)
          ·
            refine ⟨30936821199753577200607709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20624547466502384800405139 30936821199753577200607709)
            ·
              refine ⟨11601307949907591450227891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30936821199753577200607709 11601307949907591450227891)
              ·
                refine ⟨17401961924861387175341837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11601307949907591450227891 17401961924861387175341837)
                ·
                  refine ⟨6525735721823020190753189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17401961924861387175341837 6525735721823020190753189)
                  ·
                    refine ⟨1223575447841816285766223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6525735721823020190753189 1223575447841816285766223)
                    ·
                      rfl

theorem cell23_7148714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7148714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148714 prefixEnd_7148714 := by exact prefixLift 7148714
  have htrace : WordTrace (prefixWord ++ tailWord_7148714) baseStart_7148714 baseEnd_7148714 := by
    simpa [prefixWord, tailWord_7148714, baseEnd_7148714] using wordTrace_append hprefix tailTrace_7148714
  have hstable : (prefixWord ++ tailWord_7148714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148714).length < 2 ^ (prefixWord ++ tailWord_7148714).sum := by decide
  have hdescent : baseEnd_7148714 < baseStart_7148714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148765 : List Nat := [1, 4, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_7148765 : Nat := 118140960795 + 7148765 * 2 ^ 59
def prefixEnd_7148765 : Nat := 4983230072969 + 3 ^ 40 * 7148765 * 2
def baseEnd_7148765 : Nat := 1223584177012942719253645

theorem tailTrace_7148765 : CollatzResearch.WordTrace tailWord_7148765 prefixEnd_7148765 1223584177012942719253645 := by
  unfold tailWord_7148765
  simp only [CollatzResearch.WordTrace]
  refine ⟨260736879946252791705351749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173824586630835194470234499 260736879946252791705351749)
  ·
    refine ⟨48888164989922398444753453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260736879946252791705351749 48888164989922398444753453)
    ·
      refine ⟨18333061871220899416782545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48888164989922398444753453 18333061871220899416782545)
      ·
        refine ⟨13749796403415674562586909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18333061871220899416782545 13749796403415674562586909)
        ·
          refine ⟨5156173651280877960970091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13749796403415674562586909 5156173651280877960970091)
          ·
            refine ⟨7734260476921316941455137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156173651280877960970091 7734260476921316941455137)
            ·
              refine ⟨5800695357690987706091353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7734260476921316941455137 5800695357690987706091353)
              ·
                refine ⟨4350521518268240779568515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5800695357690987706091353 4350521518268240779568515)
                ·
                  refine ⟨6525782277402361169352773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350521518268240779568515 6525782277402361169352773)
                  ·
                    refine ⟨1223584177012942719253645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6525782277402361169352773 1223584177012942719253645)
                    ·
                      rfl

theorem cell23_7148765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_7148765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148765 prefixEnd_7148765 := by exact prefixLift 7148765
  have htrace : WordTrace (prefixWord ++ tailWord_7148765) baseStart_7148765 baseEnd_7148765 := by
    simpa [prefixWord, tailWord_7148765, baseEnd_7148765] using wordTrace_append hprefix tailTrace_7148765
  have hstable : (prefixWord ++ tailWord_7148765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148765).length < 2 ^ (prefixWord ++ tailWord_7148765).sum := by decide
  have hdescent : baseEnd_7148765 < baseStart_7148765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148787 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 2, 4]
def baseStart_7148787 : Nat := 118140960795 + 7148787 * 2 ^ 59
def prefixEnd_7148787 : Nat := 4983230072969 + 3 ^ 40 * 7148787 * 2
def baseEnd_7148787 : Nat := 1223587942537742357228611

theorem tailTrace_7148787 : CollatzResearch.WordTrace tailWord_7148787 prefixEnd_7148787 1223587942537742357228611 := by
  unfold tailWord_7148787
  simp only [CollatzResearch.WordTrace]
  refine ⟨260737682352173089462652615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173825121568115392975101743 260737682352173089462652615)
  ·
    refine ⟨391106523528259634193978923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260737682352173089462652615 391106523528259634193978923)
    ·
      refine ⟨586659785292389451290968385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391106523528259634193978923 586659785292389451290968385)
      ·
        refine ⟨439994838969292088468226289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586659785292389451290968385 439994838969292088468226289)
        ·
          refine ⟨329996129226969066351169717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439994838969292088468226289 329996129226969066351169717)
          ·
            refine ⟨30937137115028349970422161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 329996129226969066351169717 30937137115028349970422161)
            ·
              refine ⟨23202852836271262477816621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30937137115028349970422161 23202852836271262477816621)
              ·
                refine ⟨8701069813601723429181233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23202852836271262477816621 8701069813601723429181233)
                ·
                  refine ⟨6525802360201292571885925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8701069813601723429181233 6525802360201292571885925)
                  ·
                    refine ⟨1223587942537742357228611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6525802360201292571885925 1223587942537742357228611)
                    ·
                      rfl

theorem cell23_7148787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 4].length) (baseStart_7148787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148787 prefixEnd_7148787 := by exact prefixLift 7148787
  have htrace : WordTrace (prefixWord ++ tailWord_7148787) baseStart_7148787 baseEnd_7148787 := by
    simpa [prefixWord, tailWord_7148787, baseEnd_7148787] using wordTrace_append hprefix tailTrace_7148787
  have hstable : (prefixWord ++ tailWord_7148787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148787).length < 2 ^ (prefixWord ++ tailWord_7148787).sum := by decide
  have hdescent : baseEnd_7148787 < baseStart_7148787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148794 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2]
def baseStart_7148794 : Nat := 118140960795 + 7148794 * 2 ^ 59
def prefixEnd_7148794 : Nat := 4983230072969 + 3 ^ 40 * 7148794 * 2
def baseEnd_7148794 : Nat := 3670767421977808544298301

theorem tailTrace_7148794 : CollatzResearch.WordTrace tailWord_7148794 prefixEnd_7148794 3670767421977808544298301 := by
  unfold tailWord_7148794
  simp only [CollatzResearch.WordTrace]
  refine ⟨65184484415786932414539359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173825291775431819772104957 65184484415786932414539359)
  ·
    refine ⟨97776726623680398621809039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65184484415786932414539359 97776726623680398621809039)
    ·
      refine ⟨146665089935520597932713559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97776726623680398621809039 146665089935520597932713559)
      ·
        refine ⟨219997634903280896899070339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146665089935520597932713559 219997634903280896899070339)
        ·
          refine ⟨329996452354921345348605509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219997634903280896899070339 329996452354921345348605509)
          ·
            refine ⟨61874334816547752252863533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329996452354921345348605509 61874334816547752252863533)
            ·
              refine ⟨23202875556205407094823825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61874334816547752252863533 23202875556205407094823825)
              ·
                refine ⟨17402156667154055321117869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23202875556205407094823825 17402156667154055321117869)
                ·
                  refine ⟨6525808750182770745419201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17402156667154055321117869 6525808750182770745419201)
                  ·
                    refine ⟨4894356562637078059064401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525808750182770745419201 4894356562637078059064401)
                    ·
                      refine ⟨3670767421977808544298301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894356562637078059064401 3670767421977808544298301)
                      ·
                        rfl

theorem cell23_7148794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_7148794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148794 prefixEnd_7148794 := by exact prefixLift 7148794
  have htrace : WordTrace (prefixWord ++ tailWord_7148794) baseStart_7148794 baseEnd_7148794 := by
    simpa [prefixWord, tailWord_7148794, baseEnd_7148794] using wordTrace_append hprefix tailTrace_7148794
  have hstable : (prefixWord ++ tailWord_7148794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148794).length < 2 ^ (prefixWord ++ tailWord_7148794).sum := by decide
  have hdescent : baseEnd_7148794 < baseStart_7148794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148811 : List Nat := [1, 1, 1, 1, 5, 3, 1, 5, 1, 2, 2]
def baseStart_7148811 : Nat := 118140960795 + 7148811 * 2 ^ 59
def prefixEnd_7148811 : Nat := 4983230072969 + 3 ^ 40 * 7148811 * 2
def baseEnd_7148811 : Nat := 3670776151148934977785723

theorem tailTrace_7148811 : CollatzResearch.WordTrace tailWord_7148811 prefixEnd_7148811 3670776151148934977785723 := by
  unfold tailWord_7148811
  simp only [CollatzResearch.WordTrace]
  refine ⟨260738557704086141561526287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173825705136057427707684191 260738557704086141561526287)
  ·
    refine ⟨391107836556129212342289431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260738557704086141561526287 391107836556129212342289431)
    ·
      refine ⟨586661754834193818513434147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391107836556129212342289431 586661754834193818513434147)
      ·
        refine ⟨879992632251290727770151221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586661754834193818513434147 879992632251290727770151221)
        ·
          refine ⟨82499309273558505728451677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 879992632251290727770151221 82499309273558505728451677)
          ·
            refine ⟨30937240977584439648169379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82499309273558505728451677 30937240977584439648169379)
            ·
              refine ⟨46405861466376659472254069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30937240977584439648169379 46405861466376659472254069)
              ·
                refine ⟨4350549512472811825523819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46405861466376659472254069 4350549512472811825523819)
                ·
                  refine ⟨6525824268709217738285729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350549512472811825523819 6525824268709217738285729)
                  ·
                    refine ⟨4894368201531913303714297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525824268709217738285729 4894368201531913303714297)
                    ·
                      refine ⟨3670776151148934977785723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894368201531913303714297 3670776151148934977785723)
                      ·
                        rfl

theorem cell23_7148811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 2, 2].length) (baseStart_7148811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148811 prefixEnd_7148811 := by exact prefixLift 7148811
  have htrace : WordTrace (prefixWord ++ tailWord_7148811) baseStart_7148811 baseEnd_7148811 := by
    simpa [prefixWord, tailWord_7148811, baseEnd_7148811] using wordTrace_append hprefix tailTrace_7148811
  have hstable : (prefixWord ++ tailWord_7148811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148811).length < 2 ^ (prefixWord ++ tailWord_7148811).sum := by decide
  have hdescent : baseEnd_7148811 < baseStart_7148811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148814 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_7148814 : Nat := 118140960795 + 7148814 * 2 ^ 59
def prefixEnd_7148814 : Nat := 4983230072969 + 3 ^ 40 * 7148814 * 2
def baseEnd_7148814 : Nat := 3670777691590898466048209

theorem tailTrace_7148814 : CollatzResearch.WordTrace tailWord_7148814 prefixEnd_7148814 3670777691590898466048209 := by
  unfold tailWord_7148814
  simp only [CollatzResearch.WordTrace]
  refine ⟨32592333390384409134235687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173825778082050182049256997 32592333390384409134235687)
  ·
    refine ⟨48888500085576613701353531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32592333390384409134235687 48888500085576613701353531)
    ·
      refine ⟨73332750128364920552030297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48888500085576613701353531 73332750128364920552030297)
      ·
        refine ⟨54999562596273690414022723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73332750128364920552030297 54999562596273690414022723)
        ·
          refine ⟨82499343894410535621034085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54999562596273690414022723 82499343894410535621034085)
          ·
            refine ⟨15468626980201975428943891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82499343894410535621034085 15468626980201975428943891)
            ·
              refine ⟨23202940470302963143415837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15468626980201975428943891 23202940470302963143415837)
              ·
                refine ⟨8701102676363611178780939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23202940470302963143415837 8701102676363611178780939)
                ·
                  refine ⟨13051654014545416768171409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701102676363611178780939 13051654014545416768171409)
                  ·
                    refine ⟨9788740510909062576128557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13051654014545416768171409 9788740510909062576128557)
                    ·
                      refine ⟨3670777691590898466048209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9788740510909062576128557 3670777691590898466048209)
                      ·
                        rfl

theorem cell23_7148814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_7148814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148814 prefixEnd_7148814 := by exact prefixLift 7148814
  have htrace : WordTrace (prefixWord ++ tailWord_7148814) baseStart_7148814 baseEnd_7148814 := by
    simpa [prefixWord, tailWord_7148814, baseEnd_7148814] using wordTrace_append hprefix tailTrace_7148814
  have hstable : (prefixWord ++ tailWord_7148814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148814).length < 2 ^ (prefixWord ++ tailWord_7148814).sum := by decide
  have hdescent : baseEnd_7148814 < baseStart_7148814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148867 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 3, 4, 2]
def baseStart_7148867 : Nat := 118140960795 + 7148867 * 2 ^ 59
def prefixEnd_7148867 : Nat := 4983230072969 + 3 ^ 40 * 7148867 * 2
def baseEnd_7148867 : Nat := 3670804906065586758685465

theorem tailTrace_7148867 : CollatzResearch.WordTrace tailWord_7148867 prefixEnd_7148867 3670804906065586758685465 := by
  unfold tailWord_7148867
  simp only [CollatzResearch.WordTrace]
  refine ⟨260740600191883263125564855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173827066794588842083709903 260740600191883263125564855)
  ·
    refine ⟨391110900287824894688347283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260740600191883263125564855 391110900287824894688347283)
    ·
      refine ⟨586666350431737342032520925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391110900287824894688347283 586666350431737342032520925)
      ·
        refine ⟨219999881411901503262195347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 586666350431737342032520925 219999881411901503262195347)
        ·
          refine ⟨329999822117852254893293021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219999881411901503262195347 329999822117852254893293021)
          ·
            refine ⟨123749933294194595584984883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329999822117852254893293021 123749933294194595584984883)
            ·
              refine ⟨185624899941291893377477325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123749933294194595584984883 185624899941291893377477325)
              ·
                refine ⟨69609337477984460016553997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185624899941291893377477325 69609337477984460016553997)
                ·
                  refine ⟨26103501554244172506207749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69609337477984460016553997 26103501554244172506207749)
                  ·
                    refine ⟨4894406541420782344913953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26103501554244172506207749 4894406541420782344913953)
                    ·
                      refine ⟨3670804906065586758685465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894406541420782344913953 3670804906065586758685465)
                      ·
                        rfl

theorem cell23_7148867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_7148867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148867 prefixEnd_7148867 := by exact prefixLift 7148867
  have htrace : WordTrace (prefixWord ++ tailWord_7148867) baseStart_7148867 baseEnd_7148867 := by
    simpa [prefixWord, tailWord_7148867, baseEnd_7148867] using wordTrace_append hprefix tailTrace_7148867
  have hstable : (prefixWord ++ tailWord_7148867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148867).length < 2 ^ (prefixWord ++ tailWord_7148867).sum := by decide
  have hdescent : baseEnd_7148867 < baseStart_7148867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148901 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 2, 2, 2]
def baseStart_7148901 : Nat := 118140960795 + 7148901 * 2 ^ 59
def prefixEnd_7148901 : Nat := 4983230072969 + 3 ^ 40 * 7148901 * 2
def baseEnd_7148901 : Nat := 3670822364407839625660309

theorem tailTrace_7148901 : CollatzResearch.WordTrace tailWord_7148901 prefixEnd_7148901 3670822364407839625660309 := by
  unfold tailWord_7148901
  simp only [CollatzResearch.WordTrace]
  refine ⟨260741840273760086932302557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173827893515840057954868371 260741840273760086932302557)
  ·
    refine ⟨97778190102660032599613459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260741840273760086932302557 97778190102660032599613459)
    ·
      refine ⟨146667285153990048899420189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97778190102660032599613459 146667285153990048899420189)
      ·
        refine ⟨55000231932746268337282571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146667285153990048899420189 55000231932746268337282571)
        ·
          refine ⟨82500347899119402505923857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55000231932746268337282571 82500347899119402505923857)
          ·
            refine ⟨61875260924339551879442893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82500347899119402505923857 61875260924339551879442893)
            ·
              refine ⟨23203222846627331954791085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61875260924339551879442893 23203222846627331954791085)
              ·
                refine ⟨8701208567485249483046657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23203222846627331954791085 8701208567485249483046657)
                ·
                  refine ⟨6525906425613937112284993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8701208567485249483046657 6525906425613937112284993)
                  ·
                    refine ⟨4894429819210452834213745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525906425613937112284993 4894429819210452834213745)
                    ·
                      refine ⟨3670822364407839625660309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894429819210452834213745 3670822364407839625660309)
                      ·
                        rfl

theorem cell23_7148901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_7148901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148901 prefixEnd_7148901 := by exact prefixLift 7148901
  have htrace : WordTrace (prefixWord ++ tailWord_7148901) baseStart_7148901 baseEnd_7148901 := by
    simpa [prefixWord, tailWord_7148901, baseEnd_7148901] using wordTrace_append hprefix tailTrace_7148901
  have hstable : (prefixWord ++ tailWord_7148901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148901).length < 2 ^ (prefixWord ++ tailWord_7148901).sum := by decide
  have hdescent : baseEnd_7148901 < baseStart_7148901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7148927 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 7, 2]
def baseStart_7148927 : Nat := 118140960795 + 7148927 * 2 ^ 59
def prefixEnd_7148927 : Nat := 4983230072969 + 3 ^ 40 * 7148927 * 2
def baseEnd_7148927 : Nat := 3670835714904856523935189

theorem tailTrace_7148927 : CollatzResearch.WordTrace tailWord_7148927 prefixEnd_7148927 3670835714904856523935189 := by
  unfold tailWord_7148927
  simp only [CollatzResearch.WordTrace]
  refine ⟨260742788571665893372749035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173828525714443928915166023 260742788571665893372749035)
  ·
    refine ⟨391114182857498840059123553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260742788571665893372749035 391114182857498840059123553)
    ·
      refine ⟨293335637143124130044342665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391114182857498840059123553 293335637143124130044342665)
      ·
        refine ⟨220001727857343097533256999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293335637143124130044342665 220001727857343097533256999)
        ·
          refine ⟨330002591786014646299885499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220001727857343097533256999 330002591786014646299885499)
          ·
            refine ⟨495003887679021969449828249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330002591786014646299885499 495003887679021969449828249)
            ·
              refine ⟨371252915759266477087371187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495003887679021969449828249 371252915759266477087371187)
              ·
                refine ⟨556879373638899715631056781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371252915759266477087371187 556879373638899715631056781)
                ·
                  refine ⟨208829765114587393361646293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556879373638899715631056781 208829765114587393361646293)
                  ·
                    refine ⟨4894447619873142031913585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 208829765114587393361646293 4894447619873142031913585)
                    ·
                      refine ⟨3670835714904856523935189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894447619873142031913585 3670835714904856523935189)
                      ·
                        rfl

theorem cell23_7148927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_7148927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7148927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7148927 prefixEnd_7148927 := by exact prefixLift 7148927
  have htrace : WordTrace (prefixWord ++ tailWord_7148927) baseStart_7148927 baseEnd_7148927 := by
    simpa [prefixWord, tailWord_7148927, baseEnd_7148927] using wordTrace_append hprefix tailTrace_7148927
  have hstable : (prefixWord ++ tailWord_7148927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7148927).length < 2 ^ (prefixWord ++ tailWord_7148927).sum := by decide
  have hdescent : baseEnd_7148927 < baseStart_7148927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7148927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149024 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 5, 1, 3]
def baseStart_7149024 : Nat := 118140960795 + 7149024 * 2 ^ 59
def prefixEnd_7149024 : Nat := 4983230072969 + 3 ^ 40 * 7149024 * 2
def baseEnd_7149024 : Nat := 3670885522528342644422243

theorem tailTrace_7149024 : CollatzResearch.WordTrace tailWord_7149024 prefixEnd_7149024 3670885522528342644422243 := by
  unfold tailWord_7149024
  simp only [CollatzResearch.WordTrace]
  refine ⟨130373163226157239469515063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173830884301542985959353417 130373163226157239469515063)
  ·
    refine ⟨195559744839235859204272595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130373163226157239469515063 195559744839235859204272595)
    ·
      refine ⟨293339617258853788806408893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195559744839235859204272595 293339617258853788806408893)
      ·
        refine ⟨110002356472070170802403335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293339617258853788806408893 110002356472070170802403335)
        ·
          refine ⟨165003534708105256203605003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110002356472070170802403335 165003534708105256203605003)
          ·
            refine ⟨247505302062157884305407505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165003534708105256203605003 247505302062157884305407505)
            ·
              refine ⟨185628976546618413229055629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247505302062157884305407505 185628976546618413229055629)
              ·
                refine ⟨69610866204981904960895861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185628976546618413229055629 69610866204981904960895861)
                ·
                  refine ⟨6526018706717053590083987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69610866204981904960895861 6526018706717053590083987)
                  ·
                    refine ⟨9789028060075580385125981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6526018706717053590083987 9789028060075580385125981)
                    ·
                      refine ⟨3670885522528342644422243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9789028060075580385125981 3670885522528342644422243)
                      ·
                        rfl

theorem cell23_7149024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_7149024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149024 prefixEnd_7149024 := by exact prefixLift 7149024
  have htrace : WordTrace (prefixWord ++ tailWord_7149024) baseStart_7149024 baseEnd_7149024 := by
    simpa [prefixWord, tailWord_7149024, baseEnd_7149024] using wordTrace_append hprefix tailTrace_7149024
  have hstable : (prefixWord ++ tailWord_7149024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149024).length < 2 ^ (prefixWord ++ tailWord_7149024).sum := by decide
  have hdescent : baseEnd_7149024 < baseStart_7149024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149087 : List Nat := [1, 1, 2, 4, 1, 1, 4, 9]
def baseStart_7149087 : Nat := 118140960795 + 7149087 * 2 ^ 59
def prefixEnd_7149087 : Nat := 4983230072969 + 3 ^ 40 * 7149087 * 2
def baseEnd_7149087 : Nat := 135959921178132440664239

theorem tailTrace_7149087 : CollatzResearch.WordTrace tailWord_7149087 prefixEnd_7149087 135959921178132440664239 := by
  unfold tailWord_7149087
  simp only [CollatzResearch.WordTrace]
  refine ⟨260748624251086240698573515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173832416167390827132382343 260748624251086240698573515)
  ·
    refine ⟨391122936376629361047860273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260748624251086240698573515 391122936376629361047860273)
    ·
      refine ⟨293342202282472020785895205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391122936376629361047860273 293342202282472020785895205)
      ·
        refine ⟨55001662927963503897355351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293342202282472020785895205 55001662927963503897355351)
        ·
          refine ⟨82502494391945255846033027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55001662927963503897355351 82502494391945255846033027)
          ·
            refine ⟨123753741587917883769049541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82502494391945255846033027 123753741587917883769049541)
            ·
              refine ⟨23203826547734603206696789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123753741587917883769049541 23203826547734603206696789)
              ·
                refine ⟨135959921178132440664239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23203826547734603206696789 135959921178132440664239)
                ·
                  rfl

theorem cell23_7149087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 9].length) (baseStart_7149087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149087 prefixEnd_7149087 := by exact prefixLift 7149087
  have htrace : WordTrace (prefixWord ++ tailWord_7149087) baseStart_7149087 baseEnd_7149087 := by
    simpa [prefixWord, tailWord_7149087, baseEnd_7149087] using wordTrace_append hprefix tailTrace_7149087
  have hstable : (prefixWord ++ tailWord_7149087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149087).length < 2 ^ (prefixWord ++ tailWord_7149087).sum := by decide
  have hdescent : baseEnd_7149087 < baseStart_7149087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149098 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_7149098 : Nat := 118140960795 + 7149098 * 2 ^ 59
def prefixEnd_7149098 : Nat := 4983230072969 + 3 ^ 40 * 7149098 * 2
def baseEnd_7149098 : Nat := 3670923520096775354896903

theorem tailTrace_7149098 : CollatzResearch.WordTrace tailWord_7149098 prefixEnd_7149098 3670923520096775354896903 := by
  unfold tailWord_7149098
  simp only [CollatzResearch.WordTrace]
  refine ⟨65187256363511597394305987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173832683636030926384815965 65187256363511597394305987)
  ·
    refine ⟨97780884545267396091458981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65187256363511597394305987 97780884545267396091458981)
    ·
      refine ⟨18333915852237636767148559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97780884545267396091458981 18333915852237636767148559)
      ·
        refine ⟨27500873778356455150722839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18333915852237636767148559 27500873778356455150722839)
        ·
          refine ⟨41251310667534682726084259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27500873778356455150722839 41251310667534682726084259)
          ·
            refine ⟨61876966001302024089126389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41251310667534682726084259 61876966001302024089126389)
            ·
              refine ⟨5800965562622064758355599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61876966001302024089126389 5800965562622064758355599)
              ·
                refine ⟨8701448343933097137533399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800965562622064758355599 8701448343933097137533399)
                ·
                  refine ⟨13052172515899645706300099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701448343933097137533399 13052172515899645706300099)
                  ·
                    refine ⟨19578258773849468559450149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13052172515899645706300099 19578258773849468559450149)
                    ·
                      refine ⟨3670923520096775354896903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19578258773849468559450149 3670923520096775354896903)
                      ·
                        rfl

theorem cell23_7149098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_7149098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149098 prefixEnd_7149098 := by exact prefixLift 7149098
  have htrace : WordTrace (prefixWord ++ tailWord_7149098) baseStart_7149098 baseEnd_7149098 := by
    simpa [prefixWord, tailWord_7149098, baseEnd_7149098] using wordTrace_append hprefix tailTrace_7149098
  have hstable : (prefixWord ++ tailWord_7149098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149098).length < 2 ^ (prefixWord ++ tailWord_7149098).sum := by decide
  have hdescent : baseEnd_7149098 < baseStart_7149098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149114 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_7149114 : Nat := 118140960795 + 7149114 * 2 ^ 59
def prefixEnd_7149114 : Nat := 4983230072969 + 3 ^ 40 * 7149114 * 2
def baseEnd_7149114 : Nat := 3670931735787247292296829

theorem tailTrace_7149114 : CollatzResearch.WordTrace tailWord_7149114 prefixEnd_7149114 3670931735787247292296829 := by
  unfold tailWord_7149114
  simp only [CollatzResearch.WordTrace]
  refine ⟨65187402255497106077451599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173833072681325616206537597 65187402255497106077451599)
  ·
    refine ⟨97781103383245659116177399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65187402255497106077451599 97781103383245659116177399)
    ·
      refine ⟨146671655074868488674266099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97781103383245659116177399 146671655074868488674266099)
      ·
        refine ⟨220007482612302733011399149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146671655074868488674266099 220007482612302733011399149)
        ·
          refine ⟨82502805979613524879274681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220007482612302733011399149 82502805979613524879274681)
          ·
            refine ⟨61877104484710143659456011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82502805979613524879274681 61877104484710143659456011)
            ·
              refine ⟨92815656727065215489184017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61877104484710143659456011 92815656727065215489184017)
              ·
                refine ⟨69611742545298911616888013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92815656727065215489184017 69611742545298911616888013)
                ·
                  refine ⟨26104403454487091856333005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69611742545298911616888013 26104403454487091856333005)
                  ·
                    refine ⟨9789151295432659446124877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26104403454487091856333005 9789151295432659446124877)
                    ·
                      refine ⟨3670931735787247292296829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9789151295432659446124877 3670931735787247292296829)
                      ·
                        rfl

theorem cell23_7149114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_7149114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149114 prefixEnd_7149114 := by exact prefixLift 7149114
  have htrace : WordTrace (prefixWord ++ tailWord_7149114) baseStart_7149114 baseEnd_7149114 := by
    simpa [prefixWord, tailWord_7149114, baseEnd_7149114] using wordTrace_append hprefix tailTrace_7149114
  have hstable : (prefixWord ++ tailWord_7149114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149114).length < 2 ^ (prefixWord ++ tailWord_7149114).sum := by decide
  have hdescent : baseEnd_7149114 < baseStart_7149114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149149 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7149149 : Nat := 118140960795 + 7149149 * 2 ^ 59
def prefixEnd_7149149 : Nat := 4983230072969 + 3 ^ 40 * 7149149 * 2
def baseEnd_7149149 : Nat := 3670949707610154655359169

theorem tailTrace_7149149 : CollatzResearch.WordTrace tailWord_7149149 prefixEnd_7149149 3670949707610154655359169 := by
  unfold tailWord_7149149
  simp only [CollatzResearch.WordTrace]
  refine ⟨260750885576861625287330501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173833923717907750191553667 260750885576861625287330501)
  ·
    refine ⟨48890791045661554741374469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260750885576861625287330501 48890791045661554741374469)
    ·
      refine ⟨9167023321061541514007713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48890791045661554741374469 9167023321061541514007713)
      ·
        refine ⟨6875267490796156135505785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9167023321061541514007713 6875267490796156135505785)
        ·
          refine ⟨5156450618097117101629339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6875267490796156135505785 5156450618097117101629339)
          ·
            refine ⟨7734675927145675652444009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156450618097117101629339 7734675927145675652444009)
            ·
              refine ⟨5801006945359256739333007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7734675927145675652444009 5801006945359256739333007)
              ·
                refine ⟨8701510418038885108999511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801006945359256739333007 8701510418038885108999511)
                ·
                  refine ⟨13052265627058327663499267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701510418038885108999511 13052265627058327663499267)
                  ·
                    refine ⟨19578398440587491495248901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13052265627058327663499267 19578398440587491495248901)
                    ·
                      refine ⟨3670949707610154655359169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19578398440587491495248901 3670949707610154655359169)
                      ·
                        rfl

theorem cell23_7149149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7149149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149149 prefixEnd_7149149 := by exact prefixLift 7149149
  have htrace : WordTrace (prefixWord ++ tailWord_7149149) baseStart_7149149 baseEnd_7149149 := by
    simpa [prefixWord, tailWord_7149149, baseEnd_7149149] using wordTrace_append hprefix tailTrace_7149149
  have hstable : (prefixWord ++ tailWord_7149149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149149).length < 2 ^ (prefixWord ++ tailWord_7149149).sum := by decide
  have hdescent : baseEnd_7149149 < baseStart_7149149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149184 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_7149184 : Nat := 118140960795 + 7149184 * 2 ^ 59
def prefixEnd_7149184 : Nat := 4983230072969 + 3 ^ 40 * 7149184 * 2
def baseEnd_7149184 : Nat := 3670967679433062018421507

theorem tailTrace_7149184 : CollatzResearch.WordTrace tailWord_7149184 prefixEnd_7149184 3670967679433062018421507 := by
  unfold tailWord_7149184
  simp only [CollatzResearch.WordTrace]
  refine ⟨130376081065867413132427303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173834774754489884176569737 130376081065867413132427303)
  ·
    refine ⟨195564121598801119698640955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130376081065867413132427303 195564121598801119698640955)
    ·
      refine ⟨293346182398201679547961433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195564121598801119698640955 293346182398201679547961433)
      ·
        refine ⟨220009636798651259660971075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293346182398201679547961433 220009636798651259660971075)
        ·
          refine ⟨330014455197976889491456613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220009636798651259660971075 330014455197976889491456613)
          ·
            refine ⟨61877710349620666779648115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330014455197976889491456613 61877710349620666779648115)
            ·
              refine ⟨92816565524431000169472173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61877710349620666779648115 92816565524431000169472173)
              ·
                refine ⟨34806212071661625063552065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92816565524431000169472173 34806212071661625063552065)
                ·
                  refine ⟨26104659053746218797664049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34806212071661625063552065 26104659053746218797664049)
                  ·
                    refine ⟨19578494290309664098248037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26104659053746218797664049 19578494290309664098248037)
                    ·
                      refine ⟨3670967679433062018421507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19578494290309664098248037 3670967679433062018421507)
                      ·
                        rfl

theorem cell23_7149184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_7149184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149184 prefixEnd_7149184 := by exact prefixLift 7149184
  have htrace : WordTrace (prefixWord ++ tailWord_7149184) baseStart_7149184 baseEnd_7149184 := by
    simpa [prefixWord, tailWord_7149184, baseEnd_7149184] using wordTrace_append hprefix tailTrace_7149184
  have hstable : (prefixWord ++ tailWord_7149184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149184).length < 2 ^ (prefixWord ++ tailWord_7149184).sum := by decide
  have hdescent : baseEnd_7149184 < baseStart_7149184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149192 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7149192 : Nat := 118140960795 + 7149192 * 2 ^ 59
def prefixEnd_7149192 : Nat := 4983230072969 + 3 ^ 40 * 7149192 * 2
def baseEnd_7149192 : Nat := 3670971787278297987121471

theorem tailTrace_7149192 : CollatzResearch.WordTrace tailWord_7149192 prefixEnd_7149192 3670971787278297987121471 := by
  unfold tailWord_7149192
  simp only [CollatzResearch.WordTrace]
  refine ⟨130376226957852921815572915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173834969277137229087430553 130376226957852921815572915)
  ·
    refine ⟨195564340436779382723359373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130376226957852921815572915 195564340436779382723359373)
    ·
      refine ⟨73336627663792268521259765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195564340436779382723359373 73336627663792268521259765)
      ·
        refine ⟨6875308843480525173868103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73336627663792268521259765 6875308843480525173868103)
        ·
          refine ⟨10312963265220787760802155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875308843480525173868103 10312963265220787760802155)
          ·
            refine ⟨15469444897831181641203233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10312963265220787760802155 15469444897831181641203233)
            ·
              refine ⟨11602083673373386230902425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15469444897831181641203233 11602083673373386230902425)
              ·
                refine ⟨8701562755030039673176819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602083673373386230902425 8701562755030039673176819)
                ·
                  refine ⟨13052344132545059509765229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701562755030039673176819 13052344132545059509765229)
                  ·
                    refine ⟨4894629049704397316161961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13052344132545059509765229 4894629049704397316161961)
                    ·
                      refine ⟨3670971787278297987121471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894629049704397316161961 3670971787278297987121471)
                      ·
                        rfl

theorem cell23_7149192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7149192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149192 prefixEnd_7149192 := by exact prefixLift 7149192
  have htrace : WordTrace (prefixWord ++ tailWord_7149192) baseStart_7149192 baseEnd_7149192 := by
    simpa [prefixWord, tailWord_7149192, baseEnd_7149192] using wordTrace_append hprefix tailTrace_7149192
  have hstable : (prefixWord ++ tailWord_7149192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149192).length < 2 ^ (prefixWord ++ tailWord_7149192).sum := by decide
  have hdescent : baseEnd_7149192 < baseStart_7149192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149231 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 2, 5, 2]
def baseStart_7149231 : Nat := 118140960795 + 7149231 * 2 ^ 59
def prefixEnd_7149231 : Nat := 4983230072969 + 3 ^ 40 * 7149231 * 2
def baseEnd_7149231 : Nat := 3670991813023823334533791

theorem tailTrace_7149231 : CollatzResearch.WordTrace tailWord_7149231 prefixEnd_7149231 3670991813023823334533791 := by
  unfold tailWord_7149231
  simp only [CollatzResearch.WordTrace]
  refine ⟨260753876362564553291815547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173835917575043035527877031 260753876362564553291815547)
  ·
    refine ⟨391130814543846829937723321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260753876362564553291815547 391130814543846829937723321)
    ·
      refine ⟨293348110907885122453292491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391130814543846829937723321 293348110907885122453292491)
      ·
        refine ⟨440022166361827683679938737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293348110907885122453292491 440022166361827683679938737)
        ·
          refine ⟨330016624771370762759954053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440022166361827683679938737 330016624771370762759954053)
          ·
            refine ⟨61878117144632018017491385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330016624771370762759954053 61878117144632018017491385)
            ·
              refine ⟨46408587858474013513118539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61878117144632018017491385 46408587858474013513118539)
              ·
                refine ⟨69612881787711020269677809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46408587858474013513118539 69612881787711020269677809)
                ·
                  refine ⟨52209661340783265202258357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69612881787711020269677809 52209661340783265202258357)
                  ·
                    refine ⟨4894655750698431112711721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52209661340783265202258357 4894655750698431112711721)
                    ·
                      refine ⟨3670991813023823334533791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894655750698431112711721 3670991813023823334533791)
                      ·
                        rfl

theorem cell23_7149231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5, 2].length) (baseStart_7149231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149231 prefixEnd_7149231 := by exact prefixLift 7149231
  have htrace : WordTrace (prefixWord ++ tailWord_7149231) baseStart_7149231 baseEnd_7149231 := by
    simpa [prefixWord, tailWord_7149231, baseEnd_7149231] using wordTrace_append hprefix tailTrace_7149231
  have hstable : (prefixWord ++ tailWord_7149231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149231).length < 2 ^ (prefixWord ++ tailWord_7149231).sum := by decide
  have hdescent : baseEnd_7149231 < baseStart_7149231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149234 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_7149234 : Nat := 118140960795 + 7149234 * 2 ^ 59
def prefixEnd_7149234 : Nat := 4983230072969 + 3 ^ 40 * 7149234 * 2
def baseEnd_7149234 : Nat := 3670993353465786822796277

theorem tailTrace_7149234 : CollatzResearch.WordTrace tailWord_7149234 prefixEnd_7149234 3670993353465786822796277 := by
  unfold tailWord_7149234
  simp only [CollatzResearch.WordTrace]
  refine ⟨65188496445388421201043689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173835990521035789869449837 65188496445388421201043689)
  ·
    refine ⟨48891372334041315900782767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65188496445388421201043689 48891372334041315900782767)
    ·
      refine ⟨73337058501061973851174151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48891372334041315900782767 73337058501061973851174151)
      ·
        refine ⟨110005587751592960776761227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73337058501061973851174151 110005587751592960776761227)
        ·
          refine ⟨165008381627389441165141841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110005587751592960776761227 165008381627389441165141841)
          ·
            refine ⟨123756286220542080873856381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165008381627389441165141841 123756286220542080873856381)
            ·
              refine ⟨46408607332703280327696143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123756286220542080873856381 46408607332703280327696143)
              ·
                refine ⟨69612910999054920491544215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46408607332703280327696143 69612910999054920491544215)
                ·
                  refine ⟨104419366498582380737316323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69612910999054920491544215 104419366498582380737316323)
                  ·
                    refine ⟨156629049747873571105974485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104419366498582380737316323 156629049747873571105974485)
                    ·
                      refine ⟨3670993353465786822796277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156629049747873571105974485 3670993353465786822796277)
                      ·
                        rfl

theorem cell23_7149234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_7149234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149234 prefixEnd_7149234 := by exact prefixLift 7149234
  have htrace : WordTrace (prefixWord ++ tailWord_7149234) baseStart_7149234 baseEnd_7149234 := by
    simpa [prefixWord, tailWord_7149234, baseEnd_7149234] using wordTrace_append hprefix tailTrace_7149234
  have hstable : (prefixWord ++ tailWord_7149234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149234).length < 2 ^ (prefixWord ++ tailWord_7149234).sum := by decide
  have hdescent : baseEnd_7149234 < baseStart_7149234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149258 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_7149258 : Nat := 118140960795 + 7149258 * 2 ^ 59
def prefixEnd_7149258 : Nat := 4983230072969 + 3 ^ 40 * 7149258 * 2
def baseEnd_7149258 : Nat := 1223668559000498242965389

theorem tailTrace_7149258 : CollatzResearch.WordTrace tailWord_7149258 prefixEnd_7149258 1223668559000498242965389 := by
  unfold tailWord_7149258
  simp only [CollatzResearch.WordTrace]
  refine ⟨65188715283366684225762107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173836574088977824602032285 65188715283366684225762107)
  ·
    refine ⟨97783072925050026338643161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65188715283366684225762107 97783072925050026338643161)
    ·
      refine ⟨73337304693787519753982371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97783072925050026338643161 73337304693787519753982371)
      ·
        refine ⟨110005957040681279630973557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73337304693787519753982371 110005957040681279630973557)
        ·
          refine ⟨10313058472563869965403771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110005957040681279630973557 10313058472563869965403771)
          ·
            refine ⟨15469587708845804948105657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313058472563869965403771 15469587708845804948105657)
            ·
              refine ⟨11602190781634353711079243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15469587708845804948105657 11602190781634353711079243)
              ·
                refine ⟨17403286172451530566618865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602190781634353711079243 17403286172451530566618865)
                ·
                  refine ⟨13052464629338647924964149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17403286172451530566618865 13052464629338647924964149)
                  ·
                    refine ⟨1223668559000498242965389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13052464629338647924964149 1223668559000498242965389)
                    ·
                      rfl

theorem cell23_7149258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_7149258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149258 prefixEnd_7149258 := by exact prefixLift 7149258
  have htrace : WordTrace (prefixWord ++ tailWord_7149258) baseStart_7149258 baseEnd_7149258 := by
    simpa [prefixWord, tailWord_7149258, baseEnd_7149258] using wordTrace_append hprefix tailTrace_7149258
  have hstable : (prefixWord ++ tailWord_7149258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149258).length < 2 ^ (prefixWord ++ tailWord_7149258).sum := by decide
  have hdescent : baseEnd_7149258 < baseStart_7149258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149304 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_7149304 : Nat := 118140960795 + 7149304 * 2 ^ 59
def prefixEnd_7149304 : Nat := 4983230072969 + 3 ^ 40 * 7149304 * 2
def baseEnd_7149304 : Nat := 3671029297111601548920955

theorem tailTrace_7149304 : CollatzResearch.WordTrace tailWord_7149304 prefixEnd_7149304 3671029297111601548920955 := by
  unfold tailWord_7149304
  simp only [CollatzResearch.WordTrace]
  refine ⟨130378269445650043379611483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173837692594200057839481977 130378269445650043379611483)
  ·
    refine ⟨195567404168475065069417225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130378269445650043379611483 195567404168475065069417225)
    ·
      refine ⟨146675553126356298802062919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195567404168475065069417225 146675553126356298802062919)
      ·
        refine ⟨220013329689534448203094379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146675553126356298802062919 220013329689534448203094379)
        ·
          refine ⟨330019994534301672304641569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220013329689534448203094379 330019994534301672304641569)
          ·
            refine ⟨247514995900726254228481177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330019994534301672304641569 247514995900726254228481177)
            ·
              refine ⟨185636246925544690671360883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247514995900726254228481177 185636246925544690671360883)
              ·
                refine ⟨278454370388317036007041325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185636246925544690671360883 278454370388317036007041325)
                ·
                  refine ⟨104420388895618888502640497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278454370388317036007041325 104420388895618888502640497)
                  ·
                    refine ⟨78315291671714166376980373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104420388895618888502640497 78315291671714166376980373)
                    ·
                      refine ⟨3671029297111601548920955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78315291671714166376980373 3671029297111601548920955)
                      ·
                        rfl

theorem cell23_7149304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_7149304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149304 prefixEnd_7149304 := by exact prefixLift 7149304
  have htrace : WordTrace (prefixWord ++ tailWord_7149304) baseStart_7149304 baseEnd_7149304 := by
    simpa [prefixWord, tailWord_7149304, baseEnd_7149304] using wordTrace_append hprefix tailTrace_7149304
  have hstable : (prefixWord ++ tailWord_7149304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149304).length < 2 ^ (prefixWord ++ tailWord_7149304).sum := by decide
  have hdescent : baseEnd_7149304 < baseStart_7149304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149345 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_7149345 : Nat := 118140960795 + 7149345 * 2 ^ 59
def prefixEnd_7149345 : Nat := 4983230072969 + 3 ^ 40 * 7149345 * 2
def baseEnd_7149345 : Nat := 3671050349818435888508267

theorem tailTrace_7149345 : CollatzResearch.WordTrace tailWord_7149345 prefixEnd_7149345 3671050349818435888508267 := by
  unfold tailWord_7149345
  simp only [CollatzResearch.WordTrace]
  refine ⟨260758034284151550761465489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173838689522767700507643659 260758034284151550761465489)
  ·
    refine ⟨195568525713113663071099117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260758034284151550761465489 195568525713113663071099117)
    ·
      refine ⟨73338197142417623651662169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195568525713113663071099117 73338197142417623651662169)
      ·
        refine ⟨55003647856813217738746627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73338197142417623651662169 55003647856813217738746627)
        ·
          refine ⟨82505471785219826608119941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55003647856813217738746627 82505471785219826608119941)
          ·
            refine ⟨15469775959728717489022489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82505471785219826608119941 15469775959728717489022489)
            ·
              refine ⟨11602331969796538116766867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15469775959728717489022489 11602331969796538116766867)
              ·
                refine ⟨17403497954694807175150301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602331969796538116766867 17403497954694807175150301)
                ·
                  refine ⟨6526311733010552690681363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17403497954694807175150301 6526311733010552690681363)
                  ·
                    refine ⟨9789467599515829036022045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6526311733010552690681363 9789467599515829036022045)
                    ·
                      refine ⟨3671050349818435888508267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9789467599515829036022045 3671050349818435888508267)
                      ·
                        rfl

theorem cell23_7149345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_7149345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149345 prefixEnd_7149345 := by exact prefixLift 7149345
  have htrace : WordTrace (prefixWord ++ tailWord_7149345) baseStart_7149345 baseEnd_7149345 := by
    simpa [prefixWord, tailWord_7149345, baseEnd_7149345] using wordTrace_append hprefix tailTrace_7149345
  have hstable : (prefixWord ++ tailWord_7149345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149345).length < 2 ^ (prefixWord ++ tailWord_7149345).sum := by decide
  have hdescent : baseEnd_7149345 < baseStart_7149345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149365 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_7149365 : Nat := 118140960795 + 7149365 * 2 ^ 59
def prefixEnd_7149365 : Nat := 4983230072969 + 3 ^ 40 * 7149365 * 2
def baseEnd_7149365 : Nat := 1223686873143841936752725

theorem tailTrace_7149365 : CollatzResearch.WordTrace tailWord_7149365 prefixEnd_7149365 1223686873143841936752725 := by
  unfold tailWord_7149365
  simp only [CollatzResearch.WordTrace]
  refine ⟨260758763744079094177193549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173839175829386062784795699 260758763744079094177193549)
  ·
    refine ⟨97784536404029660316447581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260758763744079094177193549 97784536404029660316447581)
    ·
      refine ⟨36669201151511122618667843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97784536404029660316447581 36669201151511122618667843)
      ·
        refine ⟨55003801727266683928001765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36669201151511122618667843 55003801727266683928001765)
        ·
          refine ⟨10313212823862503236500331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55003801727266683928001765 10313212823862503236500331)
          ·
            refine ⟨15469819235793754854750497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313212823862503236500331 15469819235793754854750497)
            ·
              refine ⟨11602364426845316141062873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15469819235793754854750497 11602364426845316141062873)
              ·
                refine ⟨8701773320133987105797155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602364426845316141062873 8701773320133987105797155)
                ·
                  refine ⟨13052659980200980658695733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701773320133987105797155 13052659980200980658695733)
                  ·
                    refine ⟨1223686873143841936752725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13052659980200980658695733 1223686873143841936752725)
                    ·
                      rfl

theorem cell23_7149365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_7149365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149365 prefixEnd_7149365 := by exact prefixLift 7149365
  have htrace : WordTrace (prefixWord ++ tailWord_7149365) baseStart_7149365 baseEnd_7149365 := by
    simpa [prefixWord, tailWord_7149365, baseEnd_7149365] using wordTrace_append hprefix tailTrace_7149365
  have hstable : (prefixWord ++ tailWord_7149365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149365).length < 2 ^ (prefixWord ++ tailWord_7149365).sum := by decide
  have hdescent : baseEnd_7149365 < baseStart_7149365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149368 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_7149368 : Nat := 118140960795 + 7149368 * 2 ^ 59
def prefixEnd_7149368 : Nat := 4983230072969 + 3 ^ 40 * 7149368 * 2
def baseEnd_7149368 : Nat := 3671062159873489298520661

theorem tailTrace_7149368 : CollatzResearch.WordTrace tailWord_7149368 prefixEnd_7149368 3671062159873489298520661 := by
  unfold tailWord_7149368
  simp only [CollatzResearch.WordTrace]
  refine ⟨130379436581534112844776379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173839248775378817126368505 130379436581534112844776379)
  ·
    refine ⟨195569154872301169267164569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130379436581534112844776379 195569154872301169267164569)
    ·
      refine ⟨146676866154225876950373427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195569154872301169267164569 146676866154225876950373427)
      ·
        refine ⟨220015299231338815425560141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146676866154225876950373427 220015299231338815425560141)
        ·
          refine ⟨82505737211752055784585053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220015299231338815425560141 82505737211752055784585053)
          ·
            refine ⟨30939651454407020919219395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82505737211752055784585053 30939651454407020919219395)
            ·
              refine ⟨46409477181610531378829093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30939651454407020919219395 46409477181610531378829093)
              ·
                refine ⟨8701776971551974633530455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46409477181610531378829093 8701776971551974633530455)
                ·
                  refine ⟨13052665457327961950295683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701776971551974633530455 13052665457327961950295683)
                  ·
                    refine ⟨19578998185991942925443525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13052665457327961950295683 19578998185991942925443525)
                    ·
                      refine ⟨3671062159873489298520661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19578998185991942925443525 3671062159873489298520661)
                      ·
                        rfl

theorem cell23_7149368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_7149368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149368 prefixEnd_7149368 := by exact prefixLift 7149368
  have htrace : WordTrace (prefixWord ++ tailWord_7149368) baseStart_7149368 baseEnd_7149368 := by
    simpa [prefixWord, tailWord_7149368, baseEnd_7149368] using wordTrace_append hprefix tailTrace_7149368
  have hstable : (prefixWord ++ tailWord_7149368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149368).length < 2 ^ (prefixWord ++ tailWord_7149368).sum := by decide
  have hdescent : baseEnd_7149368 < baseStart_7149368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149381 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_7149381 : Nat := 118140960795 + 7149381 * 2 ^ 59
def prefixEnd_7149381 : Nat := 4983230072969 + 3 ^ 40 * 7149381 * 2
def baseEnd_7149381 : Nat := 3671068835121997747658101

theorem tailTrace_7149381 : CollatzResearch.WordTrace tailWord_7149381 prefixEnd_7149381 3671068835121997747658101 := by
  unfold tailWord_7149381
  simp only [CollatzResearch.WordTrace]
  refine ⟨260759347312021128909775997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173839564874680752606517331 260759347312021128909775997)
  ·
    refine ⟨97784755242007923341165999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260759347312021128909775997 97784755242007923341165999)
    ·
      refine ⟨146677132863011885011748999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97784755242007923341165999 146677132863011885011748999)
      ·
        refine ⟨220015699294517827517623499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146677132863011885011748999 220015699294517827517623499)
        ·
          refine ⟨330023548941776741276435249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220015699294517827517623499 330023548941776741276435249)
          ·
            refine ⟨247517661706332555957326437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330023548941776741276435249 247517661706332555957326437)
            ·
              refine ⟨46409561569937354241998707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247517661706332555957326437 46409561569937354241998707)
              ·
                refine ⟨69614342354906031362998061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46409561569937354241998707 69614342354906031362998061)
                ·
                  refine ⟨26105378383089761761124273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69614342354906031362998061 26105378383089761761124273)
                  ·
                    refine ⟨19579033787317321320843205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26105378383089761761124273 19579033787317321320843205)
                    ·
                      refine ⟨3671068835121997747658101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19579033787317321320843205 3671068835121997747658101)
                      ·
                        rfl

theorem cell23_7149381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_7149381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149381 prefixEnd_7149381 := by exact prefixLift 7149381
  have htrace : WordTrace (prefixWord ++ tailWord_7149381) baseStart_7149381 baseEnd_7149381 := by
    simpa [prefixWord, tailWord_7149381, baseEnd_7149381] using wordTrace_append hprefix tailTrace_7149381
  have hstable : (prefixWord ++ tailWord_7149381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149381).length < 2 ^ (prefixWord ++ tailWord_7149381).sum := by decide
  have hdescent : baseEnd_7149381 < baseStart_7149381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149382 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_7149382 : Nat := 118140960795 + 7149382 * 2 ^ 59
def prefixEnd_7149382 : Nat := 4983230072969 + 3 ^ 40 * 7149382 * 2
def baseEnd_7149382 : Nat := 1223689782867550747915199

theorem tailTrace_7149382 : CollatzResearch.WordTrace tailWord_7149382 prefixEnd_7149382 1223689782867550747915199 := by
  unfold tailWord_7149382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8148730743281797065017575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173839589190011670720374933 8148730743281797065017575)
  ·
    refine ⟨12223096114922695597526363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8148730743281797065017575 12223096114922695597526363)
    ·
      refine ⟨18334644172384043396289545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223096114922695597526363 18334644172384043396289545)
      ·
        refine ⟨13750983129288032547217159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18334644172384043396289545 13750983129288032547217159)
        ·
          refine ⟨20626474693932048820825739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13750983129288032547217159 20626474693932048820825739)
          ·
            refine ⟨30939712040898073231238609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20626474693932048820825739 30939712040898073231238609)
            ·
              refine ⟨23204784030673554923428957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30939712040898073231238609 23204784030673554923428957)
              ·
                refine ⟨8701794011502583096285859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23204784030673554923428957 8701794011502583096285859)
                ·
                  refine ⟨13052691017253874644428789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701794011502583096285859 13052691017253874644428789)
                  ·
                    refine ⟨1223689782867550747915199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13052691017253874644428789 1223689782867550747915199)
                    ·
                      rfl

theorem cell23_7149382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_7149382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149382 prefixEnd_7149382 := by exact prefixLift 7149382
  have htrace : WordTrace (prefixWord ++ tailWord_7149382) baseStart_7149382 baseEnd_7149382 := by
    simpa [prefixWord, tailWord_7149382, baseEnd_7149382] using wordTrace_append hprefix tailTrace_7149382
  have hstable : (prefixWord ++ tailWord_7149382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149382).length < 2 ^ (prefixWord ++ tailWord_7149382).sum := by decide
  have hdescent : baseEnd_7149382 < baseStart_7149382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149422 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_7149422 : Nat := 118140960795 + 7149422 * 2 ^ 59
def prefixEnd_7149422 : Nat := 4983230072969 + 3 ^ 40 * 7149422 * 2
def baseEnd_7149422 : Nat := 3671089887828832087245413

theorem tailTrace_7149422 : CollatzResearch.WordTrace tailWord_7149422 prefixEnd_7149422 3671089887828832087245413 := by
  unfold tailWord_7149422
  simp only [CollatzResearch.WordTrace]
  refine ⟨32595105338109074114002315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173840561803248395274679013 32595105338109074114002315)
  ·
    refine ⟨48892658007163611171003473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32595105338109074114002315 48892658007163611171003473)
    ·
      refine ⟨36669493505372708378252605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48892658007163611171003473 36669493505372708378252605)
      ·
        refine ⟨13751060064514765641844727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36669493505372708378252605 13751060064514765641844727)
        ·
          refine ⟨20626590096772148462767091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13751060064514765641844727 20626590096772148462767091)
          ·
            refine ⟨30939885145158222694150637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20626590096772148462767091 30939885145158222694150637)
            ·
              refine ⟨11602456929434333510306489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30939885145158222694150637 11602456929434333510306489)
              ·
                refine ⟨8701842697075750132729867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602456929434333510306489 8701842697075750132729867)
                ·
                  refine ⟨13052764045613625199094801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701842697075750132729867 13052764045613625199094801)
                  ·
                    refine ⟨9789573034210218899321101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13052764045613625199094801 9789573034210218899321101)
                    ·
                      refine ⟨3671089887828832087245413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9789573034210218899321101 3671089887828832087245413)
                      ·
                        rfl

theorem cell23_7149422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_7149422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149422 prefixEnd_7149422 := by exact prefixLift 7149422
  have htrace : WordTrace (prefixWord ++ tailWord_7149422) baseStart_7149422 baseEnd_7149422 := by
    simpa [prefixWord, tailWord_7149422, baseEnd_7149422] using wordTrace_append hprefix tailTrace_7149422
  have hstable : (prefixWord ++ tailWord_7149422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149422).length < 2 ^ (prefixWord ++ tailWord_7149422).sum := by decide
  have hdescent : baseEnd_7149422 < baseStart_7149422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149451 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 2, 6]
def baseStart_7149451 : Nat := 118140960795 + 7149451 * 2 ^ 59
def prefixEnd_7149451 : Nat := 4983230072969 + 3 ^ 40 * 7149451 * 2
def baseEnd_7149451 : Nat := 1223701592922604157927593

theorem tailTrace_7149451 : CollatzResearch.WordTrace tailWord_7149451 prefixEnd_7149451 1223701592922604157927593 := by
  unfold tailWord_7149451
  simp only [CollatzResearch.WordTrace]
  refine ⟨260761900421767530864824207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173841266947845020576549471 260761900421767530864824207)
  ·
    refine ⟨391142850632651296297236311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260761900421767530864824207 391142850632651296297236311)
    ·
      refine ⟨586714275948976944445854467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391142850632651296297236311 586714275948976944445854467)
      ·
        refine ⟨880071413923465416668781701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586714275948976944445854467 880071413923465416668781701)
        ·
          refine ⟨165013390110649765625396569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 880071413923465416668781701 165013390110649765625396569)
          ·
            refine ⟨123760042582987324219047427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165013390110649765625396569 123760042582987324219047427)
            ·
              refine ⟨185640063874480986328571141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123760042582987324219047427 185640063874480986328571141)
              ·
                refine ⟨34807511976465184936607089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185640063874480986328571141 34807511976465184936607089)
                ·
                  refine ⟨26105633982348888702455317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34807511976465184936607089 26105633982348888702455317)
                  ·
                    refine ⟨1223701592922604157927593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26105633982348888702455317 1223701592922604157927593)
                    ·
                      rfl

theorem cell23_7149451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 6].length) (baseStart_7149451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149451 prefixEnd_7149451 := by exact prefixLift 7149451
  have htrace : WordTrace (prefixWord ++ tailWord_7149451) baseStart_7149451 baseEnd_7149451 := by
    simpa [prefixWord, tailWord_7149451, baseEnd_7149451] using wordTrace_append hprefix tailTrace_7149451
  have hstable : (prefixWord ++ tailWord_7149451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149451).length < 2 ^ (prefixWord ++ tailWord_7149451).sum := by decide
  have hdescent : baseEnd_7149451 < baseStart_7149451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149468 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_7149468 : Nat := 118140960795 + 7149468 * 2 ^ 59
def prefixEnd_7149468 : Nat := 4983230072969 + 3 ^ 40 * 7149468 * 2
def baseEnd_7149468 : Nat := 1223704502646312969090067

theorem tailTrace_7149468 : CollatzResearch.WordTrace tailWord_7149468 prefixEnd_7149468 1223704502646312969090067 := by
  unfold tailWord_7149468
  simp only [CollatzResearch.WordTrace]
  refine ⟨130381260231352971384096529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173841680308470628512128705 130381260231352971384096529)
  ·
    refine ⟨97785945173514728538072397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130381260231352971384096529 97785945173514728538072397)
    ·
      refine ⟨36669729440068023201777149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97785945173514728538072397 36669729440068023201777149)
      ·
        refine ⟨13751148540025508700666431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36669729440068023201777149 13751148540025508700666431)
        ·
          refine ⟨20626722810038263050999647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13751148540025508700666431 20626722810038263050999647)
          ·
            refine ⟨30940084215057394576499471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20626722810038263050999647 30940084215057394576499471)
            ·
              refine ⟨46410126322586091864749207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30940084215057394576499471 46410126322586091864749207)
              ·
                refine ⟨69615189483879137797123811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46410126322586091864749207 69615189483879137797123811)
                ·
                  refine ⟨104422784225818706695685717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69615189483879137797123811 104422784225818706695685717)
                  ·
                    refine ⟨1223704502646312969090067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104422784225818706695685717 1223704502646312969090067)
                    ·
                      rfl

theorem cell23_7149468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_7149468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149468 prefixEnd_7149468 := by exact prefixLift 7149468
  have htrace : WordTrace (prefixWord ++ tailWord_7149468) baseStart_7149468 baseEnd_7149468 := by
    simpa [prefixWord, tailWord_7149468, baseEnd_7149468] using wordTrace_append hprefix tailTrace_7149468
  have hstable : (prefixWord ++ tailWord_7149468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149468).length < 2 ^ (prefixWord ++ tailWord_7149468).sum := by decide
  have hdescent : baseEnd_7149468 < baseStart_7149468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149475 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 6, 2, 2]
def baseStart_7149475 : Nat := 118140960795 + 7149475 * 2 ^ 59
def prefixEnd_7149475 : Nat := 4983230072969 + 3 ^ 40 * 7149475 * 2
def baseEnd_7149475 : Nat := 3671117102303520379882669

theorem tailTrace_7149475 : CollatzResearch.WordTrace tailWord_7149475 prefixEnd_7149475 3671117102303520379882669 := by
  unfold tailWord_7149475
  simp only [CollatzResearch.WordTrace]
  refine ⟨260762775773680582963697879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173841850515787055309131919 260762775773680582963697879)
  ·
    refine ⟨391144163660520874445546819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260762775773680582963697879 391144163660520874445546819)
    ·
      refine ⟨586716245490781311668320229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391144163660520874445546819 586716245490781311668320229)
      ·
        refine ⟨110009296029521495937810043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 586716245490781311668320229 110009296029521495937810043)
        ·
          refine ⟨165013944044282243906715065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110009296029521495937810043 165013944044282243906715065)
          ·
            refine ⟨123760458033211682930036299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165013944044282243906715065 123760458033211682930036299)
            ·
              refine ⟨185640687049817524395054449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123760458033211682930036299 185640687049817524395054449)
              ·
                refine ⟨139230515287363143296290837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185640687049817524395054449 139230515287363143296290837)
                ·
                  refine ⟨6526430404095147342013633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139230515287363143296290837 6526430404095147342013633)
                  ·
                    refine ⟨4894822803071360506510225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6526430404095147342013633 4894822803071360506510225)
                    ·
                      refine ⟨3671117102303520379882669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894822803071360506510225 3671117102303520379882669)
                      ·
                        rfl

theorem cell23_7149475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_7149475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149475 prefixEnd_7149475 := by exact prefixLift 7149475
  have htrace : WordTrace (prefixWord ++ tailWord_7149475) baseStart_7149475 baseEnd_7149475 := by
    simpa [prefixWord, tailWord_7149475, baseEnd_7149475] using wordTrace_append hprefix tailTrace_7149475
  have hstable : (prefixWord ++ tailWord_7149475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149475).length < 2 ^ (prefixWord ++ tailWord_7149475).sum := by decide
  have hdescent : baseEnd_7149475 < baseStart_7149475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149525 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_7149525 : Nat := 118140960795 + 7149525 * 2 ^ 59
def prefixEnd_7149525 : Nat := 4983230072969 + 3 ^ 40 * 7149525 * 2
def baseEnd_7149525 : Nat := 3671142776336245184257439

theorem tailTrace_7149525 : CollatzResearch.WordTrace tailWord_7149525 prefixEnd_7149525 3671142776336245184257439 := by
  unfold tailWord_7149525
  simp only [CollatzResearch.WordTrace]
  refine ⟨260764599423499441503018029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173843066282332961002012019 260764599423499441503018029)
  ·
    refine ⟨97786724783812290563631761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260764599423499441503018029 97786724783812290563631761)
    ·
      refine ⟨73340043587859217922723821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97786724783812290563631761 73340043587859217922723821)
      ·
        refine ⟨27502516345447206721021433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73340043587859217922723821 27502516345447206721021433)
        ·
          refine ⟨20626887259085405040766075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27502516345447206721021433 20626887259085405040766075)
          ·
            refine ⟨30940330888628107561149113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20626887259085405040766075 30940330888628107561149113)
            ·
              refine ⟨23205248166471080670861835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30940330888628107561149113 23205248166471080670861835)
              ·
                refine ⟨34807872249706621006292753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23205248166471080670861835 34807872249706621006292753)
                ·
                  refine ⟨26105904187279965754719565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34807872249706621006292753 26105904187279965754719565)
                  ·
                    refine ⟨9789714070229987158019837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26105904187279965754719565 9789714070229987158019837)
                    ·
                      refine ⟨3671142776336245184257439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9789714070229987158019837 3671142776336245184257439)
                      ·
                        rfl

theorem cell23_7149525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_7149525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149525 prefixEnd_7149525 := by exact prefixLift 7149525
  have htrace : WordTrace (prefixWord ++ tailWord_7149525) baseStart_7149525 baseEnd_7149525 := by
    simpa [prefixWord, tailWord_7149525, baseEnd_7149525] using wordTrace_append hprefix tailTrace_7149525
  have hstable : (prefixWord ++ tailWord_7149525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149525).length < 2 ^ (prefixWord ++ tailWord_7149525).sum := by decide
  have hdescent : baseEnd_7149525 < baseStart_7149525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149526 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7149526 : Nat := 118140960795 + 7149526 * 2 ^ 59
def prefixEnd_7149526 : Nat := 4983230072969 + 3 ^ 40 * 7149526 * 2
def baseEnd_7149526 : Nat := 3671143289816899680344935

theorem tailTrace_7149526 : CollatzResearch.WordTrace tailWord_7149526 prefixEnd_7149526 3671143289816899680344935 := by
  unfold tailWord_7149526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297789743530988667112777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173843090597663879115869621 16297789743530988667112777)
  ·
    refine ⟨12223342307648241500334583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16297789743530988667112777 12223342307648241500334583)
    ·
      refine ⟨18335013461472362250501875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223342307648241500334583 18335013461472362250501875)
      ·
        refine ⟨27502520192208543375752813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18335013461472362250501875 27502520192208543375752813)
        ·
          refine ⟨10313445072078203765907305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27502520192208543375752813 10313445072078203765907305)
          ·
            refine ⟨7735083804058652824430479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313445072078203765907305 7735083804058652824430479)
            ·
              refine ⟨11602625706087979236645719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735083804058652824430479 11602625706087979236645719)
              ·
                refine ⟨17403938559131968854968579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602625706087979236645719 17403938559131968854968579)
                ·
                  refine ⟨26105907838697953282452869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17403938559131968854968579 26105907838697953282452869)
                  ·
                    refine ⟨4894857719755866240459913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26105907838697953282452869 4894857719755866240459913)
                    ·
                      refine ⟨3671143289816899680344935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894857719755866240459913 3671143289816899680344935)
                      ·
                        rfl

theorem cell23_7149526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7149526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149526 prefixEnd_7149526 := by exact prefixLift 7149526
  have htrace : WordTrace (prefixWord ++ tailWord_7149526) baseStart_7149526 baseEnd_7149526 := by
    simpa [prefixWord, tailWord_7149526, baseEnd_7149526] using wordTrace_append hprefix tailTrace_7149526
  have hstable : (prefixWord ++ tailWord_7149526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149526).length < 2 ^ (prefixWord ++ tailWord_7149526).sum := by decide
  have hdescent : baseEnd_7149526 < baseStart_7149526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149548 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_7149548 : Nat := 118140960795 + 7149548 * 2 ^ 59
def prefixEnd_7149548 : Nat := 4983230072969 + 3 ^ 40 * 7149548 * 2
def baseEnd_7149548 : Nat := 3671154586391298594269833

theorem tailTrace_7149548 : CollatzResearch.WordTrace tailWord_7149548 prefixEnd_7149548 3671154586391298594269833 := by
  unfold tailWord_7149548
  simp only [CollatzResearch.WordTrace]
  refine ⟨130382719151208058215552649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173843625534944077620736865 130382719151208058215552649)
  ·
    refine ⟨97787039363406043661664487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130382719151208058215552649 97787039363406043661664487)
    ·
      refine ⟨146680559045109065492496731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97787039363406043661664487 146680559045109065492496731)
      ·
        refine ⟨220020838567663598238745097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146680559045109065492496731 220020838567663598238745097)
        ·
          refine ⟨165015628925747698679058823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220020838567663598238745097 165015628925747698679058823)
          ·
            refine ⟨247523443388621548018588235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165015628925747698679058823 247523443388621548018588235)
            ·
              refine ⟨371285165082932322027882353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247523443388621548018588235 371285165082932322027882353)
              ·
                refine ⟨278463873812199241520911765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371285165082932322027882353 278463873812199241520911765)
                ·
                  refine ⟨13052994084946839446292739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 278463873812199241520911765 13052994084946839446292739)
                  ·
                    refine ⟨19579491127420259169439109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13052994084946839446292739 19579491127420259169439109)
                    ·
                      refine ⟨3671154586391298594269833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19579491127420259169439109 3671154586391298594269833)
                      ·
                        rfl

theorem cell23_7149548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_7149548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149548 prefixEnd_7149548 := by exact prefixLift 7149548
  have htrace : WordTrace (prefixWord ++ tailWord_7149548) baseStart_7149548 baseEnd_7149548 := by
    simpa [prefixWord, tailWord_7149548, baseEnd_7149548] using wordTrace_append hprefix tailTrace_7149548
  have hstable : (prefixWord ++ tailWord_7149548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149548).length < 2 ^ (prefixWord ++ tailWord_7149548).sum := by decide
  have hdescent : baseEnd_7149548 < baseStart_7149548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149565 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_7149565 : Nat := 118140960795 + 7149565 * 2 ^ 59
def prefixEnd_7149565 : Nat := 4983230072969 + 3 ^ 40 * 7149565 * 2
def baseEnd_7149565 : Nat := 3671163315562425027757255

theorem tailTrace_7149565 : CollatzResearch.WordTrace tailWord_7149565 prefixEnd_7149565 3671163315562425027757255 := by
  unfold tailWord_7149565
  simp only [CollatzResearch.WordTrace]
  refine ⟨260766058343354528334474149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173844038895569685556316099 260766058343354528334474149)
  ·
    refine ⟨48893635939378974062713903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260766058343354528334474149 48893635939378974062713903)
    ·
      refine ⟨73340453909068461094070855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48893635939378974062713903 73340453909068461094070855)
      ·
        refine ⟨110010680863602691641106283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73340453909068461094070855 110010680863602691641106283)
        ·
          refine ⟨165016021295404037461659425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110010680863602691641106283 165016021295404037461659425)
          ·
            refine ⟨123762015971553028096244569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165016021295404037461659425 123762015971553028096244569)
            ·
              refine ⟨92821511978664771072183427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123762015971553028096244569 92821511978664771072183427)
              ·
                refine ⟨139232267967997156608275141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92821511978664771072183427 139232267967997156608275141)
                ·
                  refine ⟨26106050243999466864051589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139232267967997156608275141 26106050243999466864051589)
                  ·
                    refine ⟨4894884420749900037009673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26106050243999466864051589 4894884420749900037009673)
                    ·
                      refine ⟨3671163315562425027757255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894884420749900037009673 3671163315562425027757255)
                      ·
                        rfl

theorem cell23_7149565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_7149565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149565 prefixEnd_7149565 := by exact prefixLift 7149565
  have htrace : WordTrace (prefixWord ++ tailWord_7149565) baseStart_7149565 baseEnd_7149565 := by
    simpa [prefixWord, tailWord_7149565, baseEnd_7149565] using wordTrace_append hprefix tailTrace_7149565
  have hstable : (prefixWord ++ tailWord_7149565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149565).length < 2 ^ (prefixWord ++ tailWord_7149565).sum := by decide
  have hdescent : baseEnd_7149565 < baseStart_7149565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149568 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3]
def baseStart_7149568 : Nat := 118140960795 + 7149568 * 2 ^ 59
def prefixEnd_7149568 : Nat := 4983230072969 + 3 ^ 40 * 7149568 * 2
def baseEnd_7149568 : Nat := 3671164856004388516019741

theorem tailTrace_7149568 : CollatzResearch.WordTrace tailWord_7149568 prefixEnd_7149568 3671164856004388516019741 := by
  unfold tailWord_7149568
  simp only [CollatzResearch.WordTrace]
  refine ⟨130383083881171829923416679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173844111841562439897888905 130383083881171829923416679)
  ·
    refine ⟨195574625821757744885125019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130383083881171829923416679 195574625821757744885125019)
    ·
      refine ⟨293361938732636617327687529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195574625821757744885125019 293361938732636617327687529)
      ·
        refine ⟨220021454049477462995765647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293361938732636617327687529 220021454049477462995765647)
        ·
          refine ⟨330032181074216194493648471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220021454049477462995765647 330032181074216194493648471)
          ·
            refine ⟨495048271611324291740472707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330032181074216194493648471 495048271611324291740472707)
            ·
              refine ⟨742572407416986437610709061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495048271611324291740472707 742572407416986437610709061)
              ·
                refine ⟨139232326390684957052007949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742572407416986437610709061 139232326390684957052007949)
                ·
                  refine ⟨52212122396506858894502981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139232326390684957052007949 52212122396506858894502981)
                  ·
                    refine ⟨9789772949345036042719309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52212122396506858894502981 9789772949345036042719309)
                    ·
                      refine ⟨3671164856004388516019741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9789772949345036042719309 3671164856004388516019741)
                      ·
                        rfl

theorem cell23_7149568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_7149568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149568 prefixEnd_7149568 := by exact prefixLift 7149568
  have htrace : WordTrace (prefixWord ++ tailWord_7149568) baseStart_7149568 baseEnd_7149568 := by
    simpa [prefixWord, tailWord_7149568, baseEnd_7149568] using wordTrace_append hprefix tailTrace_7149568
  have hstable : (prefixWord ++ tailWord_7149568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149568).length < 2 ^ (prefixWord ++ tailWord_7149568).sum := by decide
  have hdescent : baseEnd_7149568 < baseStart_7149568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149572 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7149572 : Nat := 118140960795 + 7149572 * 2 ^ 59
def prefixEnd_7149572 : Nat := 4983230072969 + 3 ^ 40 * 7149572 * 2
def baseEnd_7149572 : Nat := 3671166909927006500369723

theorem tailTrace_7149572 : CollatzResearch.WordTrace tailWord_7149572 prefixEnd_7149572 3671166909927006500369723 := by
  unfold tailWord_7149572
  simp only [CollatzResearch.WordTrace]
  refine ⟨130383156827164584264989485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173844209102886112353319313 130383156827164584264989485)
  ·
    refine ⟨48893683810186719099371057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130383156827164584264989485 48893683810186719099371057)
    ·
      refine ⟨36670262857640039324528293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48893683810186719099371057 36670262857640039324528293)
      ·
        refine ⟨6875674285807507373349055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36670262857640039324528293 6875674285807507373349055)
        ·
          refine ⟨10313511428711261060023583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875674285807507373349055 10313511428711261060023583)
          ·
            refine ⟨15470267143066891590035375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313511428711261060023583 15470267143066891590035375)
            ·
              refine ⟨23205400714600337385053063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15470267143066891590035375 23205400714600337385053063)
              ·
                refine ⟨34808101071900506077579595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23205400714600337385053063 34808101071900506077579595)
                ·
                  refine ⟨52212151607850759116369393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34808101071900506077579595 52212151607850759116369393)
                  ·
                    refine ⟨39159113705888069337277045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52212151607850759116369393 39159113705888069337277045)
                    ·
                      refine ⟨3671166909927006500369723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39159113705888069337277045 3671166909927006500369723)
                      ·
                        rfl

theorem cell23_7149572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7149572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149572 prefixEnd_7149572 := by exact prefixLift 7149572
  have htrace : WordTrace (prefixWord ++ tailWord_7149572) baseStart_7149572 baseEnd_7149572 := by
    simpa [prefixWord, tailWord_7149572, baseEnd_7149572] using wordTrace_append hprefix tailTrace_7149572
  have hstable : (prefixWord ++ tailWord_7149572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149572).length < 2 ^ (prefixWord ++ tailWord_7149572).sum := by decide
  have hdescent : baseEnd_7149572 < baseStart_7149572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149602 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_7149602 : Nat := 118140960795 + 7149602 * 2 ^ 59
def prefixEnd_7149602 : Nat := 4983230072969 + 3 ^ 40 * 7149602 * 2
def baseEnd_7149602 : Nat := 3671182314346641382994585

theorem tailTrace_7149602 : CollatzResearch.WordTrace tailWord_7149602 prefixEnd_7149602 3671182314346641382994585 := by
  unfold tailWord_7149602
  simp only [CollatzResearch.WordTrace]
  refine ⟨65191851961055120913392765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173844938562813655769047373 65191851961055120913392765)
  ·
    refine ⟨24446944485395670342522287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65191851961055120913392765 24446944485395670342522287)
    ·
      refine ⟨36670416728093505513783431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24446944485395670342522287 36670416728093505513783431)
      ·
        refine ⟨55005625092140258270675147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36670416728093505513783431 55005625092140258270675147)
        ·
          refine ⟨82508437638210387406012721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55005625092140258270675147 82508437638210387406012721)
          ·
            refine ⟨61881328228657790554509541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82508437638210387406012721 61881328228657790554509541)
            ·
              refine ⟨11602749042873335728970539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61881328228657790554509541 11602749042873335728970539)
              ·
                refine ⟨17404123564310003593455809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602749042873335728970539 17404123564310003593455809)
                ·
                  refine ⟨13053092673232502695091857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17404123564310003593455809 13053092673232502695091857)
                  ·
                    refine ⟨9789819504924377021318893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13053092673232502695091857 9789819504924377021318893)
                    ·
                      refine ⟨3671182314346641382994585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9789819504924377021318893 3671182314346641382994585)
                      ·
                        rfl

theorem cell23_7149602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_7149602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149602 prefixEnd_7149602 := by exact prefixLift 7149602
  have htrace : WordTrace (prefixWord ++ tailWord_7149602) baseStart_7149602 baseEnd_7149602 := by
    simpa [prefixWord, tailWord_7149602, baseEnd_7149602] using wordTrace_append hprefix tailTrace_7149602
  have hstable : (prefixWord ++ tailWord_7149602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149602).length < 2 ^ (prefixWord ++ tailWord_7149602).sum := by decide
  have hdescent : baseEnd_7149602 < baseStart_7149602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149615 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 3]
def baseStart_7149615 : Nat := 118140960795 + 7149615 * 2 ^ 59
def prefixEnd_7149615 : Nat := 4983230072969 + 3 ^ 40 * 7149615 * 2
def baseEnd_7149615 : Nat := 3671188989595149832132025

theorem tailTrace_7149615 : CollatzResearch.WordTrace tailWord_7149615 prefixEnd_7149615 3671188989595149832132025 := by
  unfold tailWord_7149615
  simp only [CollatzResearch.WordTrace]
  refine ⟨260767881993173386873794299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173845254662115591249196199 260767881993173386873794299)
  ·
    refine ⟨391151822989760080310691449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260767881993173386873794299 391151822989760080310691449)
    ·
      refine ⟨293363867242320060233018587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391151822989760080310691449 293363867242320060233018587)
      ·
        refine ⟨440045800863480090349527881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293363867242320060233018587 440045800863480090349527881)
        ·
          refine ⟨330034350647610067762145911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440045800863480090349527881 330034350647610067762145911)
          ·
            refine ⟨495051525971415101643218867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330034350647610067762145911 495051525971415101643218867)
            ·
              refine ⟨742577288957122652464828301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495051525971415101643218867 742577288957122652464828301)
              ·
                refine ⟨278466483358920994674310613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742577288957122652464828301 278466483358920994674310613)
                ·
                  refine ⟨6526558203724710812679155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 278466483358920994674310613 6526558203724710812679155)
                  ·
                    refine ⟨9789837305587066219018733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6526558203724710812679155 9789837305587066219018733)
                    ·
                      refine ⟨3671188989595149832132025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9789837305587066219018733 3671188989595149832132025)
                      ·
                        rfl

theorem cell23_7149615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 3].length) (baseStart_7149615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149615 prefixEnd_7149615 := by exact prefixLift 7149615
  have htrace : WordTrace (prefixWord ++ tailWord_7149615) baseStart_7149615 baseEnd_7149615 := by
    simpa [prefixWord, tailWord_7149615, baseEnd_7149615] using wordTrace_append hprefix tailTrace_7149615
  have hstable : (prefixWord ++ tailWord_7149615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149615).length < 2 ^ (prefixWord ++ tailWord_7149615).sum := by decide
  have hdescent : baseEnd_7149615 < baseStart_7149615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149622 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_7149622 : Nat := 118140960795 + 7149622 * 2 ^ 59
def prefixEnd_7149622 : Nat := 4983230072969 + 3 ^ 40 * 7149622 * 2
def baseEnd_7149622 : Nat := 407910287106636811638277

theorem tailTrace_7149622 : CollatzResearch.WordTrace tailWord_7149622 prefixEnd_7149622 407910287106636811638277 := by
  unfold tailWord_7149622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16298008581509251691831195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173845424869432018046199413 16298008581509251691831195)
  ·
    refine ⟨24447012872263877537746793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16298008581509251691831195 24447012872263877537746793)
    ·
      refine ⟨18335259654197908153310095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24447012872263877537746793 18335259654197908153310095)
      ·
        refine ⟨27502889481296862229965143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18335259654197908153310095 27502889481296862229965143)
        ·
          refine ⟨41254334221945293344947715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27502889481296862229965143 41254334221945293344947715)
          ·
            refine ⟨61881501332917940017421573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41254334221945293344947715 61881501332917940017421573)
            ·
              refine ⟨11602781499922113753266545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61881501332917940017421573 11602781499922113753266545)
              ·
                refine ⟨8702086124941585314949909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11602781499922113753266545 8702086124941585314949909)
                ·
                  refine ⟨407910287106636811638277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8702086124941585314949909 407910287106636811638277)
                  ·
                    rfl

theorem cell23_7149622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_7149622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149622 prefixEnd_7149622 := by exact prefixLift 7149622
  have htrace : WordTrace (prefixWord ++ tailWord_7149622) baseStart_7149622 baseEnd_7149622 := by
    simpa [prefixWord, tailWord_7149622, baseEnd_7149622] using wordTrace_append hprefix tailTrace_7149622
  have hstable : (prefixWord ++ tailWord_7149622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149622).length < 2 ^ (prefixWord ++ tailWord_7149622).sum := by decide
  have hdescent : baseEnd_7149622 < baseStart_7149622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149645 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7149645 : Nat := 118140960795 + 7149645 * 2 ^ 59
def prefixEnd_7149645 : Nat := 4983230072969 + 3 ^ 40 * 7149645 * 2
def baseEnd_7149645 : Nat := 3671204394014784714756887

theorem tailTrace_7149645 : CollatzResearch.WordTrace tailWord_7149645 prefixEnd_7149645 3671204394014784714756887 := by
  unfold tailWord_7149645
  simp only [CollatzResearch.WordTrace]
  refine ⟨260768976183064701997386389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173845984122043134664924259 260768976183064701997386389)
  ·
    refine ⟨12223545758581157906127487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260768976183064701997386389 12223545758581157906127487)
    ·
      refine ⟨18335318637871736859191231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223545758581157906127487 18335318637871736859191231)
      ·
        refine ⟨27502977956807605288786847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18335318637871736859191231 27502977956807605288786847)
        ·
          refine ⟨41254466935211407933180271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27502977956807605288786847 41254466935211407933180271)
          ·
            refine ⟨61881700402817111899770407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41254466935211407933180271 61881700402817111899770407)
            ·
              refine ⟨92822550604225667849655611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61881700402817111899770407 92822550604225667849655611)
              ·
                refine ⟨139233825906338501774483417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92822550604225667849655611 139233825906338501774483417)
                ·
                  refine ⟨104425369429753876330862563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139233825906338501774483417 104425369429753876330862563)
                  ·
                    refine ⟨156638054144630814496293845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104425369429753876330862563 156638054144630814496293845)
                    ·
                      refine ⟨3671204394014784714756887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156638054144630814496293845 3671204394014784714756887)
                      ·
                        rfl

theorem cell23_7149645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7149645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149645 prefixEnd_7149645 := by exact prefixLift 7149645
  have htrace : WordTrace (prefixWord ++ tailWord_7149645) baseStart_7149645 baseEnd_7149645 := by
    simpa [prefixWord, tailWord_7149645, baseEnd_7149645] using wordTrace_append hprefix tailTrace_7149645
  have hstable : (prefixWord ++ tailWord_7149645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149645).length < 2 ^ (prefixWord ++ tailWord_7149645).sum := by decide
  have hdescent : baseEnd_7149645 < baseStart_7149645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149655 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_7149655 : Nat := 118140960795 + 7149655 * 2 ^ 59
def prefixEnd_7149655 : Nat := 4983230072969 + 3 ^ 40 * 7149655 * 2
def baseEnd_7149655 : Nat := 3671209528821329675631841

theorem tailTrace_7149655 : CollatzResearch.WordTrace tailWord_7149655 prefixEnd_7149655 3671209528821329675631841 := by
  unfold tailWord_7149655
  simp only [CollatzResearch.WordTrace]
  refine ⟨260769340913028473705250419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173846227275352315803500279 260769340913028473705250419)
  ·
    refine ⟨391154011369542710557875629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260769340913028473705250419 391154011369542710557875629)
    ·
      refine ⟨146682754263578516459203361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391154011369542710557875629 146682754263578516459203361)
      ·
        refine ⟨110012065697683887344402521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146682754263578516459203361 110012065697683887344402521)
        ·
          refine ⟨82509049273262915508301891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110012065697683887344402521 82509049273262915508301891)
          ·
            refine ⟨123763573909894373262452837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82509049273262915508301891 123763573909894373262452837)
            ·
              refine ⟨23205670108105194986709907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123763573909894373262452837 23205670108105194986709907)
              ·
                refine ⟨34808505162157792480064861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23205670108105194986709907 34808505162157792480064861)
                ·
                  refine ⟨13053189435809172180024323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34808505162157792480064861 13053189435809172180024323)
                  ·
                    refine ⟨19579784153713758270036485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13053189435809172180024323 19579784153713758270036485)
                    ·
                      refine ⟨3671209528821329675631841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19579784153713758270036485 3671209528821329675631841)
                      ·
                        rfl

theorem cell23_7149655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_7149655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149655 prefixEnd_7149655 := by exact prefixLift 7149655
  have htrace : WordTrace (prefixWord ++ tailWord_7149655) baseStart_7149655 baseEnd_7149655 := by
    simpa [prefixWord, tailWord_7149655, baseEnd_7149655] using wordTrace_append hprefix tailTrace_7149655
  have hstable : (prefixWord ++ tailWord_7149655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149655).length < 2 ^ (prefixWord ++ tailWord_7149655).sum := by decide
  have hdescent : baseEnd_7149655 < baseStart_7149655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149665 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 4, 4]
def baseStart_7149665 : Nat := 118140960795 + 7149665 * 2 ^ 59
def prefixEnd_7149665 : Nat := 4983230072969 + 3 ^ 40 * 7149665 * 2
def baseEnd_7149665 : Nat := 1223738221209291545502265

theorem tailTrace_7149665 : CollatzResearch.WordTrace tailWord_7149665 prefixEnd_7149665 1223738221209291545502265 := by
  unfold tailWord_7149665
  simp only [CollatzResearch.WordTrace]
  refine ⟨260769705642992245413114449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173846470428661496942076299 260769705642992245413114449)
  ·
    refine ⟨195577279232244184059835837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260769705642992245413114449 195577279232244184059835837)
    ·
      refine ⟨73341479712091569022438439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195577279232244184059835837 73341479712091569022438439)
      ·
        refine ⟨110012219568137353533657659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73341479712091569022438439 110012219568137353533657659)
        ·
          refine ⟨165018329352206030300486489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110012219568137353533657659 165018329352206030300486489)
          ·
            refine ⟨123763747014154522725364867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165018329352206030300486489 123763747014154522725364867)
            ·
              refine ⟨185645620521231784088047301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123763747014154522725364867 185645620521231784088047301)
              ·
                refine ⟨34808553847730959516508869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185645620521231784088047301 34808553847730959516508869)
                ·
                  refine ⟨6526603846449554909345413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34808553847730959516508869 6526603846449554909345413)
                  ·
                    refine ⟨1223738221209291545502265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526603846449554909345413 1223738221209291545502265)
                    ·
                      rfl

theorem cell23_7149665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_7149665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149665 prefixEnd_7149665 := by exact prefixLift 7149665
  have htrace : WordTrace (prefixWord ++ tailWord_7149665) baseStart_7149665 baseEnd_7149665 := by
    simpa [prefixWord, tailWord_7149665, baseEnd_7149665] using wordTrace_append hprefix tailTrace_7149665
  have hstable : (prefixWord ++ tailWord_7149665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149665).length < 2 ^ (prefixWord ++ tailWord_7149665).sum := by decide
  have hdescent : baseEnd_7149665 < baseStart_7149665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149669 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_7149669 : Nat := 118140960795 + 7149669 * 2 ^ 59
def prefixEnd_7149669 : Nat := 4983230072969 + 3 ^ 40 * 7149669 * 2
def baseEnd_7149669 : Nat := 1223738905850164206952259

theorem tailTrace_7149669 : CollatzResearch.WordTrace tailWord_7149669 prefixEnd_7149669 1223738905850164206952259 := by
  unfold tailWord_7149669
  simp only [CollatzResearch.WordTrace]
  refine ⟨260769851534977754096260061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173846567689985169397506707 260769851534977754096260061)
  ·
    refine ⟨97788694325616657786097523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260769851534977754096260061 97788694325616657786097523)
    ·
      refine ⟨146683041488424986679146285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97788694325616657786097523 146683041488424986679146285)
      ·
        refine ⟨55006140558159370004679857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146683041488424986679146285 55006140558159370004679857)
        ·
          refine ⟨41254605418619527503509893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55006140558159370004679857 41254605418619527503509893)
          ·
            refine ⟨7735238515991161406908105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41254605418619527503509893 7735238515991161406908105)
            ·
              refine ⟨5801428886993371055181079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7735238515991161406908105 5801428886993371055181079)
              ·
                refine ⟨8702143330490056582771619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801428886993371055181079 8702143330490056582771619)
                ·
                  refine ⟨13053214995735084874157429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702143330490056582771619 13053214995735084874157429)
                  ·
                    refine ⟨1223738905850164206952259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13053214995735084874157429 1223738905850164206952259)
                    ·
                      rfl

theorem cell23_7149669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_7149669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149669 prefixEnd_7149669 := by exact prefixLift 7149669
  have htrace : WordTrace (prefixWord ++ tailWord_7149669) baseStart_7149669 baseEnd_7149669 := by
    simpa [prefixWord, tailWord_7149669, baseEnd_7149669] using wordTrace_append hprefix tailTrace_7149669
  have hstable : (prefixWord ++ tailWord_7149669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149669).length < 2 ^ (prefixWord ++ tailWord_7149669).sum := by decide
  have hdescent : baseEnd_7149669 < baseStart_7149669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149682 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_7149682 : Nat := 118140960795 + 7149682 * 2 ^ 59
def prefixEnd_7149682 : Nat := 4983230072969 + 3 ^ 40 * 7149682 * 2
def baseEnd_7149682 : Nat := 1223741130933000356664739

theorem tailTrace_7149682 : CollatzResearch.WordTrace tailWord_7149682 prefixEnd_7149682 1223741130933000356664739 := by
  unfold tailWord_7149682
  simp only [CollatzResearch.WordTrace]
  refine ⟨65192581420982664329120825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173846883789287104877655533 65192581420982664329120825)
  ·
    refine ⟨48894436065736998246840619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65192581420982664329120825 48894436065736998246840619)
    ·
      refine ⟨73341654098605497370260929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48894436065736998246840619 73341654098605497370260929)
      ·
        refine ⟨55006240573954123027695697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73341654098605497370260929 55006240573954123027695697)
        ·
          refine ⟨41254680430465592270771773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55006240573954123027695697 41254680430465592270771773)
          ·
            refine ⟨15470505161424597101539415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41254680430465592270771773 15470505161424597101539415)
            ·
              refine ⟨23205757742136895652309123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15470505161424597101539415 23205757742136895652309123)
              ·
                refine ⟨34808636613205343478463685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23205757742136895652309123 34808636613205343478463685)
                ·
                  refine ⟨6526619364976001902211941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34808636613205343478463685 6526619364976001902211941)
                  ·
                    refine ⟨1223741130933000356664739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526619364976001902211941 1223741130933000356664739)
                    ·
                      rfl

theorem cell23_7149682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_7149682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149682 prefixEnd_7149682 := by exact prefixLift 7149682
  have htrace : WordTrace (prefixWord ++ tailWord_7149682) baseStart_7149682 baseEnd_7149682 := by
    simpa [prefixWord, tailWord_7149682, baseEnd_7149682] using wordTrace_append hprefix tailTrace_7149682
  have hstable : (prefixWord ++ tailWord_7149682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149682).length < 2 ^ (prefixWord ++ tailWord_7149682).sum := by decide
  have hdescent : baseEnd_7149682 < baseStart_7149682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149688 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_7149688 : Nat := 118140960795 + 7149688 * 2 ^ 59
def prefixEnd_7149688 : Nat := 4983230072969 + 3 ^ 40 * 7149688 * 2
def baseEnd_7149688 : Nat := 3671226473682928046519189

theorem tailTrace_7149688 : CollatzResearch.WordTrace tailWord_7149688 prefixEnd_7149688 3671226473682928046519189 := by
  unfold tailWord_7149688
  simp only [CollatzResearch.WordTrace]
  refine ⟨130385272260954460170600859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173847029681272613560801145 130385272260954460170600859)
  ·
    refine ⟨195577908391431690255901289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130385272260954460170600859 195577908391431690255901289)
    ·
      refine ⟨146683431293573767691925967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195577908391431690255901289 146683431293573767691925967)
      ·
        refine ⟨220025146940360651537888951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146683431293573767691925967 220025146940360651537888951)
        ·
          refine ⟨330037720410540977306833427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220025146940360651537888951 330037720410540977306833427)
          ·
            refine ⟨495056580615811465960250141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330037720410540977306833427 495056580615811465960250141)
            ·
              refine ⟨185646217730929299735093803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495056580615811465960250141 185646217730929299735093803)
              ·
                refine ⟨278469326596393949602640705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185646217730929299735093803 278469326596393949602640705)
                ·
                  refine ⟨208851994947295462201980529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278469326596393949602640705 208851994947295462201980529)
                  ·
                    refine ⟨156638996210471596651485397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208851994947295462201980529 156638996210471596651485397)
                    ·
                      refine ⟨3671226473682928046519189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156638996210471596651485397 3671226473682928046519189)
                      ·
                        rfl

theorem cell23_7149688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_7149688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149688 prefixEnd_7149688 := by exact prefixLift 7149688
  have htrace : WordTrace (prefixWord ++ tailWord_7149688) baseStart_7149688 baseEnd_7149688 := by
    simpa [prefixWord, tailWord_7149688, baseEnd_7149688] using wordTrace_append hprefix tailTrace_7149688
  have hstable : (prefixWord ++ tailWord_7149688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149688).length < 2 ^ (prefixWord ++ tailWord_7149688).sum := by decide
  have hdescent : baseEnd_7149688 < baseStart_7149688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149689 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 3, 2, 2]
def baseStart_7149689 : Nat := 118140960795 + 7149689 * 2 ^ 59
def prefixEnd_7149689 : Nat := 4983230072969 + 3 ^ 40 * 7149689 * 2
def baseEnd_7149689 : Nat := 3671226987163582542606685

theorem tailTrace_7149689 : CollatzResearch.WordTrace tailWord_7149689 prefixEnd_7149689 3671226987163582542606685 := by
  unfold tailWord_7149689
  simp only [CollatzResearch.WordTrace]
  refine ⟨260770580994905297511988121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173847053996603531674658747 260770580994905297511988121)
  ·
    refine ⟨195577935746178973133991091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260770580994905297511988121 195577935746178973133991091)
    ·
      refine ⟨293366903619268459700986637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195577935746178973133991091 293366903619268459700986637)
      ·
        refine ⟨110012588857225672387869989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293366903619268459700986637 110012588857225672387869989)
        ·
          refine ⟨20627360410729813572725623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110012588857225672387869989 20627360410729813572725623)
          ·
            refine ⟨30941040616094720359088435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20627360410729813572725623 30941040616094720359088435)
            ·
              refine ⟨46411560924142080538632653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30941040616094720359088435 46411560924142080538632653)
              ·
                refine ⟨17404335346553280201987245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46411560924142080538632653 17404335346553280201987245)
                ·
                  refine ⟨6526625754957480075745217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17404335346553280201987245 6526625754957480075745217)
                  ·
                    refine ⟨4894969316218110056808913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6526625754957480075745217 4894969316218110056808913)
                    ·
                      refine ⟨3671226987163582542606685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4894969316218110056808913 3671226987163582542606685)
                      ·
                        rfl

theorem cell23_7149689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_7149689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149689 prefixEnd_7149689 := by exact prefixLift 7149689
  have htrace : WordTrace (prefixWord ++ tailWord_7149689) baseStart_7149689 baseEnd_7149689 := by
    simpa [prefixWord, tailWord_7149689, baseEnd_7149689] using wordTrace_append hprefix tailTrace_7149689
  have hstable : (prefixWord ++ tailWord_7149689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149689).length < 2 ^ (prefixWord ++ tailWord_7149689).sum := by decide
  have hdescent : baseEnd_7149689 < baseStart_7149689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149699 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 2, 4]
def baseStart_7149699 : Nat := 118140960795 + 7149699 * 2 ^ 59
def prefixEnd_7149699 : Nat := 4983230072969 + 3 ^ 40 * 7149699 * 2
def baseEnd_7149699 : Nat := 1223744040656709167827213

theorem tailTrace_7149699 : CollatzResearch.WordTrace tailWord_7149699 prefixEnd_7149699 1223744040656709167827213 := by
  unfold tailWord_7149699
  simp only [CollatzResearch.WordTrace]
  refine ⟨260770945724869069219852151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173847297149912712813234767 260770945724869069219852151)
  ·
    refine ⟨391156418587303603829778227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260770945724869069219852151 391156418587303603829778227)
    ·
      refine ⟨586734627880955405744667341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391156418587303603829778227 586734627880955405744667341)
      ·
        refine ⟨220025485455358277154250253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 586734627880955405744667341 220025485455358277154250253)
        ·
          refine ⟨82509557045759353932843845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220025485455358277154250253 82509557045759353932843845)
          ·
            refine ⟨15470541946079878862408221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82509557045759353932843845 15470541946079878862408221)
            ·
              refine ⟨5801453229779954573403083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15470541946079878862408221 5801453229779954573403083)
              ·
                refine ⟨8702179844669931860104625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801453229779954573403083 8702179844669931860104625)
                ·
                  refine ⟨6526634883502448895078469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702179844669931860104625 6526634883502448895078469)
                  ·
                    refine ⟨1223744040656709167827213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526634883502448895078469 1223744040656709167827213)
                    ·
                      rfl

theorem cell23_7149699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 4].length) (baseStart_7149699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149699 prefixEnd_7149699 := by exact prefixLift 7149699
  have htrace : WordTrace (prefixWord ++ tailWord_7149699) baseStart_7149699 baseEnd_7149699 := by
    simpa [prefixWord, tailWord_7149699, baseEnd_7149699] using wordTrace_append hprefix tailTrace_7149699
  have hstable : (prefixWord ++ tailWord_7149699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149699).length < 2 ^ (prefixWord ++ tailWord_7149699).sum := by decide
  have hdescent : baseEnd_7149699 < baseStart_7149699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149756 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_7149756 : Nat := 118140960795 + 7149756 * 2 ^ 59
def prefixEnd_7149756 : Nat := 4983230072969 + 3 ^ 40 * 7149756 * 2
def baseEnd_7149756 : Nat := 3671261390367433780468877

theorem tailTrace_7149756 : CollatzResearch.WordTrace tailWord_7149756 prefixEnd_7149756 3671261390367433780468877 := by
  unfold tailWord_7149756
  simp only [CollatzResearch.WordTrace]
  refine ⟨130386512342831283977338561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173848683123775045303118081 130386512342831283977338561)
  ·
    refine ⟨97789884257123462983003921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130386512342831283977338561 97789884257123462983003921)
    ·
      refine ⟨73342413192842597237252941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97789884257123462983003921 73342413192842597237252941)
      ·
        refine ⟨27503404947315973963969853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73342413192842597237252941 27503404947315973963969853)
        ·
          refine ⟨10313776855243490236488695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27503404947315973963969853 10313776855243490236488695)
          ·
            refine ⟨15470665282865235354733043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313776855243490236488695 15470665282865235354733043)
            ·
              refine ⟨23205997924297853032099565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15470665282865235354733043 23205997924297853032099565)
              ·
                refine ⟨8702249221611694887037337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23205997924297853032099565 8702249221611694887037337)
                ·
                  refine ⟨6526686916208771165278003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702249221611694887037337 6526686916208771165278003)
                  ·
                    refine ⟨9790030374313156747917005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6526686916208771165278003 9790030374313156747917005)
                    ·
                      refine ⟨3671261390367433780468877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790030374313156747917005 3671261390367433780468877)
                      ·
                        rfl

theorem cell23_7149756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_7149756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149756 prefixEnd_7149756 := by exact prefixLift 7149756
  have htrace : WordTrace (prefixWord ++ tailWord_7149756) baseStart_7149756 baseEnd_7149756 := by
    simpa [prefixWord, tailWord_7149756, baseEnd_7149756] using wordTrace_append hprefix tailTrace_7149756
  have hstable : (prefixWord ++ tailWord_7149756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149756).length < 2 ^ (prefixWord ++ tailWord_7149756).sum := by decide
  have hdescent : baseEnd_7149756 < baseStart_7149756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149765 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_7149765 : Nat := 118140960795 + 7149765 * 2 ^ 59
def prefixEnd_7149765 : Nat := 4983230072969 + 3 ^ 40 * 7149765 * 2
def baseEnd_7149765 : Nat := 3671266011693324245256335

theorem tailTrace_7149765 : CollatzResearch.WordTrace tailWord_7149765 prefixEnd_7149765 3671266011693324245256335 := by
  unfold tailWord_7149765
  simp only [CollatzResearch.WordTrace]
  refine ⟨260773352942629962491754749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173848901961753308327836499 260773352942629962491754749)
  ·
    refine ⟨97790007353486235934408031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260773352942629962491754749 97790007353486235934408031)
    ·
      refine ⟨146685011030229353901612047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97790007353486235934408031 146685011030229353901612047)
      ·
        refine ⟨220027516545344030852418071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146685011030229353901612047 220027516545344030852418071)
        ·
          refine ⟨330041274818016046278627107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220027516545344030852418071 330041274818016046278627107)
          ·
            refine ⟨495061912227024069417940661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330041274818016046278627107 495061912227024069417940661)
            ·
              refine ⟨46412054271283506507931937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495061912227024069417940661 46412054271283506507931937)
              ·
                refine ⟨34809040703462629880948953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46412054271283506507931937 34809040703462629880948953)
                ·
                  refine ⟨26106780527596972410711715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34809040703462629880948953 26106780527596972410711715)
                  ·
                    refine ⟨39160170791395458616067573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26106780527596972410711715 39160170791395458616067573)
                    ·
                      refine ⟨3671266011693324245256335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39160170791395458616067573 3671266011693324245256335)
                      ·
                        rfl

theorem cell23_7149765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_7149765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149765 prefixEnd_7149765 := by exact prefixLift 7149765
  have htrace : WordTrace (prefixWord ++ tailWord_7149765) baseStart_7149765 baseEnd_7149765 := by
    simpa [prefixWord, tailWord_7149765, baseEnd_7149765] using wordTrace_append hprefix tailTrace_7149765
  have hstable : (prefixWord ++ tailWord_7149765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149765).length < 2 ^ (prefixWord ++ tailWord_7149765).sum := by decide
  have hdescent : baseEnd_7149765 < baseStart_7149765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149832 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 1, 7]
def baseStart_7149832 : Nat := 118140960795 + 7149832 * 2 ^ 59
def prefixEnd_7149832 : Nat := 4983230072969 + 3 ^ 40 * 7149832 * 2
def baseEnd_7149832 : Nat := 1223766804965725161039509

theorem tailTrace_7149832 : CollatzResearch.WordTrace tailWord_7149832 prefixEnd_7149832 1223766804965725161039509 := by
  unfold tailWord_7149832
  simp only [CollatzResearch.WordTrace]
  refine ⟨130387898316693616467221875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173850531088924821956295833 130387898316693616467221875)
  ·
    refine ⟨195581847475040424700832813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130387898316693616467221875 195581847475040424700832813)
    ·
      refine ⟨73343192803140159262812305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195581847475040424700832813 73343192803140159262812305)
      ·
        refine ⟨55007394602355119447109229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73343192803140159262812305 55007394602355119447109229)
        ·
          refine ⟨20627772975883169792665961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55007394602355119447109229 20627772975883169792665961)
          ·
            refine ⟨15470829731912377344499471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20627772975883169792665961 15470829731912377344499471)
            ·
              refine ⟨23206244597868566016749207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15470829731912377344499471 23206244597868566016749207)
              ·
                refine ⟨34809366896802849025123811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23206244597868566016749207 34809366896802849025123811)
                ·
                  refine ⟨52214050345204273537685717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34809366896802849025123811 52214050345204273537685717)
                  ·
                    refine ⟨1223766804965725161039509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52214050345204273537685717 1223766804965725161039509)
                    ·
                      rfl

theorem cell23_7149832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_7149832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149832 prefixEnd_7149832 := by exact prefixLift 7149832
  have htrace : WordTrace (prefixWord ++ tailWord_7149832) baseStart_7149832 baseEnd_7149832 := by
    simpa [prefixWord, tailWord_7149832, baseEnd_7149832] using wordTrace_append hprefix tailTrace_7149832
  have hstable : (prefixWord ++ tailWord_7149832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149832).length < 2 ^ (prefixWord ++ tailWord_7149832).sum := by decide
  have hdescent : baseEnd_7149832 < baseStart_7149832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149852 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7149852 : Nat := 118140960795 + 7149852 * 2 ^ 59
def prefixEnd_7149852 : Nat := 4983230072969 + 3 ^ 40 * 7149852 * 2
def baseEnd_7149852 : Nat := 3671310684510265404868435

theorem tailTrace_7149852 : CollatzResearch.WordTrace tailWord_7149852 prefixEnd_7149852 3671310684510265404868435 := by
  unfold tailWord_7149852
  simp only [CollatzResearch.WordTrace]
  refine ⟨130388263046657388175085905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173851017395543184233447873 130388263046657388175085905)
  ·
    refine ⟨97791197284993041131314429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130388263046657388175085905 97791197284993041131314429)
    ·
      refine ⟨36671698981872390424242911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97791197284993041131314429 36671698981872390424242911)
      ·
        refine ⟨55007548472808585636364367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36671698981872390424242911 55007548472808585636364367)
        ·
          refine ⟨82511322709212878454546551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55007548472808585636364367 82511322709212878454546551)
          ·
            refine ⟨123766984063819317681819827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82511322709212878454546551 123766984063819317681819827)
            ·
              refine ⟨185650476095728976522729741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123766984063819317681819827 185650476095728976522729741)
              ·
                refine ⟨69618928535898366196023653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185650476095728976522729741 69618928535898366196023653)
                ·
                  refine ⟨13053549100480943661754435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69618928535898366196023653 13053549100480943661754435)
                  ·
                    refine ⟨19580323650721415492631653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13053549100480943661754435 19580323650721415492631653)
                    ·
                      refine ⟨3671310684510265404868435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19580323650721415492631653 3671310684510265404868435)
                      ·
                        rfl

theorem cell23_7149852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7149852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149852 prefixEnd_7149852 := by exact prefixLift 7149852
  have htrace : WordTrace (prefixWord ++ tailWord_7149852) baseStart_7149852 baseEnd_7149852 := by
    simpa [prefixWord, tailWord_7149852, baseEnd_7149852] using wordTrace_append hprefix tailTrace_7149852
  have hstable : (prefixWord ++ tailWord_7149852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149852).length < 2 ^ (prefixWord ++ tailWord_7149852).sum := by decide
  have hdescent : baseEnd_7149852 < baseStart_7149852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149872 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3]
def baseStart_7149872 : Nat := 118140960795 + 7149872 * 2 ^ 59
def prefixEnd_7149872 : Nat := 4983230072969 + 3 ^ 40 * 7149872 * 2
def baseEnd_7149872 : Nat := 3671320954123355326618343

theorem tailTrace_7149872 : CollatzResearch.WordTrace tailWord_7149872 prefixEnd_7149872 3671320954123355326618343 := by
  unfold tailWord_7149872
  simp only [CollatzResearch.WordTrace]
  refine ⟨130388627776621159882949935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173851503702161546510599913 130388627776621159882949935)
  ·
    refine ⟨195582941664931739824424903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130388627776621159882949935 195582941664931739824424903)
    ·
      refine ⟨293374412497397609736637355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195582941664931739824424903 293374412497397609736637355)
      ·
        refine ⟨440061618746096414604956033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293374412497397609736637355 440061618746096414604956033)
        ·
          refine ⟨330046214059572310953717025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440061618746096414604956033 330046214059572310953717025)
          ·
            refine ⟨247534660544679233215287769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330046214059572310953717025 247534660544679233215287769)
            ·
              refine ⟨185650995408509424911465827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247534660544679233215287769 185650995408509424911465827)
              ·
                refine ⟨278476493112764137367198741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185650995408509424911465827 278476493112764137367198741)
                ·
                  refine ⟨13053585614660818939087441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 278476493112764137367198741 13053585614660818939087441)
                  ·
                    refine ⟨9790189210995614204315581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13053585614660818939087441 9790189210995614204315581)
                    ·
                      refine ⟨3671320954123355326618343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790189210995614204315581 3671320954123355326618343)
                      ·
                        rfl

theorem cell23_7149872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_7149872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149872 prefixEnd_7149872 := by exact prefixLift 7149872
  have htrace : WordTrace (prefixWord ++ tailWord_7149872) baseStart_7149872 baseEnd_7149872 := by
    simpa [prefixWord, tailWord_7149872, baseEnd_7149872] using wordTrace_append hprefix tailTrace_7149872
  have hstable : (prefixWord ++ tailWord_7149872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149872).length < 2 ^ (prefixWord ++ tailWord_7149872).sum := by decide
  have hdescent : baseEnd_7149872 < baseStart_7149872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149896 : List Nat := [2, 1, 3, 1, 1, 2, 5, 3, 1, 4]
def baseStart_7149896 : Nat := 118140960795 + 7149896 * 2 ^ 59
def prefixEnd_7149896 : Nat := 4983230072969 + 3 ^ 40 * 7149896 * 2
def baseEnd_7149896 : Nat := 1223777759219687744239411

theorem tailTrace_7149896 : CollatzResearch.WordTrace tailWord_7149896 prefixEnd_7149896 1223777759219687744239411 := by
  unfold tailWord_7149896
  simp only [CollatzResearch.WordTrace]
  refine ⟨130389065452577685932386771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173852087270103581243182361 130389065452577685932386771)
  ·
    refine ⟨195583598178866528898580157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130389065452577685932386771 195583598178866528898580157)
    ·
      refine ⟨73343849317074948336967559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195583598178866528898580157 73343849317074948336967559)
      ·
        refine ⟨110015773975612422505451339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73343849317074948336967559 110015773975612422505451339)
        ·
          refine ⟨165023660963418633758177009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110015773975612422505451339 165023660963418633758177009)
          ·
            refine ⟨123767745722563975318632757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165023660963418633758177009 123767745722563975318632757)
            ·
              refine ⟨11603226161490372686121821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123767745722563975318632757 11603226161490372686121821)
              ·
                refine ⟨4351209810558889757295683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11603226161490372686121821 4351209810558889757295683)
                ·
                  refine ⟨6526814715838334635943525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351209810558889757295683 6526814715838334635943525)
                  ·
                    refine ⟨1223777759219687744239411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526814715838334635943525 1223777759219687744239411)
                    ·
                      rfl

theorem cell23_7149896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_7149896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149896 prefixEnd_7149896 := by exact prefixLift 7149896
  have htrace : WordTrace (prefixWord ++ tailWord_7149896) baseStart_7149896 baseEnd_7149896 := by
    simpa [prefixWord, tailWord_7149896, baseEnd_7149896] using wordTrace_append hprefix tailTrace_7149896
  have hstable : (prefixWord ++ tailWord_7149896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149896).length < 2 ^ (prefixWord ++ tailWord_7149896).sum := by decide
  have hdescent : baseEnd_7149896 < baseStart_7149896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149915 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11]
def baseStart_7149915 : Nat := 118140960795 + 7149915 * 2 ^ 59
def prefixEnd_7149915 : Nat := 4983230072969 + 3 ^ 40 * 7149915 * 2
def baseEnd_7149915 : Nat := 3671343033791498658380645

theorem tailTrace_7149915 : CollatzResearch.WordTrace tailWord_7149915 prefixEnd_7149915 3671343033791498658380645 := by
  unfold tailWord_7149915
  simp only [CollatzResearch.WordTrace]
  refine ⟨260778823892086538109715199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173852549261391025406476799 260778823892086538109715199)
  ·
    refine ⟨391168235838129807164572799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260778823892086538109715199 391168235838129807164572799)
    ·
      refine ⟨586752353757194710746859199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391168235838129807164572799 586752353757194710746859199)
      ·
        refine ⟨880128530635792066120288799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586752353757194710746859199 880128530635792066120288799)
        ·
          refine ⟨1320192795953688099180433199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880128530635792066120288799 1320192795953688099180433199)
          ·
            refine ⟨1980289193930532148770649799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320192795953688099180433199 1980289193930532148770649799)
            ·
              refine ⟨2970433790895798223155974699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980289193930532148770649799 2970433790895798223155974699)
              ·
                refine ⟨4455650686343697334733962049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970433790895798223155974699 4455650686343697334733962049)
                ·
                  refine ⟨3341738014757773001050471537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4455650686343697334733962049 3341738014757773001050471537)
                  ·
                    refine ⟨2506303511068329750787853653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341738014757773001050471537 2506303511068329750787853653)
                    ·
                      refine ⟨3671343033791498658380645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2506303511068329750787853653 3671343033791498658380645)
                      ·
                        rfl

theorem cell23_7149915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_7149915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149915 prefixEnd_7149915 := by exact prefixLift 7149915
  have htrace : WordTrace (prefixWord ++ tailWord_7149915) baseStart_7149915 baseEnd_7149915 := by
    simpa [prefixWord, tailWord_7149915, baseEnd_7149915] using wordTrace_append hprefix tailTrace_7149915
  have hstable : (prefixWord ++ tailWord_7149915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149915).length < 2 ^ (prefixWord ++ tailWord_7149915).sum := by decide
  have hdescent : baseEnd_7149915 < baseStart_7149915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149929 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 4, 3, 2]
def baseStart_7149929 : Nat := 118140960795 + 7149929 * 2 ^ 59
def prefixEnd_7149929 : Nat := 4983230072969 + 3 ^ 40 * 7149929 * 2
def baseEnd_7149929 : Nat := 3671350222520661603605581

theorem tailTrace_7149929 : CollatzResearch.WordTrace tailWord_7149929 prefixEnd_7149929 3671350222520661603605581 := by
  unfold tailWord_7149929
  simp only [CollatzResearch.WordTrace]
  refine ⟨260779334514035818500724841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173852889676023879000483227 260779334514035818500724841)
  ·
    refine ⟨195584500885526863875543631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260779334514035818500724841 195584500885526863875543631)
    ·
      refine ⟨293376751328290295813315447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195584500885526863875543631 293376751328290295813315447)
      ·
        refine ⟨440065126992435443719973171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293376751328290295813315447 440065126992435443719973171)
        ·
          refine ⟨660097690488653165579959757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440065126992435443719973171 660097690488653165579959757)
          ·
            refine ⟨247536633933244937092484909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660097690488653165579959757 247536633933244937092484909)
            ·
              refine ⟨92826237724966851409681841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247536633933244937092484909 92826237724966851409681841)
              ·
                refine ⟨69619678293725138557261381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92826237724966851409681841 69619678293725138557261381)
                ·
                  refine ⟨13053689680073463479486509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69619678293725138557261381 13053689680073463479486509)
                  ·
                    refine ⟨4895133630027548804807441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13053689680073463479486509 4895133630027548804807441)
                    ·
                      refine ⟨3671350222520661603605581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895133630027548804807441 3671350222520661603605581)
                      ·
                        rfl

theorem cell23_7149929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 3, 2].length) (baseStart_7149929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149929 prefixEnd_7149929 := by exact prefixLift 7149929
  have htrace : WordTrace (prefixWord ++ tailWord_7149929) baseStart_7149929 baseEnd_7149929 := by
    simpa [prefixWord, tailWord_7149929, baseEnd_7149929] using wordTrace_append hprefix tailTrace_7149929
  have hstable : (prefixWord ++ tailWord_7149929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149929).length < 2 ^ (prefixWord ++ tailWord_7149929).sum := by decide
  have hdescent : baseEnd_7149929 < baseStart_7149929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149956 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_7149956 : Nat := 118140960795 + 7149956 * 2 ^ 59
def prefixEnd_7149956 : Nat := 4983230072969 + 3 ^ 40 * 7149956 * 2
def baseEnd_7149956 : Nat := 1223788028832777665989319

theorem tailTrace_7149956 : CollatzResearch.WordTrace tailWord_7149956 prefixEnd_7149956 1223788028832777665989319 := by
  unfold tailWord_7149956
  simp only [CollatzResearch.WordTrace]
  refine ⟨130390159642469001055978861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173853546189958668074638481 130390159642469001055978861)
  ·
    refine ⟨48896309865925875395992073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130390159642469001055978861 48896309865925875395992073)
    ·
      refine ⟨36672232399444406546994055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48896309865925875395992073 36672232399444406546994055)
      ·
        refine ⟨55008348599166609820491083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36672232399444406546994055 55008348599166609820491083)
        ·
          refine ⟨82512522898749914730736625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55008348599166609820491083 82512522898749914730736625)
          ·
            refine ⟨61884392174062436048052469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82512522898749914730736625 61884392174062436048052469)
            ·
              refine ⟨5801661766318353379504919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61884392174062436048052469 5801661766318353379504919)
              ·
                refine ⟨8702492649477530069257379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801661766318353379504919 8702492649477530069257379)
                ·
                  refine ⟨13053738974216295103886069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702492649477530069257379 13053738974216295103886069)
                  ·
                    refine ⟨1223788028832777665989319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13053738974216295103886069 1223788028832777665989319)
                    ·
                      rfl

theorem cell23_7149956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_7149956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149956 prefixEnd_7149956 := by exact prefixLift 7149956
  have htrace : WordTrace (prefixWord ++ tailWord_7149956) baseStart_7149956 baseEnd_7149956 := by
    simpa [prefixWord, tailWord_7149956, baseEnd_7149956] using wordTrace_append hprefix tailTrace_7149956
  have hstable : (prefixWord ++ tailWord_7149956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149956).length < 2 ^ (prefixWord ++ tailWord_7149956).sum := by decide
  have hdescent : baseEnd_7149956 < baseStart_7149956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149986 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7149986 : Nat := 118140960795 + 7149986 * 2 ^ 59
def prefixEnd_7149986 : Nat := 4983230072969 + 3 ^ 40 * 7149986 * 2
def baseEnd_7149986 : Nat := 1223793163639322626864273

theorem tailTrace_7149986 : CollatzResearch.WordTrace tailWord_7149986 prefixEnd_7149986 1223793163639322626864273 := by
  unfold tailWord_7149986
  simp only [CollatzResearch.WordTrace]
  refine ⟨65195353368707329308887453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173854275649886211490366541 65195353368707329308887453)
  ·
    refine ⟨24448257513265248490832795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65195353368707329308887453 24448257513265248490832795)
    ·
      refine ⟨36672386269897872736249193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24448257513265248490832795 36672386269897872736249193)
      ·
        refine ⟨27504289702423404552186895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36672386269897872736249193 27504289702423404552186895)
        ·
          refine ⟨41256434553635106828280343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27504289702423404552186895 41256434553635106828280343)
          ·
            refine ⟨61884651830452660242420515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41256434553635106828280343 61884651830452660242420515)
            ·
              refine ⟨92826977745678990363630773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61884651830452660242420515 92826977745678990363630773)
              ·
                refine ⟨8702529163657405346590385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92826977745678990363630773 8702529163657405346590385)
                ·
                  refine ⟨6526896872743054009942789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702529163657405346590385 6526896872743054009942789)
                  ·
                    refine ⟨1223793163639322626864273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526896872743054009942789 1223793163639322626864273)
                    ·
                      rfl

theorem cell23_7149986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7149986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149986 prefixEnd_7149986 := by exact prefixLift 7149986
  have htrace : WordTrace (prefixWord ++ tailWord_7149986) baseStart_7149986 baseEnd_7149986 := by
    simpa [prefixWord, tailWord_7149986, baseEnd_7149986] using wordTrace_append hprefix tailTrace_7149986
  have hstable : (prefixWord ++ tailWord_7149986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149986).length < 2 ^ (prefixWord ++ tailWord_7149986).sum := by decide
  have hdescent : baseEnd_7149986 < baseStart_7149986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149989 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_7149989 : Nat := 118140960795 + 7149989 * 2 ^ 59
def prefixEnd_7149989 : Nat := 4983230072969 + 3 ^ 40 * 7149989 * 2
def baseEnd_7149989 : Nat := 3671381031359931368855305

theorem tailTrace_7149989 : CollatzResearch.WordTrace tailWord_7149989 prefixEnd_7149989 3671381031359931368855305 := by
  unfold tailWord_7149989
  simp only [CollatzResearch.WordTrace]
  refine ⟨260781522893818448747909021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173854348595878965831939347 260781522893818448747909021)
  ·
    refine ⟨97793071085181918280465883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260781522893818448747909021 97793071085181918280465883)
    ·
      refine ⟨146689606627772877420698825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97793071085181918280465883 146689606627772877420698825)
      ·
        refine ⟨110017204970829658065524119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146689606627772877420698825 110017204970829658065524119)
        ·
          refine ⟨165025807456244487098286179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110017204970829658065524119 165025807456244487098286179)
          ·
            refine ⟨247538711184366730647429269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165025807456244487098286179 247538711184366730647429269)
            ·
              refine ⟨11603377086767190499098247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247538711184366730647429269 11603377086767190499098247)
              ·
                refine ⟨17405065630150785748647371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11603377086767190499098247 17405065630150785748647371)
                ·
                  refine ⟨26107598445226178622971057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17405065630150785748647371 26107598445226178622971057)
                  ·
                    refine ⟨19580698833919633967228293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26107598445226178622971057 19580698833919633967228293)
                    ·
                      refine ⟨3671381031359931368855305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19580698833919633967228293 3671381031359931368855305)
                      ·
                        rfl

theorem cell23_7149989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_7149989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149989 prefixEnd_7149989 := by exact prefixLift 7149989
  have htrace : WordTrace (prefixWord ++ tailWord_7149989) baseStart_7149989 baseEnd_7149989 := by
    simpa [prefixWord, tailWord_7149989, baseEnd_7149989] using wordTrace_append hprefix tailTrace_7149989
  have hstable : (prefixWord ++ tailWord_7149989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149989).length < 2 ^ (prefixWord ++ tailWord_7149989).sum := by decide
  have hdescent : baseEnd_7149989 < baseStart_7149989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7149997 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7149997 : Nat := 118140960795 + 7149997 * 2 ^ 59
def prefixEnd_7149997 : Nat := 4983230072969 + 3 ^ 40 * 7149997 * 2
def baseEnd_7149997 : Nat := 3671385139205167337555269

theorem tailTrace_7149997 : CollatzResearch.WordTrace tailWord_7149997 prefixEnd_7149997 3671385139205167337555269 := by
  unfold tailWord_7149997
  simp only [CollatzResearch.WordTrace]
  refine ⟨260781814677789466114200245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173854543118526310742800163 260781814677789466114200245)
  ·
    refine ⟨24448295126042762448206273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260781814677789466114200245 24448295126042762448206273)
    ·
      refine ⟨18336221344532071836154705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24448295126042762448206273 18336221344532071836154705)
      ·
        refine ⟨13752166008399053877116029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18336221344532071836154705 13752166008399053877116029)
        ·
          refine ⟨5157062253149645203918511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13752166008399053877116029 5157062253149645203918511)
          ·
            refine ⟨7735593379724467805877767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157062253149645203918511 7735593379724467805877767)
            ·
              refine ⟨11603390069586701708816651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735593379724467805877767 11603390069586701708816651)
              ·
                refine ⟨17405085104380052563224977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11603390069586701708816651 17405085104380052563224977)
                ·
                  refine ⟨13053813828285039422418733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17405085104380052563224977 13053813828285039422418733)
                  ·
                    refine ⟨4895180185606889783407025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13053813828285039422418733 4895180185606889783407025)
                    ·
                      refine ⟨3671385139205167337555269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4895180185606889783407025 3671385139205167337555269)
                      ·
                        rfl

theorem cell23_7149997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7149997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7149997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7149997 prefixEnd_7149997 := by exact prefixLift 7149997
  have htrace : WordTrace (prefixWord ++ tailWord_7149997) baseStart_7149997 baseEnd_7149997 := by
    simpa [prefixWord, tailWord_7149997, baseEnd_7149997] using wordTrace_append hprefix tailTrace_7149997
  have hstable : (prefixWord ++ tailWord_7149997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7149997).length < 2 ^ (prefixWord ++ tailWord_7149997).sum := by decide
  have hdescent : baseEnd_7149997 < baseStart_7149997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7149997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150004 : List Nat := [2, 5, 2, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7150004 : Nat := 118140960795 + 7150004 * 2 ^ 59
def prefixEnd_7150004 : Nat := 4983230072969 + 3 ^ 40 * 7150004 * 2
def baseEnd_7150004 : Nat := 3671388733569748810167737

theorem tailTrace_7150004 : CollatzResearch.WordTrace tailWord_7150004 prefixEnd_7150004 3671388733569748810167737 := by
  unfold tailWord_7150004
  simp only [CollatzResearch.WordTrace]
  refine ⟨130391034994382053154852533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173854713325842737539803377 130391034994382053154852533)
  ·
    refine ⟨12224159530723317483267425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130391034994382053154852533 12224159530723317483267425)
    ·
      refine ⟨9168119648042488112450569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12224159530723317483267425 9168119648042488112450569)
      ·
        refine ⟨6876089736031866084337927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9168119648042488112450569 6876089736031866084337927)
        ·
          refine ⟨10314134604047799126506891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6876089736031866084337927 10314134604047799126506891)
          ·
            refine ⟨15471201906071698689760337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10314134604047799126506891 15471201906071698689760337)
            ·
              refine ⟨11603401429553774017320253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15471201906071698689760337 11603401429553774017320253)
              ·
                refine ⟨4351275536082665256495095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11603401429553774017320253 4351275536082665256495095)
                ·
                  refine ⟨6526913304123997884742643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351275536082665256495095 6526913304123997884742643)
                  ·
                    refine ⟨9790369956185996827113965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6526913304123997884742643 9790369956185996827113965)
                    ·
                      refine ⟨3671388733569748810167737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790369956185996827113965 3671388733569748810167737)
                      ·
                        rfl

theorem cell23_7150004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7150004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150004 prefixEnd_7150004 := by exact prefixLift 7150004
  have htrace : WordTrace (prefixWord ++ tailWord_7150004) baseStart_7150004 baseEnd_7150004 := by
    simpa [prefixWord, tailWord_7150004, baseEnd_7150004] using wordTrace_append hprefix tailTrace_7150004
  have hstable : (prefixWord ++ tailWord_7150004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150004).length < 2 ^ (prefixWord ++ tailWord_7150004).sum := by decide
  have hdescent : baseEnd_7150004 < baseStart_7150004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150013 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_7150013 : Nat := 118140960795 + 7150013 * 2 ^ 59
def prefixEnd_7150013 : Nat := 4983230072969 + 3 ^ 40 * 7150013 * 2
def baseEnd_7150013 : Nat := 3671393354895639274955195

theorem tailTrace_7150013 : CollatzResearch.WordTrace tailWord_7150013 prefixEnd_7150013 3671393354895639274955195 := by
  unfold tailWord_7150013
  simp only [CollatzResearch.WordTrace]
  refine ⟨260782398245731500846782693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173854932163821000564521795 260782398245731500846782693)
  ·
    refine ⟨48896699671074656408771755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260782398245731500846782693 48896699671074656408771755)
    ·
      refine ⟨73345049506611984613157633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48896699671074656408771755 73345049506611984613157633)
      ·
        refine ⟨55008787129958988459868225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73345049506611984613157633 55008787129958988459868225)
        ·
          refine ⟨41256590347469241344901169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55008787129958988459868225 41256590347469241344901169)
          ·
            refine ⟨30942442760601931008675877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41256590347469241344901169 30942442760601931008675877)
            ·
              refine ⟨5801708017612862064126727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30942442760601931008675877 5801708017612862064126727)
              ·
                refine ⟨8702562026419293096190091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801708017612862064126727 8702562026419293096190091)
                ·
                  refine ⟨13053843039628939644285137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702562026419293096190091 13053843039628939644285137)
                  ·
                    refine ⟨9790382279721704733213853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13053843039628939644285137 9790382279721704733213853)
                    ·
                      refine ⟨3671393354895639274955195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9790382279721704733213853 3671393354895639274955195)
                      ·
                        rfl

theorem cell23_7150013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_7150013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150013 prefixEnd_7150013 := by exact prefixLift 7150013
  have htrace : WordTrace (prefixWord ++ tailWord_7150013) baseStart_7150013 baseEnd_7150013 := by
    simpa [prefixWord, tailWord_7150013, baseEnd_7150013] using wordTrace_append hprefix tailTrace_7150013
  have hstable : (prefixWord ++ tailWord_7150013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150013).length < 2 ^ (prefixWord ++ tailWord_7150013).sum := by decide
  have hdescent : baseEnd_7150013 < baseStart_7150013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7150020 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_7150020 : Nat := 118140960795 + 7150020 * 2 ^ 59
def prefixEnd_7150020 : Nat := 4983230072969 + 3 ^ 40 * 7150020 * 2
def baseEnd_7150020 : Nat := 1223798983086740249189221

theorem tailTrace_7150020 : CollatzResearch.WordTrace tailWord_7150020 prefixEnd_7150020 1223798983086740249189221 := by
  unfold tailWord_7150020
  simp only [CollatzResearch.WordTrace]
  refine ⟨130391326778353070521143757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173855102371137427361525009 130391326778353070521143757)
  ·
    refine ⟨48896747541882401445428909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130391326778353070521143757 48896747541882401445428909)
    ·
      refine ⟨18336280328205900542035841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48896747541882401445428909 18336280328205900542035841)
      ·
        refine ⟨13752210246154425406526881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18336280328205900542035841 13752210246154425406526881)
        ·
          refine ⟨10314157684615819054895161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13752210246154425406526881 10314157684615819054895161)
          ·
            refine ⟨7735618263461864291171371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10314157684615819054895161 7735618263461864291171371)
            ·
              refine ⟨11603427395192796436757057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735618263461864291171371 11603427395192796436757057)
              ·
                refine ⟨8702570546394597327567793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11603427395192796436757057 8702570546394597327567793)
                ·
                  refine ⟨6526927909795947995675845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702570546394597327567793 6526927909795947995675845)
                  ·
                    refine ⟨1223798983086740249189221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526927909795947995675845 1223798983086740249189221)
                    ·
                      rfl

theorem cell23_7150020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_7150020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7150020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7150020 prefixEnd_7150020 := by exact prefixLift 7150020
  have htrace : WordTrace (prefixWord ++ tailWord_7150020) baseStart_7150020 baseEnd_7150020 := by
    simpa [prefixWord, tailWord_7150020, baseEnd_7150020] using wordTrace_append hprefix tailTrace_7150020
  have hstable : (prefixWord ++ tailWord_7150020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7150020).length < 2 ^ (prefixWord ++ tailWord_7150020).sum := by decide
  have hdescent : baseEnd_7150020 < baseStart_7150020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7150020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
