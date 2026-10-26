import V185TrunkScan23Chunk0665

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3937911 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 6, 2, 2]
def baseStart_3937911 : Nat := 118140960795 + 3937911 * 2 ^ 59
def prefixEnd_3937911 : Nat := 4983230072969 + 3 ^ 40 * 3937911 * 2
def baseEnd_3937911 : Nat := 2022041117627447638802383

theorem tailTrace_3937911 : CollatzResearch.WordTrace tailWord_3937911 prefixEnd_3937911 2022041117627447638802383 := by
  unfold tailWord_3937911
  simp only [CollatzResearch.WordTrace]
  refine ⟨143627413636628463500133587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95751609091085642333422391 143627413636628463500133587)
  ·
    refine ⟨215441120454942695250200381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143627413636628463500133587 215441120454942695250200381)
    ·
      refine ⟨80790420170603510718825143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215441120454942695250200381 80790420170603510718825143)
      ·
        refine ⟨121185630255905266078237715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80790420170603510718825143 121185630255905266078237715)
        ·
          refine ⟨181778445383857899117356573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121185630255905266078237715 181778445383857899117356573)
          ·
            refine ⟨68166917018946712169008715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181778445383857899117356573 68166917018946712169008715)
            ·
              refine ⟨102250375528420068253513073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68166917018946712169008715 102250375528420068253513073)
              ·
                refine ⟨76687781646315051190134805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102250375528420068253513073 76687781646315051190134805)
                ·
                  refine ⟨3594739764671018024537569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76687781646315051190134805 3594739764671018024537569)
                  ·
                    refine ⟨2696054823503263518403177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3594739764671018024537569 2696054823503263518403177)
                    ·
                      refine ⟨2022041117627447638802383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696054823503263518403177 2022041117627447638802383)
                      ·
                        rfl

theorem cell23_3937911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_3937911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937911 prefixEnd_3937911 := by exact prefixLift 3937911
  have htrace : WordTrace (prefixWord ++ tailWord_3937911) baseStart_3937911 baseEnd_3937911 := by
    simpa [prefixWord, tailWord_3937911, baseEnd_3937911] using wordTrace_append hprefix tailTrace_3937911
  have hstable : (prefixWord ++ tailWord_3937911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937911).length < 2 ^ (prefixWord ++ tailWord_3937911).sum := by decide
  have hdescent : baseEnd_3937911 < baseStart_3937911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937984 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_3937984 : Nat := 118140960795 + 3937984 * 2 ^ 59
def prefixEnd_3937984 : Nat := 4983230072969 + 3 ^ 40 * 3937984 * 2
def baseEnd_3937984 : Nat := 2022078601715225853189547

theorem tailTrace_3937984 : CollatzResearch.WordTrace tailWord_3937984 prefixEnd_3937984 2022078601715225853189547 := by
  unfold tailWord_3937984
  simp only [CollatzResearch.WordTrace]
  refine ⟨71815038082681998483770503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95753384110242664645027337 71815038082681998483770503)
  ·
    refine ⟨107722557124022997725655755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71815038082681998483770503 107722557124022997725655755)
    ·
      refine ⟨161583835686034496588483633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107722557124022997725655755 161583835686034496588483633)
      ·
        refine ⟨121187876764525872441362725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161583835686034496588483633 121187876764525872441362725)
        ·
          refine ⟨22722726893348601082755511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121187876764525872441362725 22722726893348601082755511)
          ·
            refine ⟨34084090340022901624133267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22722726893348601082755511 34084090340022901624133267)
            ·
              refine ⟨51126135510034352436199901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34084090340022901624133267 51126135510034352436199901)
              ·
                refine ⟨19172300816262882163574963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51126135510034352436199901 19172300816262882163574963)
                ·
                  refine ⟨28758451224394323245362445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19172300816262882163574963 28758451224394323245362445)
                  ·
                    refine ⟨10784419209147871217010917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28758451224394323245362445 10784419209147871217010917)
                    ·
                      refine ⟨2022078601715225853189547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10784419209147871217010917 2022078601715225853189547)
                      ·
                        rfl

theorem cell23_3937984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_3937984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3937984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3937984 prefixEnd_3937984 := by exact prefixLift 3937984
  have htrace : WordTrace (prefixWord ++ tailWord_3937984) baseStart_3937984 baseEnd_3937984 := by
    simpa [prefixWord, tailWord_3937984, baseEnd_3937984] using wordTrace_append hprefix tailTrace_3937984
  have hstable : (prefixWord ++ tailWord_3937984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937984).length < 2 ^ (prefixWord ++ tailWord_3937984).sum := by decide
  have hdescent : baseEnd_3937984 < baseStart_3937984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938001 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_3938001 : Nat := 118140960795 + 3938001 * 2 ^ 59
def prefixEnd_3938001 : Nat := 4983230072969 + 3 ^ 40 * 3938001 * 2
def baseEnd_3938001 : Nat := 2022087330886352286676969

theorem tailTrace_3938001 : CollatzResearch.WordTrace tailWord_3938001 prefixEnd_3938001 2022087330886352286676969 := by
  unfold tailWord_3938001
  simp only [CollatzResearch.WordTrace]
  refine ⟨143630696206302408870909857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95753797470868272580606571 143630696206302408870909857)
  ·
    refine ⟨107723022154726806653182393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143630696206302408870909857 107723022154726806653182393)
    ·
      refine ⟨80792266616045104989886795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107723022154726806653182393 80792266616045104989886795)
      ·
        refine ⟨121188399924067657484830193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80792266616045104989886795 121188399924067657484830193)
        ·
          refine ⟨90891299943050743113622645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121188399924067657484830193 90891299943050743113622645)
          ·
            refine ⟨8521059369661007166902123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90891299943050743113622645 8521059369661007166902123)
            ·
              refine ⟨12781589054491510750353185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8521059369661007166902123 12781589054491510750353185)
              ·
                refine ⟨9586191790868633062764889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12781589054491510750353185 9586191790868633062764889)
                ·
                  refine ⟨7189643843151474797073667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9586191790868633062764889 7189643843151474797073667)
                  ·
                    refine ⟨10784465764727212195610501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7189643843151474797073667 10784465764727212195610501)
                    ·
                      refine ⟨2022087330886352286676969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10784465764727212195610501 2022087330886352286676969)
                      ·
                        rfl

theorem cell23_3938001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_3938001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938001 prefixEnd_3938001 := by exact prefixLift 3938001
  have htrace : WordTrace (prefixWord ++ tailWord_3938001) baseStart_3938001 baseEnd_3938001 := by
    simpa [prefixWord, tailWord_3938001, baseEnd_3938001] using wordTrace_append hprefix tailTrace_3938001
  have hstable : (prefixWord ++ tailWord_3938001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938001).length < 2 ^ (prefixWord ++ tailWord_3938001).sum := by decide
  have hdescent : baseEnd_3938001 < baseStart_3938001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938021 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3938021 : Nat := 118140960795 + 3938021 * 2 ^ 59
def prefixEnd_3938021 : Nat := 4983230072969 + 3 ^ 40 * 3938021 * 2
def baseEnd_3938021 : Nat := 2022097600499442208426877

theorem tailTrace_3938021 : CollatzResearch.WordTrace tailWord_3938021 prefixEnd_3938021 2022097600499442208426877 := by
  unfold tailWord_3938021
  simp only [CollatzResearch.WordTrace]
  refine ⟨143631425666229952286637917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95754283777486634857758611 143631425666229952286637917)
  ·
    refine ⟨53861784624836232107489219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143631425666229952286637917 53861784624836232107489219)
    ·
      refine ⟨80792676937254348161233829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53861784624836232107489219 80792676937254348161233829)
      ·
        refine ⟨15148626925735190280231343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80792676937254348161233829 15148626925735190280231343)
        ·
          refine ⟨22722940388602785420347015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15148626925735190280231343 22722940388602785420347015)
          ·
            refine ⟨34084410582904178130520523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22722940388602785420347015 34084410582904178130520523)
            ·
              refine ⟨51126615874356267195780785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34084410582904178130520523 51126615874356267195780785)
              ·
                refine ⟨38344961905767200396835589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51126615874356267195780785 38344961905767200396835589)
                ·
                  refine ⟨7189680357331350074406673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38344961905767200396835589 7189680357331350074406673)
                  ·
                    refine ⟨5392260267998512555805005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7189680357331350074406673 5392260267998512555805005)
                    ·
                      refine ⟨2022097600499442208426877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5392260267998512555805005 2022097600499442208426877)
                      ·
                        rfl

theorem cell23_3938021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3938021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938021 prefixEnd_3938021 := by exact prefixLift 3938021
  have htrace : WordTrace (prefixWord ++ tailWord_3938021) baseStart_3938021 baseEnd_3938021 := by
    simpa [prefixWord, tailWord_3938021, baseEnd_3938021] using wordTrace_append hprefix tailTrace_3938021
  have hstable : (prefixWord ++ tailWord_3938021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938021).length < 2 ^ (prefixWord ++ tailWord_3938021).sum := by decide
  have hdescent : baseEnd_3938021 < baseStart_3938021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938038 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3938038 : Nat := 118140960795 + 3938038 * 2 ^ 59
def prefixEnd_3938038 : Nat := 4983230072969 + 3 ^ 40 * 3938038 * 2
def baseEnd_3938038 : Nat := 2022106329670568641914299

theorem tailTrace_3938038 : CollatzResearch.WordTrace tailWord_3938038 prefixEnd_3938038 2022106329670568641914299 := by
  unfold tailWord_3938038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977002856698022761875423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95754697138112242793337845 8977002856698022761875423)
  ·
    refine ⟨13465504285047034142813135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8977002856698022761875423 13465504285047034142813135)
    ·
      refine ⟨20198256427570551214219703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13465504285047034142813135 20198256427570551214219703)
      ·
        refine ⟨30297384641355826821329555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20198256427570551214219703 30297384641355826821329555)
        ·
          refine ⟨45446076962033740231994333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30297384641355826821329555 45446076962033740231994333)
          ·
            refine ⟨17042278860762652586997875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45446076962033740231994333 17042278860762652586997875)
            ·
              refine ⟨25563418291143978880496813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042278860762652586997875 25563418291143978880496813)
              ·
                refine ⟨9586281859178992080186305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25563418291143978880496813 9586281859178992080186305)
                ·
                  refine ⟨7189711394384244060139729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9586281859178992080186305 7189711394384244060139729)
                  ·
                    refine ⟨5392283545788183045104797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7189711394384244060139729 5392283545788183045104797)
                    ·
                      refine ⟨2022106329670568641914299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5392283545788183045104797 2022106329670568641914299)
                      ·
                        rfl

theorem cell23_3938038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3938038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938038 prefixEnd_3938038 := by exact prefixLift 3938038
  have htrace : WordTrace (prefixWord ++ tailWord_3938038) baseStart_3938038 baseEnd_3938038 := by
    simpa [prefixWord, tailWord_3938038, baseEnd_3938038] using wordTrace_append hprefix tailTrace_3938038
  have hstable : (prefixWord ++ tailWord_3938038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938038).length < 2 ^ (prefixWord ++ tailWord_3938038).sum := by decide
  have hdescent : baseEnd_3938038 < baseStart_3938038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938071 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 3, 5]
def baseStart_3938071 : Nat := 118140960795 + 3938071 * 2 ^ 59
def prefixEnd_3938071 : Nat := 4983230072969 + 3 ^ 40 * 3938071 * 2
def baseEnd_3938071 : Nat := 674041091510722337600549

theorem tailTrace_3938071 : CollatzResearch.WordTrace tailWord_3938071 prefixEnd_3938071 674041091510722337600549 := by
  unfold tailWord_3938071
  simp only [CollatzResearch.WordTrace]
  refine ⟨143633249316048810825958067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95755499544032540550638711 143633249316048810825958067)
  ·
    refine ⟨215449873974073216238937101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143633249316048810825958067 215449873974073216238937101)
    ·
      refine ⟨80793702740277456089601413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215449873974073216238937101 80793702740277456089601413)
      ·
        refine ⟨15148819263802023016800265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80793702740277456089601413 15148819263802023016800265)
        ·
          refine ⟨11361614447851517262600199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15148819263802023016800265 11361614447851517262600199)
          ·
            refine ⟨17042421671777275893900299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361614447851517262600199 17042421671777275893900299)
            ·
              refine ⟨25563632507665913840850449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042421671777275893900299 25563632507665913840850449)
              ·
                refine ⟨19172724380749435380637837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25563632507665913840850449 19172724380749435380637837)
                ·
                  refine ⟨7189771642781038267739189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19172724380749435380637837 7189771642781038267739189)
                  ·
                    refine ⟨674041091510722337600549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7189771642781038267739189 674041091510722337600549)
                    ·
                      rfl

theorem cell23_3938071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_3938071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938071 prefixEnd_3938071 := by exact prefixLift 3938071
  have htrace : WordTrace (prefixWord ++ tailWord_3938071) baseStart_3938071 baseEnd_3938071 := by
    simpa [prefixWord, tailWord_3938071, baseEnd_3938071] using wordTrace_append hprefix tailTrace_3938071
  have hstable : (prefixWord ++ tailWord_3938071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938071).length < 2 ^ (prefixWord ++ tailWord_3938071).sum := by decide
  have hdescent : baseEnd_3938071 < baseStart_3938071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938105 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 1, 5]
def baseStart_3938105 : Nat := 118140960795 + 3938105 * 2 ^ 59
def prefixEnd_3938105 : Nat := 4983230072969 + 3 ^ 40 * 3938105 * 2
def baseEnd_3938105 : Nat := 674046910958139959925497

theorem tailTrace_3938105 : CollatzResearch.WordTrace tailWord_3938105 prefixEnd_3938105 674046910958139959925497 := by
  unfold tailWord_3938105
  simp only [CollatzResearch.WordTrace]
  refine ⟨143634489397925634632695769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95756326265283756421797179 143634489397925634632695769)
  ·
    refine ⟨107725867048444225974521827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143634489397925634632695769 107725867048444225974521827)
    ·
      refine ⟨161588800572666338961782741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107725867048444225974521827 161588800572666338961782741)
      ·
        refine ⟨3787237513421867319416783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 161588800572666338961782741 3787237513421867319416783)
        ·
          refine ⟨5680856270132800979125175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787237513421867319416783 5680856270132800979125175)
          ·
            refine ⟨8521284405199201468687763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5680856270132800979125175 8521284405199201468687763)
            ·
              refine ⟨12781926607798802203031645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8521284405199201468687763 12781926607798802203031645)
              ·
                refine ⟨4793222477924550826136867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12781926607798802203031645 4793222477924550826136867)
                ·
                  refine ⟨7189833716886826239205301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793222477924550826136867 7189833716886826239205301)
                  ·
                    refine ⟨674046910958139959925497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7189833716886826239205301 674046910958139959925497)
                    ·
                      rfl

theorem cell23_3938105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_3938105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938105 prefixEnd_3938105 := by exact prefixLift 3938105
  have htrace : WordTrace (prefixWord ++ tailWord_3938105) baseStart_3938105 baseEnd_3938105 := by
    simpa [prefixWord, tailWord_3938105, baseEnd_3938105] using wordTrace_append hprefix tailTrace_3938105
  have hstable : (prefixWord ++ tailWord_3938105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938105).length < 2 ^ (prefixWord ++ tailWord_3938105).sum := by decide
  have hdescent : baseEnd_3938105 < baseStart_3938105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938135 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 1, 6]
def baseStart_3938135 : Nat := 118140960795 + 3938135 * 2 ^ 59
def prefixEnd_3938135 : Nat := 4983230072969 + 3 ^ 40 * 3938135 * 2
def baseEnd_3938135 : Nat := 674052045764684920800451

theorem tailTrace_3938135 : CollatzResearch.WordTrace tailWord_3938135 prefixEnd_3938135 674052045764684920800451 := by
  unfold tailWord_3938135
  simp only [CollatzResearch.WordTrace]
  refine ⟨143635583587816949756287859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95757055725211299837525239 143635583587816949756287859)
  ·
    refine ⟨215453375381725424634431789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143635583587816949756287859 215453375381725424634431789)
    ·
      refine ⟨80795015768147034237911921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215453375381725424634431789 80795015768147034237911921)
      ·
        refine ⟨60596261826110275678433941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80795015768147034237911921 60596261826110275678433941)
        ·
          refine ⟨2840449773098919172426591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60596261826110275678433941 2840449773098919172426591)
          ·
            refine ⟨4260674659648378758639887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840449773098919172426591 4260674659648378758639887)
            ·
              refine ⟨6391011989472568137959831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260674659648378758639887 6391011989472568137959831)
              ·
                refine ⟨9586517984208852206939747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6391011989472568137959831 9586517984208852206939747)
                ·
                  refine ⟨14379776976313278310409621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9586517984208852206939747 14379776976313278310409621)
                  ·
                    refine ⟨674052045764684920800451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14379776976313278310409621 674052045764684920800451)
                    ·
                      rfl

theorem cell23_3938135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_3938135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938135 prefixEnd_3938135 := by exact prefixLift 3938135
  have htrace : WordTrace (prefixWord ++ tailWord_3938135) baseStart_3938135 baseEnd_3938135 := by
    simpa [prefixWord, tailWord_3938135, baseEnd_3938135] using wordTrace_append hprefix tailTrace_3938135
  have hstable : (prefixWord ++ tailWord_3938135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938135).length < 2 ^ (prefixWord ++ tailWord_3938135).sum := by decide
  have hdescent : baseEnd_3938135 < baseStart_3938135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938181 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3938181 : Nat := 118140960795 + 3938181 * 2 ^ 59
def prefixEnd_3938181 : Nat := 4983230072969 + 3 ^ 40 * 3938181 * 2
def baseEnd_3938181 : Nat := 2022179757404161582426141

theorem tailTrace_3938181 : CollatzResearch.WordTrace tailWord_3938181 prefixEnd_3938181 2022179757404161582426141 := by
  unfold tailWord_3938181
  simp only [CollatzResearch.WordTrace]
  refine ⟨143637261345650299612462397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95758174230433533074974931 143637261345650299612462397)
  ·
    refine ⟨53863973004618862354673399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143637261345650299612462397 53863973004618862354673399)
    ·
      refine ⟨80795959506928293532010099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53863973004618862354673399 80795959506928293532010099)
      ·
        refine ⟨121193939260392440298015149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80795959506928293532010099 121193939260392440298015149)
        ·
          refine ⟨45447727222647165111755681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121193939260392440298015149 45447727222647165111755681)
          ·
            refine ⟨34085795416985373833816761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45447727222647165111755681 34085795416985373833816761)
            ·
              refine ⟨25564346562739030375362571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34085795416985373833816761 25564346562739030375362571)
              ·
                refine ⟨38346519844108545563043857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564346562739030375362571 38346519844108545563043857)
                ·
                  refine ⟨28759889883081409172282893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38346519844108545563043857 28759889883081409172282893)
                  ·
                    refine ⟨10784958706155528439606085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28759889883081409172282893 10784958706155528439606085)
                    ·
                      refine ⟨2022179757404161582426141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10784958706155528439606085 2022179757404161582426141)
                      ·
                        rfl

theorem cell23_3938181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3938181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938181 prefixEnd_3938181 := by exact prefixLift 3938181
  have htrace : WordTrace (prefixWord ++ tailWord_3938181) baseStart_3938181 baseEnd_3938181 := by
    simpa [prefixWord, tailWord_3938181, baseEnd_3938181] using wordTrace_append hprefix tailTrace_3938181
  have hstable : (prefixWord ++ tailWord_3938181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938181).length < 2 ^ (prefixWord ++ tailWord_3938181).sum := by decide
  have hdescent : baseEnd_3938181 < baseStart_3938181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938201 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_3938201 : Nat := 118140960795 + 3938201 * 2 ^ 59
def prefixEnd_3938201 : Nat := 4983230072969 + 3 ^ 40 * 3938201 * 2
def baseEnd_3938201 : Nat := 2022190027017251504176049

theorem tailTrace_3938201 : CollatzResearch.WordTrace tailWord_3938201 prefixEnd_3938201 2022190027017251504176049 := by
  unfold tailWord_3938201
  simp only [CollatzResearch.WordTrace]
  refine ⟨143637990805577843028190457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95758660537051895352126971 143637990805577843028190457)
  ·
    refine ⟨107728493104183382271142843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143637990805577843028190457 107728493104183382271142843)
    ·
      refine ⟨161592739656275073406714265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107728493104183382271142843 161592739656275073406714265)
      ·
        refine ⟨121194554742206305055035699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161592739656275073406714265 121194554742206305055035699)
        ·
          refine ⟨181791832113309457582553549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121194554742206305055035699 181791832113309457582553549)
          ·
            refine ⟨68171937042491046593457581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181791832113309457582553549 68171937042491046593457581)
            ·
              refine ⟨25564476390934142472546593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68171937042491046593457581 25564476390934142472546593)
              ·
                refine ⟨19173357293200606854409945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25564476390934142472546593 19173357293200606854409945)
                ·
                  refine ⟨14380017969900455140807459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19173357293200606854409945 14380017969900455140807459)
                  ·
                    refine ⟨21570026954850682711211189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14380017969900455140807459 21570026954850682711211189)
                    ·
                      refine ⟨2022190027017251504176049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21570026954850682711211189 2022190027017251504176049)
                      ·
                        rfl

theorem cell23_3938201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_3938201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938201 prefixEnd_3938201 := by exact prefixLift 3938201
  have htrace : WordTrace (prefixWord ++ tailWord_3938201) baseStart_3938201 baseEnd_3938201 := by
    simpa [prefixWord, tailWord_3938201, baseEnd_3938201] using wordTrace_append hprefix tailTrace_3938201
  have hstable : (prefixWord ++ tailWord_3938201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938201).length < 2 ^ (prefixWord ++ tailWord_3938201).sum := by decide
  have hdescent : baseEnd_3938201 < baseStart_3938201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938202 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2]
def baseStart_3938202 : Nat := 118140960795 + 3938202 * 2 ^ 59
def prefixEnd_3938202 : Nat := 4983230072969 + 3 ^ 40 * 3938202 * 2
def baseEnd_3938202 : Nat := 2022190540497906000263545

theorem tailTrace_3938202 : CollatzResearch.WordTrace tailWord_3938202 prefixEnd_3938202 2022190540497906000263545 := by
  unfold tailWord_3938202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35909506819643555049744215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95758684852382813465984573 35909506819643555049744215)
  ·
    refine ⟨53864260229465332574616323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35909506819643555049744215 53864260229465332574616323)
    ·
      refine ⟨80796390344197998861924485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53864260229465332574616323 80796390344197998861924485)
      ·
        refine ⟨15149323189537124786610841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80796390344197998861924485 15149323189537124786610841)
        ·
          refine ⟨11361992392152843589958131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15149323189537124786610841 11361992392152843589958131)
          ·
            refine ⟨17042988588229265384937197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361992392152843589958131 17042988588229265384937197)
            ·
              refine ⟨6391120720585974519351449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17042988588229265384937197 6391120720585974519351449)
              ·
                refine ⟨4793340540439480889513587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391120720585974519351449 4793340540439480889513587)
                ·
                  refine ⟨7190010810659221334270381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793340540439480889513587 7190010810659221334270381)
                  ·
                    refine ⟨2696254053997208000351393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7190010810659221334270381 2696254053997208000351393)
                    ·
                      refine ⟨2022190540497906000263545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696254053997208000351393 2022190540497906000263545)
                      ·
                        rfl

theorem cell23_3938202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_3938202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938202 prefixEnd_3938202 := by exact prefixLift 3938202
  have htrace : WordTrace (prefixWord ++ tailWord_3938202) baseStart_3938202 baseEnd_3938202 := by
    simpa [prefixWord, tailWord_3938202, baseEnd_3938202] using wordTrace_append hprefix tailTrace_3938202
  have hstable : (prefixWord ++ tailWord_3938202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938202).length < 2 ^ (prefixWord ++ tailWord_3938202).sum := by decide
  have hdescent : baseEnd_3938202 < baseStart_3938202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938211 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3938211 : Nat := 118140960795 + 3938211 * 2 ^ 59
def prefixEnd_3938211 : Nat := 4983230072969 + 3 ^ 40 * 3938211 * 2
def baseEnd_3938211 : Nat := 2022195161823796465051003

theorem tailTrace_3938211 : CollatzResearch.WordTrace tailWord_3938211 prefixEnd_3938211 2022195161823796465051003 := by
  unfold tailWord_3938211
  simp only [CollatzResearch.WordTrace]
  refine ⟨143638355535541614736054487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95758903690361076490702991 143638355535541614736054487)
  ·
    refine ⟨215457533303312422104081731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143638355535541614736054487 215457533303312422104081731)
    ·
      refine ⟨323186299954968633156122597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215457533303312422104081731 323186299954968633156122597)
      ·
        refine ⟨60597431241556618716772987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323186299954968633156122597 60597431241556618716772987)
        ·
          refine ⟨90896146862334928075159481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60597431241556618716772987 90896146862334928075159481)
          ·
            refine ⟨68172110146751196056369611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90896146862334928075159481 68172110146751196056369611)
            ·
              refine ⟨102258165220126794084554417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68172110146751196056369611 102258165220126794084554417)
              ·
                refine ⟨76693623915095095563415813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102258165220126794084554417 76693623915095095563415813)
                ·
                  refine ⟨14380054484080330418140465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76693623915095095563415813 14380054484080330418140465)
                  ·
                    refine ⟨10785040863060247813605349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14380054484080330418140465 10785040863060247813605349)
                    ·
                      refine ⟨2022195161823796465051003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10785040863060247813605349 2022195161823796465051003)
                      ·
                        rfl

theorem cell23_3938211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3938211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938211 prefixEnd_3938211 := by exact prefixLift 3938211
  have htrace : WordTrace (prefixWord ++ tailWord_3938211) baseStart_3938211 baseEnd_3938211 := by
    simpa [prefixWord, tailWord_3938211, baseEnd_3938211] using wordTrace_append hprefix tailTrace_3938211
  have hstable : (prefixWord ++ tailWord_3938211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938211).length < 2 ^ (prefixWord ++ tailWord_3938211).sum := by decide
  have hdescent : baseEnd_3938211 < baseStart_3938211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938215 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_3938215 : Nat := 118140960795 + 3938215 * 2 ^ 59
def prefixEnd_3938215 : Nat := 4983230072969 + 3 ^ 40 * 3938215 * 2
def baseEnd_3938215 : Nat := 2022197215746414449400985

theorem tailTrace_3938215 : CollatzResearch.WordTrace tailWord_3938215 prefixEnd_3938215 2022197215746414449400985 := by
  unfold tailWord_3938215
  simp only [CollatzResearch.WordTrace]
  refine ⟨143638501427527123419200099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95759000951684748946133399 143638501427527123419200099)
  ·
    refine ⟨215457752141290685128800149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143638501427527123419200099 215457752141290685128800149)
    ·
      refine ⟨10099582131623000865412507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215457752141290685128800149 10099582131623000865412507)
      ·
        refine ⟨15149373197434501298118761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099582131623000865412507 15149373197434501298118761)
        ·
          refine ⟨11362029898075875973589071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15149373197434501298118761 11362029898075875973589071)
          ·
            refine ⟨17043044847113813960383607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362029898075875973589071 17043044847113813960383607)
            ·
              refine ⟨25564567270670720940575411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043044847113813960383607 25564567270670720940575411)
              ·
                refine ⟨38346850906006081410863117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564567270670720940575411 38346850906006081410863117)
                ·
                  refine ⟨14380069089752280529073669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38346850906006081410863117 14380069089752280529073669)
                  ·
                    refine ⟨2696262954328552599201313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14380069089752280529073669 2696262954328552599201313)
                    ·
                      refine ⟨2022197215746414449400985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696262954328552599201313 2022197215746414449400985)
                      ·
                        rfl

theorem cell23_3938215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_3938215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938215 prefixEnd_3938215 := by exact prefixLift 3938215
  have htrace : WordTrace (prefixWord ++ tailWord_3938215) baseStart_3938215 baseEnd_3938215 := by
    simpa [prefixWord, tailWord_3938215, baseEnd_3938215] using wordTrace_append hprefix tailTrace_3938215
  have hstable : (prefixWord ++ tailWord_3938215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938215).length < 2 ^ (prefixWord ++ tailWord_3938215).sum := by decide
  have hdescent : baseEnd_3938215 < baseStart_3938215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938232 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 2, 2, 2]
def baseStart_3938232 : Nat := 118140960795 + 3938232 * 2 ^ 59
def prefixEnd_3938232 : Nat := 4983230072969 + 3 ^ 40 * 3938232 * 2
def baseEnd_3938232 : Nat := 2022205944917540882888407

theorem tailTrace_3938232 : CollatzResearch.WordTrace tailWord_3938232 prefixEnd_3938232 2022205944917540882888407 := by
  unfold tailWord_3938232
  simp only [CollatzResearch.WordTrace]
  refine ⟨71819560734232767661284475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95759414312310356881712633 71819560734232767661284475)
  ·
    refine ⟨107729341101349151491926713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71819560734232767661284475 107729341101349151491926713)
    ·
      refine ⟨80797005826011863618945035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107729341101349151491926713 80797005826011863618945035)
      ·
        refine ⟨121195508739017795428417553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80797005826011863618945035 121195508739017795428417553)
        ·
          refine ⟨90896631554263346571313165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121195508739017795428417553 90896631554263346571313165)
          ·
            refine ⟨34086236832848754964242437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90896631554263346571313165 34086236832848754964242437)
            ·
              refine ⟨6391169406159141555795457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34086236832848754964242437 6391169406159141555795457)
              ·
                refine ⟨4793377054619356166846593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391169406159141555795457 4793377054619356166846593)
                ·
                  refine ⟨3595032790964517125134945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4793377054619356166846593 3595032790964517125134945)
                  ·
                    refine ⟨2696274593223387843851209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3595032790964517125134945 2696274593223387843851209)
                    ·
                      refine ⟨2022205944917540882888407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696274593223387843851209 2022205944917540882888407)
                      ·
                        rfl

theorem cell23_3938232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_3938232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938232 prefixEnd_3938232 := by exact prefixLift 3938232
  have htrace : WordTrace (prefixWord ++ tailWord_3938232) baseStart_3938232 baseEnd_3938232 := by
    simpa [prefixWord, tailWord_3938232, baseEnd_3938232] using wordTrace_append hprefix tailTrace_3938232
  have hstable : (prefixWord ++ tailWord_3938232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938232).length < 2 ^ (prefixWord ++ tailWord_3938232).sum := by decide
  have hdescent : baseEnd_3938232 < baseStart_3938232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938248 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_3938248 : Nat := 118140960795 + 3938248 * 2 ^ 59
def prefixEnd_3938248 : Nat := 4983230072969 + 3 ^ 40 * 3938248 * 2
def baseEnd_3938248 : Nat := 2022214160608012820288333

theorem tailTrace_3938248 : CollatzResearch.WordTrace tailWord_3938248 prefixEnd_3938248 2022214160608012820288333 := by
  unfold tailWord_3938248
  simp only [CollatzResearch.WordTrace]
  refine ⟨71819852518203785027575699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95759803357605046703434265 71819852518203785027575699)
  ·
    refine ⟨107729778777305677541363549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71819852518203785027575699 107729778777305677541363549)
    ·
      refine ⟨40398667041489629078011331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107729778777305677541363549 40398667041489629078011331)
      ·
        refine ⟨60598000562234443617016997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40398667041489629078011331 60598000562234443617016997)
        ·
          refine ⟨11362125105418958178190687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60598000562234443617016997 11362125105418958178190687)
          ·
            refine ⟨17043187658128437267286031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362125105418958178190687 17043187658128437267286031)
            ·
              refine ⟨25564781487192655900929047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043187658128437267286031 25564781487192655900929047)
              ·
                refine ⟨38347172230788983851393571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564781487192655900929047 38347172230788983851393571)
                ·
                  refine ⟨57520758346183475777090357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38347172230788983851393571 57520758346183475777090357)
                  ·
                    refine ⟨5392571094954700854102221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57520758346183475777090357 5392571094954700854102221)
                    ·
                      refine ⟨2022214160608012820288333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5392571094954700854102221 2022214160608012820288333)
                      ·
                        rfl

theorem cell23_3938248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_3938248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938248 prefixEnd_3938248 := by exact prefixLift 3938248
  have htrace : WordTrace (prefixWord ++ tailWord_3938248) baseStart_3938248 baseEnd_3938248 := by
    simpa [prefixWord, tailWord_3938248, baseEnd_3938248] using wordTrace_append hprefix tailTrace_3938248
  have hstable : (prefixWord ++ tailWord_3938248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938248).length < 2 ^ (prefixWord ++ tailWord_3938248).sum := by decide
  have hdescent : baseEnd_3938248 < baseStart_3938248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938251 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 1, 7]
def baseStart_3938251 : Nat := 118140960795 + 3938251 * 2 ^ 59
def prefixEnd_3938251 : Nat := 4983230072969 + 3 ^ 40 * 3938251 * 2
def baseEnd_3938251 : Nat := 674071900349992102850273

theorem tailTrace_3938251 : CollatzResearch.WordTrace tailWord_3938251 prefixEnd_3938251 674071900349992102850273 := by
  unfold tailWord_3938251
  simp only [CollatzResearch.WordTrace]
  refine ⟨143639814455396701567510607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95759876303597801045007071 143639814455396701567510607)
  ·
    refine ⟨215459721683095052351265911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143639814455396701567510607 215459721683095052351265911)
    ·
      refine ⟨323189582524642578526898867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215459721683095052351265911 323189582524642578526898867)
      ·
        refine ⟨484784373786963867790348301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323189582524642578526898867 484784373786963867790348301)
        ·
          refine ⟨181794140170111450421380613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484784373786963867790348301 181794140170111450421380613)
          ·
            refine ⟨34086401281895896954008865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181794140170111450421380613 34086401281895896954008865)
            ·
              refine ⟨25564800961421922715506649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34086401281895896954008865 25564800961421922715506649)
              ·
                refine ⟨19173600721066442036629987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25564800961421922715506649 19173600721066442036629987)
                ·
                  refine ⟨28760401081599663054944981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19173600721066442036629987 28760401081599663054944981)
                  ·
                    refine ⟨674071900349992102850273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28760401081599663054944981 674071900349992102850273)
                    ·
                      rfl

theorem cell23_3938251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 7].length) (baseStart_3938251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938251 prefixEnd_3938251 := by exact prefixLift 3938251
  have htrace : WordTrace (prefixWord ++ tailWord_3938251) baseStart_3938251 baseEnd_3938251 := by
    simpa [prefixWord, tailWord_3938251, baseEnd_3938251] using wordTrace_append hprefix tailTrace_3938251
  have hstable : (prefixWord ++ tailWord_3938251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938251).length < 2 ^ (prefixWord ++ tailWord_3938251).sum := by decide
  have hdescent : baseEnd_3938251 < baseStart_3938251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938288 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_3938288 : Nat := 118140960795 + 3938288 * 2 ^ 59
def prefixEnd_3938288 : Nat := 4983230072969 + 3 ^ 40 * 3938288 * 2
def baseEnd_3938288 : Nat := 2022234699834192663788149

theorem tailTrace_3938288 : CollatzResearch.WordTrace tailWord_3938288 prefixEnd_3938288 2022234699834192663788149 := by
  unfold tailWord_3938288
  simp only [CollatzResearch.WordTrace]
  refine ⟨71820581978131328443303759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95760775970841771257738345 71820581978131328443303759)
  ·
    refine ⟨107730872967196992664955639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71820581978131328443303759 107730872967196992664955639)
    ·
      refine ⟨161596309450795488997433459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107730872967196992664955639 161596309450795488997433459)
      ·
        refine ⟨242394464176193233496150189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161596309450795488997433459 242394464176193233496150189)
        ·
          refine ⟨90897924066072462561056321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242394464176193233496150189 90897924066072462561056321)
          ·
            refine ⟨68173443049554346920792241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90897924066072462561056321 68173443049554346920792241)
            ·
              refine ⟨51130082287165760190594181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68173443049554346920792241 51130082287165760190594181)
              ·
                refine ⟨9586890428843580035736409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51130082287165760190594181 9586890428843580035736409)
                ·
                  refine ⟨7190167821632685026802307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9586890428843580035736409 7190167821632685026802307)
                  ·
                    refine ⟨10785251732449027540203461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7190167821632685026802307 10785251732449027540203461)
                    ·
                      refine ⟨2022234699834192663788149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10785251732449027540203461 2022234699834192663788149)
                      ·
                        rfl

theorem cell23_3938288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_3938288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938288 prefixEnd_3938288 := by exact prefixLift 3938288
  have htrace : WordTrace (prefixWord ++ tailWord_3938288) baseStart_3938288 baseEnd_3938288 := by
    simpa [prefixWord, tailWord_3938288, baseEnd_3938288] using wordTrace_append hprefix tailTrace_3938288
  have hstable : (prefixWord ++ tailWord_3938288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938288).length < 2 ^ (prefixWord ++ tailWord_3938288).sum := by decide
  have hdescent : baseEnd_3938288 < baseStart_3938288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938291 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5]
def baseStart_3938291 : Nat := 118140960795 + 3938291 * 2 ^ 59
def prefixEnd_3938291 : Nat := 4983230072969 + 3 ^ 40 * 3938291 * 2
def baseEnd_3938291 : Nat := 2022236240276156152050635

theorem tailTrace_3938291 : CollatzResearch.WordTrace tailWord_3938291 prefixEnd_3938291 2022236240276156152050635 := by
  unfold tailWord_3938291
  simp only [CollatzResearch.WordTrace]
  refine ⟨143641273375251788398966727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95760848916834525599311151 143641273375251788398966727)
  ·
    refine ⟨215461910062877682598450091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143641273375251788398966727 215461910062877682598450091)
    ·
      refine ⟨323192865094316523897675137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215461910062877682598450091 323192865094316523897675137)
      ·
        refine ⟨242394648820737392923256353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323192865094316523897675137 242394648820737392923256353)
        ·
          refine ⟨181795986615553044692442265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242394648820737392923256353 181795986615553044692442265)
          ·
            refine ⟨136346989961664783519331699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181795986615553044692442265 136346989961664783519331699)
            ·
              refine ⟨204520484942497175278997549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136346989961664783519331699 204520484942497175278997549)
              ·
                refine ⟨76695181853436440729624081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204520484942497175278997549 76695181853436440729624081)
                ·
                  refine ⟨57521386390077330547218061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76695181853436440729624081 57521386390077330547218061)
                  ·
                    refine ⟨21570519896278998955206773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57521386390077330547218061 21570519896278998955206773)
                    ·
                      refine ⟨2022236240276156152050635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21570519896278998955206773 2022236240276156152050635)
                      ·
                        rfl

theorem cell23_3938291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_3938291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938291 prefixEnd_3938291 := by exact prefixLift 3938291
  have htrace : WordTrace (prefixWord ++ tailWord_3938291) baseStart_3938291 baseEnd_3938291 := by
    simpa [prefixWord, tailWord_3938291, baseEnd_3938291] using wordTrace_append hprefix tailTrace_3938291
  have hstable : (prefixWord ++ tailWord_3938291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938291).length < 2 ^ (prefixWord ++ tailWord_3938291).sum := by decide
  have hdescent : baseEnd_3938291 < baseStart_3938291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938305 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_3938305 : Nat := 118140960795 + 3938305 * 2 ^ 59
def prefixEnd_3938305 : Nat := 4983230072969 + 3 ^ 40 * 3938305 * 2
def baseEnd_3938305 : Nat := 2022243429005319097275571

theorem tailTrace_3938305 : CollatzResearch.WordTrace tailWord_3938305 prefixEnd_3938305 2022243429005319097275571 := by
  unfold tailWord_3938305
  simp only [CollatzResearch.WordTrace]
  refine ⟨143641783997201068789976369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95761189331467379193317579 143641783997201068789976369)
  ·
    refine ⟨107731337997900801592482277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143641783997201068789976369 107731337997900801592482277)
    ·
      refine ⟨20199625874606400298590427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107731337997900801592482277 20199625874606400298590427)
      ·
        refine ⟨30299438811909600447885641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20199625874606400298590427 30299438811909600447885641)
        ·
          refine ⟨22724579108932200335914231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30299438811909600447885641 22724579108932200335914231)
          ·
            refine ⟨34086868663398300503871347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22724579108932200335914231 34086868663398300503871347)
            ·
              refine ⟨51130302995097450755807021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34086868663398300503871347 51130302995097450755807021)
              ·
                refine ⟨19173863623161544033427633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51130302995097450755807021 19173863623161544033427633)
                ·
                  refine ⟨14380397717371158025070725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19173863623161544033427633 14380397717371158025070725)
                  ·
                    refine ⟨2696324572007092129700761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14380397717371158025070725 2696324572007092129700761)
                    ·
                      refine ⟨2022243429005319097275571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696324572007092129700761 2022243429005319097275571)
                      ·
                        rfl

theorem cell23_3938305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_3938305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938305 prefixEnd_3938305 := by exact prefixLift 3938305
  have htrace : WordTrace (prefixWord ++ tailWord_3938305) baseStart_3938305 baseEnd_3938305 := by
    simpa [prefixWord, tailWord_3938305, baseEnd_3938305] using wordTrace_append hprefix tailTrace_3938305
  have hstable : (prefixWord ++ tailWord_3938305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938305).length < 2 ^ (prefixWord ++ tailWord_3938305).sum := by decide
  have hdescent : baseEnd_3938305 < baseStart_3938305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938318 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3938318 : Nat := 118140960795 + 3938318 * 2 ^ 59
def prefixEnd_3938318 : Nat := 4983230072969 + 3 ^ 40 * 3938318 * 2
def baseEnd_3938318 : Nat := 2022250104253827546413011

theorem tailTrace_3938318 : CollatzResearch.WordTrace tailWord_3938318 prefixEnd_3938318 2022250104253827546413011 := by
  unfold tailWord_3938318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955282268269246501274951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95761505430769314673466405 17955282268269246501274951)
  ·
    refine ⟨26932923402403869751912427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955282268269246501274951 26932923402403869751912427)
    ·
      refine ⟨40399385103605804627868641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26932923402403869751912427 40399385103605804627868641)
      ·
        refine ⟨30299538827704353470901481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40399385103605804627868641 30299538827704353470901481)
        ·
          refine ⟨22724654120778265103176111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30299538827704353470901481 22724654120778265103176111)
          ·
            refine ⟨34086981181167397654764167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22724654120778265103176111 34086981181167397654764167)
            ·
              refine ⟨51130471771751096482146251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34086981181167397654764167 51130471771751096482146251)
              ·
                refine ⟨76695707657626644723219377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51130471771751096482146251 76695707657626644723219377)
                ·
                  refine ⟨57521780743219983542414533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76695707657626644723219377 57521780743219983542414533)
                  ·
                    refine ⟨10785333889353746914202725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57521780743219983542414533 10785333889353746914202725)
                    ·
                      refine ⟨2022250104253827546413011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10785333889353746914202725 2022250104253827546413011)
                      ·
                        rfl

theorem cell23_3938318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3938318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938318 prefixEnd_3938318 := by exact prefixLift 3938318
  have htrace : WordTrace (prefixWord ++ tailWord_3938318) baseStart_3938318 baseEnd_3938318 := by
    simpa [prefixWord, tailWord_3938318, baseEnd_3938318] using wordTrace_append hprefix tailTrace_3938318
  have hstable : (prefixWord ++ tailWord_3938318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938318).length < 2 ^ (prefixWord ++ tailWord_3938318).sum := by decide
  have hdescent : baseEnd_3938318 < baseStart_3938318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938321 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_3938321 : Nat := 118140960795 + 3938321 * 2 ^ 59
def prefixEnd_3938321 : Nat := 4983230072969 + 3 ^ 40 * 3938321 * 2
def baseEnd_3938321 : Nat := 2022251644695791034675497

theorem tailTrace_3938321 : CollatzResearch.WordTrace tailWord_3938321 prefixEnd_3938321 2022251644695791034675497 := by
  unfold tailWord_3938321
  simp only [CollatzResearch.WordTrace]
  refine ⟨143642367565143103522558817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95761578376762069015039211 143642367565143103522558817)
  ·
    refine ⟨107731775673857327641919113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143642367565143103522558817 107731775673857327641919113)
    ·
      refine ⟨80798831755392995731439335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107731775673857327641919113 80798831755392995731439335)
      ·
        refine ⟨121198247633089493597159003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80798831755392995731439335 121198247633089493597159003)
        ·
          refine ⟨181797371449634240395738505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121198247633089493597159003 181797371449634240395738505)
          ·
            refine ⟨136348028587225680296803879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181797371449634240395738505 136348028587225680296803879)
            ·
              refine ⟨204522042880838520445205819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136348028587225680296803879 204522042880838520445205819)
              ·
                refine ⟨306783064321257780667808729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204522042880838520445205819 306783064321257780667808729)
                ·
                  refine ⟨230087298240943335500856547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306783064321257780667808729 230087298240943335500856547)
                  ·
                    refine ⟨345130947361415003251284821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230087298240943335500856547 345130947361415003251284821)
                    ·
                      refine ⟨2022251644695791034675497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 345130947361415003251284821 2022251644695791034675497)
                      ·
                        rfl

theorem cell23_3938321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_3938321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938321 prefixEnd_3938321 := by exact prefixLift 3938321
  have htrace : WordTrace (prefixWord ++ tailWord_3938321) baseStart_3938321 baseEnd_3938321 := by
    simpa [prefixWord, tailWord_3938321, baseEnd_3938321] using wordTrace_append hprefix tailTrace_3938321
  have hstable : (prefixWord ++ tailWord_3938321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938321).length < 2 ^ (prefixWord ++ tailWord_3938321).sum := by decide
  have hdescent : baseEnd_3938321 < baseStart_3938321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938331 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8]
def baseStart_3938331 : Nat := 118140960795 + 3938331 * 2 ^ 59
def prefixEnd_3938331 : Nat := 4983230072969 + 3 ^ 40 * 3938331 * 2
def baseEnd_3938331 : Nat := 2022256779502335995550451

theorem tailTrace_3938331 : CollatzResearch.WordTrace tailWord_3938331 prefixEnd_3938331 2022256779502335995550451 := by
  unfold tailWord_3938331
  simp only [CollatzResearch.WordTrace]
  refine ⟨143642732295106875230422847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95761821530071250153615231 143642732295106875230422847)
  ·
    refine ⟨215464098442660312845634271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143642732295106875230422847 215464098442660312845634271)
    ·
      refine ⟨323196147663990469268451407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215464098442660312845634271 323196147663990469268451407)
      ·
        refine ⟨484794221495985703902677111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323196147663990469268451407 484794221495985703902677111)
        ·
          refine ⟨727191332243978555854015667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484794221495985703902677111 727191332243978555854015667)
          ·
            refine ⟨1090786998365967833781023501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727191332243978555854015667 1090786998365967833781023501)
            ·
              refine ⟨409045124387237937667883813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090786998365967833781023501 409045124387237937667883813)
              ·
                refine ⟨76695960822607113312728215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409045124387237937667883813 76695960822607113312728215)
                ·
                  refine ⟨115043941233910669969092323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76695960822607113312728215 115043941233910669969092323)
                  ·
                    refine ⟨172565911850866004953638485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115043941233910669969092323 172565911850866004953638485)
                    ·
                      refine ⟨2022256779502335995550451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 172565911850866004953638485 2022256779502335995550451)
                      ·
                        rfl

theorem cell23_3938331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_3938331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938331 prefixEnd_3938331 := by exact prefixLift 3938331
  have htrace : WordTrace (prefixWord ++ tailWord_3938331) baseStart_3938331 baseEnd_3938331 := by
    simpa [prefixWord, tailWord_3938331, baseEnd_3938331] using wordTrace_append hprefix tailTrace_3938331
  have hstable : (prefixWord ++ tailWord_3938331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938331).length < 2 ^ (prefixWord ++ tailWord_3938331).sum := by decide
  have hdescent : baseEnd_3938331 < baseStart_3938331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938382 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_3938382 : Nat := 118140960795 + 3938382 * 2 ^ 59
def prefixEnd_3938382 : Nat := 4983230072969 + 3 ^ 40 * 3938382 * 2
def baseEnd_3938382 : Nat := 2022282967015715296012717

theorem tailTrace_3938382 : CollatzResearch.WordTrace tailWord_3938382 prefixEnd_3938382 2022282967015715296012717 := by
  unfold tailWord_3938382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955574052240263867566175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95763061611948073960352933 17955574052240263867566175)
  ·
    refine ⟨26933361078360395801349263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955574052240263867566175 26933361078360395801349263)
    ·
      refine ⟨40400041617540593702023895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26933361078360395801349263 40400041617540593702023895)
      ·
        refine ⟨60600062426310890553035843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40400041617540593702023895 60600062426310890553035843)
        ·
          refine ⟨90900093639466335829553765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60600062426310890553035843 90900093639466335829553765)
          ·
            refine ⟨17043767557399937968041331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90900093639466335829553765 17043767557399937968041331)
            ·
              refine ⟨25565651336099906952061997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043767557399937968041331 25565651336099906952061997)
              ·
                refine ⟨9587119251037465107023249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25565651336099906952061997 9587119251037465107023249)
                ·
                  refine ⟨7190339438278098830267437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9587119251037465107023249 7190339438278098830267437)
                  ·
                    refine ⟨2696377289354287061350289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7190339438278098830267437 2696377289354287061350289)
                    ·
                      refine ⟨2022282967015715296012717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696377289354287061350289 2022282967015715296012717)
                      ·
                        rfl

theorem cell23_3938382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_3938382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938382 prefixEnd_3938382 := by exact prefixLift 3938382
  have htrace : WordTrace (prefixWord ++ tailWord_3938382) baseStart_3938382 baseEnd_3938382 := by
    simpa [prefixWord, tailWord_3938382, baseEnd_3938382] using wordTrace_append hprefix tailTrace_3938382
  have hstable : (prefixWord ++ tailWord_3938382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938382).length < 2 ^ (prefixWord ++ tailWord_3938382).sum := by decide
  have hdescent : baseEnd_3938382 < baseStart_3938382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938392 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 1, 5]
def baseStart_3938392 : Nat := 118140960795 + 3938392 * 2 ^ 59
def prefixEnd_3938392 : Nat := 4983230072969 + 3 ^ 40 * 3938392 * 2
def baseEnd_3938392 : Nat := 674096033940753418962557

theorem tailTrace_3938392 : CollatzResearch.WordTrace tailWord_3938392 prefixEnd_3938392 674096033940753418962557 := by
  unfold tailWord_3938392
  simp only [CollatzResearch.WordTrace]
  refine ⟨71822478573942941324196715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95763304765257255098928953 71822478573942941324196715)
  ·
    refine ⟨107733717860914411986295073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71822478573942941324196715 107733717860914411986295073)
    ·
      refine ⟨80800288395685808989721305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107733717860914411986295073 80800288395685808989721305)
      ·
        refine ⟨60600216296764356742290979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80800288395685808989721305 60600216296764356742290979)
        ·
          refine ⟨90900324445146535113436469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60600216296764356742290979 90900324445146535113436469)
          ·
            refine ⟨8521905416732487666884669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90900324445146535113436469 8521905416732487666884669)
            ·
              refine ⟨3195714531274682875081751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8521905416732487666884669 3195714531274682875081751)
              ·
                refine ⟨4793571796912024312622627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195714531274682875081751 4793571796912024312622627)
                ·
                  refine ⟨7190357695368036468933941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793571796912024312622627 7190357695368036468933941)
                  ·
                    refine ⟨674096033940753418962557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7190357695368036468933941 674096033940753418962557)
                    ·
                      rfl

theorem cell23_3938392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_3938392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938392 prefixEnd_3938392 := by exact prefixLift 3938392
  have htrace : WordTrace (prefixWord ++ tailWord_3938392) baseStart_3938392 baseEnd_3938392 := by
    simpa [prefixWord, tailWord_3938392, baseEnd_3938392] using wordTrace_append hprefix tailTrace_3938392
  have hstable : (prefixWord ++ tailWord_3938392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938392).length < 2 ^ (prefixWord ++ tailWord_3938392).sum := by decide
  have hdescent : baseEnd_3938392 < baseStart_3938392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938415 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 3]
def baseStart_3938415 : Nat := 118140960795 + 3938415 * 2 ^ 59
def prefixEnd_3938415 : Nat := 4983230072969 + 3 ^ 40 * 3938415 * 2
def baseEnd_3938415 : Nat := 2022299911877313666900065

theorem tailTrace_3938415 : CollatzResearch.WordTrace tailWord_3938415 prefixEnd_3938415 2022299911877313666900065 := by
  unfold tailWord_3938415
  simp only [CollatzResearch.WordTrace]
  refine ⟨143645796026802557576480699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95763864017868371717653799 143645796026802557576480699)
  ·
    refine ⟨215468694040203836364721049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143645796026802557576480699 215468694040203836364721049)
    ·
      refine ⟨161601520530152877273540787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215468694040203836364721049 161601520530152877273540787)
      ·
        refine ⟨242402280795229315910311181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161601520530152877273540787 242402280795229315910311181)
        ·
          refine ⟨90900855298210993466366693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242402280795229315910311181 90900855298210993466366693)
          ·
            refine ⟨17043910368414561274943755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90900855298210993466366693 17043910368414561274943755)
            ·
              refine ⟨25565865552621841912415633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043910368414561274943755 25565865552621841912415633)
              ·
                refine ⟨19174399164466381434311725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25565865552621841912415633 19174399164466381434311725)
                ·
                  refine ⟨7190399686674893037866897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19174399164466381434311725 7190399686674893037866897)
                  ·
                    refine ⟨5392799765006169778400173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7190399686674893037866897 5392799765006169778400173)
                    ·
                      refine ⟨2022299911877313666900065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5392799765006169778400173 2022299911877313666900065)
                      ·
                        rfl

theorem cell23_3938415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_3938415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938415 prefixEnd_3938415 := by exact prefixLift 3938415
  have htrace : WordTrace (prefixWord ++ tailWord_3938415) baseStart_3938415 baseEnd_3938415 := by
    simpa [prefixWord, tailWord_3938415, baseEnd_3938415] using wordTrace_append hprefix tailTrace_3938415
  have hstable : (prefixWord ++ tailWord_3938415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938415).length < 2 ^ (prefixWord ++ tailWord_3938415).sum := by decide
  have hdescent : baseEnd_3938415 < baseStart_3938415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938422 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_3938422 : Nat := 118140960795 + 3938422 * 2 ^ 59
def prefixEnd_3938422 : Nat := 4983230072969 + 3 ^ 40 * 3938422 * 2
def baseEnd_3938422 : Nat := 674101168747298379837511

theorem tailTrace_3938422 : CollatzResearch.WordTrace tailWord_3938422 prefixEnd_3938422 674101168747298379837511 := by
  unfold tailWord_3938422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977878208611074860749095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95764034225184798514657013 8977878208611074860749095)
  ·
    refine ⟨13466817312916612291123643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8977878208611074860749095 13466817312916612291123643)
    ·
      refine ⟨20200225969374918436685465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13466817312916612291123643 20200225969374918436685465)
      ·
        refine ⟨15150169477031188827514099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20200225969374918436685465 15150169477031188827514099)
        ·
          refine ⟨22725254215546783241271149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15150169477031188827514099 22725254215546783241271149)
          ·
            refine ⟨8521970330830043715476681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22725254215546783241271149 8521970330830043715476681)
            ·
              refine ⟨6391477748122532786607511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8521970330830043715476681 6391477748122532786607511)
              ·
                refine ⟨9587216622183799179911267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6391477748122532786607511 9587216622183799179911267)
                ·
                  refine ⟨14380824933275698769866901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9587216622183799179911267 14380824933275698769866901)
                  ·
                    refine ⟨674101168747298379837511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14380824933275698769866901 674101168747298379837511)
                    ·
                      rfl

theorem cell23_3938422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_3938422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938422 prefixEnd_3938422 := by exact prefixLift 3938422
  have htrace : WordTrace (prefixWord ++ tailWord_3938422) baseStart_3938422 baseEnd_3938422 := by
    simpa [prefixWord, tailWord_3938422, baseEnd_3938422] using wordTrace_append hprefix tailTrace_3938422
  have hstable : (prefixWord ++ tailWord_3938422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938422).length < 2 ^ (prefixWord ++ tailWord_3938422).sum := by decide
  have hdescent : baseEnd_3938422 < baseStart_3938422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938425 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_3938425 : Nat := 118140960795 + 3938425 * 2 ^ 59
def prefixEnd_3938425 : Nat := 4983230072969 + 3 ^ 40 * 3938425 * 2
def baseEnd_3938425 : Nat := 2022305046683858627775019

theorem tailTrace_3938425 : CollatzResearch.WordTrace tailWord_3938425 prefixEnd_3938425 2022305046683858627775019 := by
  unfold tailWord_3938425
  simp only [CollatzResearch.WordTrace]
  refine ⟨143646160756766329284344729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95764107171177552856229819 143646160756766329284344729)
  ·
    refine ⟨107734620567574746963258547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143646160756766329284344729 107734620567574746963258547)
    ·
      refine ⟨161601930851362120444887821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107734620567574746963258547 161601930851362120444887821)
      ·
        refine ⟨60600724069260795166832933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161601930851362120444887821 60600724069260795166832933)
        ·
          refine ⟨11362635762986399093781175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60600724069260795166832933 11362635762986399093781175)
          ·
            refine ⟨17043953644479598640671763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362635762986399093781175 17043953644479598640671763)
            ·
              refine ⟨25565930466719397961007645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043953644479598640671763 25565930466719397961007645)
              ·
                refine ⟨9587223925019774235377867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25565930466719397961007645 9587223925019774235377867)
                ·
                  refine ⟨14380835887529661353066801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9587223925019774235377867 14380835887529661353066801)
                  ·
                    refine ⟨10785626915647246014800101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14380835887529661353066801 10785626915647246014800101)
                    ·
                      refine ⟨2022305046683858627775019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10785626915647246014800101 2022305046683858627775019)
                      ·
                        rfl

theorem cell23_3938425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_3938425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938425 prefixEnd_3938425 := by exact prefixLift 3938425
  have htrace : WordTrace (prefixWord ++ tailWord_3938425) baseStart_3938425 baseEnd_3938425 := by
    simpa [prefixWord, tailWord_3938425, baseEnd_3938425] using wordTrace_append hprefix tailTrace_3938425
  have hstable : (prefixWord ++ tailWord_3938425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938425).length < 2 ^ (prefixWord ++ tailWord_3938425).sum := by decide
  have hdescent : baseEnd_3938425 < baseStart_3938425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938429 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_3938429 : Nat := 118140960795 + 3938429 * 2 ^ 59
def prefixEnd_3938429 : Nat := 4983230072969 + 3 ^ 40 * 3938429 * 2
def baseEnd_3938429 : Nat := 2022307100606476612125001

theorem tailTrace_3938429 : CollatzResearch.WordTrace tailWord_3938429 prefixEnd_3938429 2022307100606476612125001 := by
  unfold tailWord_3938429
  simp only [CollatzResearch.WordTrace]
  refine ⟨143646306648751837967490341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95764204432501225311660227 143646306648751837967490341)
  ·
    refine ⟨26933682496640969618904439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143646306648751837967490341 26933682496640969618904439)
    ·
      refine ⟨40400523744961454428356659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26933682496640969618904439 40400523744961454428356659)
      ·
        refine ⟨60600785617442181642534989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40400523744961454428356659 60600785617442181642534989)
        ·
          refine ⟨22725294606540818115950621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60600785617442181642534989 22725294606540818115950621)
          ·
            refine ⟨8521985477452806793481483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22725294606540818115950621 8521985477452806793481483)
            ·
              refine ⟨12782978216179210190222225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8521985477452806793481483 12782978216179210190222225)
              ·
                refine ⟨9587233662134407642666669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12782978216179210190222225 9587233662134407642666669)
                ·
                  refine ⟨3595212623300402866000001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9587233662134407642666669 3595212623300402866000001)
                  ·
                    refine ⟨2696409467475302149500001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3595212623300402866000001 2696409467475302149500001)
                    ·
                      refine ⟨2022307100606476612125001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696409467475302149500001 2022307100606476612125001)
                      ·
                        rfl

theorem cell23_3938429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_3938429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938429 prefixEnd_3938429 := by exact prefixLift 3938429
  have htrace : WordTrace (prefixWord ++ tailWord_3938429) baseStart_3938429 baseEnd_3938429 := by
    simpa [prefixWord, tailWord_3938429, baseEnd_3938429] using wordTrace_append hprefix tailTrace_3938429
  have hstable : (prefixWord ++ tailWord_3938429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938429).length < 2 ^ (prefixWord ++ tailWord_3938429).sum := by decide
  have hdescent : baseEnd_3938429 < baseStart_3938429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938435 : List Nat := [1, 1, 1, 3, 3, 4, 3, 7]
def baseStart_3938435 : Nat := 118140960795 + 3938435 * 2 ^ 59
def prefixEnd_3938435 : Nat := 4983230072969 + 3 ^ 40 * 3938435 * 2
def baseEnd_3938435 : Nat := 74900377092237169949999

theorem tailTrace_3938435 : CollatzResearch.WordTrace tailWord_3938435 prefixEnd_3938435 74900377092237169949999 := by
  unfold tailWord_3938435
  simp only [CollatzResearch.WordTrace]
  refine ⟨143646525486730100992208759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95764350324486733994805839 143646525486730100992208759)
  ·
    refine ⟨215469788230095151488313139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143646525486730100992208759 215469788230095151488313139)
    ·
      refine ⟨323204682345142727232469709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215469788230095151488313139 323204682345142727232469709)
      ·
        refine ⟨121201755879428522712176141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323204682345142727232469709 121201755879428522712176141)
        ·
          refine ⟨45450658454785696017066053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121201755879428522712176141 45450658454785696017066053)
          ·
            refine ⟨8521998460272318003199885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45450658454785696017066053 8521998460272318003199885)
            ·
              refine ⟨3195749422602119251199957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8521998460272318003199885 3195749422602119251199957)
              ·
                refine ⟨74900377092237169949999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3195749422602119251199957 74900377092237169949999)
                ·
                  rfl

theorem cell23_3938435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 7].length) (baseStart_3938435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938435 prefixEnd_3938435 := by exact prefixLift 3938435
  have htrace : WordTrace (prefixWord ++ tailWord_3938435) baseStart_3938435 baseEnd_3938435 := by
    simpa [prefixWord, tailWord_3938435, baseEnd_3938435] using wordTrace_append hprefix tailTrace_3938435
  have hstable : (prefixWord ++ tailWord_3938435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938435).length < 2 ^ (prefixWord ++ tailWord_3938435).sum := by decide
  have hdescent : baseEnd_3938435 < baseStart_3938435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938446 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3938446 : Nat := 118140960795 + 3938446 * 2 ^ 59
def prefixEnd_3938446 : Nat := 4983230072969 + 3 ^ 40 * 3938446 * 2
def baseEnd_3938446 : Nat := 2022315829777603045612423

theorem tailTrace_3938446 : CollatzResearch.WordTrace tailWord_3938446 prefixEnd_3938446 2022315829777603045612423 := by
  unfold tailWord_3938446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955865836211281233857399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95764617793126833247239461 17955865836211281233857399)
  ·
    refine ⟨26933798754316921850786099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955865836211281233857399 26933798754316921850786099)
    ·
      refine ⟨40400698131475382776179149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26933798754316921850786099 40400698131475382776179149)
      ·
        refine ⟨15150261799303268541067181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40400698131475382776179149 15150261799303268541067181)
        ·
          refine ⟨5681348174738725702900193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15150261799303268541067181 5681348174738725702900193)
          ·
            refine ⟨4261011131054044277175145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5681348174738725702900193 4261011131054044277175145)
            ·
              refine ⟨3195758348290533207881359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261011131054044277175145 3195758348290533207881359)
              ·
                refine ⟨4793637522435799811822039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195758348290533207881359 4793637522435799811822039)
                ·
                  refine ⟨7190456283653699717733059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793637522435799811822039 7190456283653699717733059)
                  ·
                    refine ⟨10785684425480549576599589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7190456283653699717733059 10785684425480549576599589)
                    ·
                      refine ⟨2022315829777603045612423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10785684425480549576599589 2022315829777603045612423)
                      ·
                        rfl

theorem cell23_3938446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3938446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938446 prefixEnd_3938446 := by exact prefixLift 3938446
  have htrace : WordTrace (prefixWord ++ tailWord_3938446) baseStart_3938446 baseEnd_3938446 := by
    simpa [prefixWord, tailWord_3938446, baseEnd_3938446] using wordTrace_append hprefix tailTrace_3938446
  have hstable : (prefixWord ++ tailWord_3938446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938446).length < 2 ^ (prefixWord ++ tailWord_3938446).sum := by decide
  have hdescent : baseEnd_3938446 < baseStart_3938446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938452 : List Nat := [2, 4, 2, 3, 1, 1, 10]
def baseStart_3938452 : Nat := 118140960795 + 3938452 * 2 ^ 59
def prefixEnd_3938452 : Nat := 4983230072969 + 3 ^ 40 * 3938452 * 2
def baseEnd_3938452 : Nat := 24966900131623827433795

theorem tailTrace_3938452 : CollatzResearch.WordTrace tailWord_3938452 prefixEnd_3938452 24966900131623827433795 := by
  unfold tailWord_3938452
  simp only [CollatzResearch.WordTrace]
  refine ⟨71823572763834256447788805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95764763685112341930385073 71823572763834256447788805)
  ·
    refine ⟨13466919893218923083960401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71823572763834256447788805 13466919893218923083960401)
    ·
      refine ⟨10100189919914192312970301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13466919893218923083960401 10100189919914192312970301)
      ·
        refine ⟨3787571219967822117363863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10100189919914192312970301 3787571219967822117363863)
        ·
          refine ⟨5681356829951733176045795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787571219967822117363863 5681356829951733176045795)
          ·
            refine ⟨8522035244927599764068693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681356829951733176045795 8522035244927599764068693)
            ·
              refine ⟨24966900131623827433795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8522035244927599764068693 24966900131623827433795)
              ·
                rfl

theorem cell23_3938452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 10].length) (baseStart_3938452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938452 prefixEnd_3938452 := by exact prefixLift 3938452
  have htrace : WordTrace (prefixWord ++ tailWord_3938452) baseStart_3938452 baseEnd_3938452 := by
    simpa [prefixWord, tailWord_3938452, baseEnd_3938452] using wordTrace_append hprefix tailTrace_3938452
  have hstable : (prefixWord ++ tailWord_3938452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938452).length < 2 ^ (prefixWord ++ tailWord_3938452).sum := by decide
  have hdescent : baseEnd_3938452 < baseStart_3938452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938456 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 2, 4]
def baseStart_3938456 : Nat := 118140960795 + 3938456 * 2 ^ 59
def prefixEnd_3938456 : Nat := 4983230072969 + 3 ^ 40 * 3938456 * 2
def baseEnd_3938456 : Nat := 674106988194716002162459

theorem tailTrace_3938456 : CollatzResearch.WordTrace tailWord_3938456 prefixEnd_3938456 674106988194716002162459 := by
  unfold tailWord_3938456
  simp only [CollatzResearch.WordTrace]
  refine ⟨71823645709827010789361611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95764860946436014385815481 71823645709827010789361611)
  ·
    refine ⟨107735468564740516184042417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71823645709827010789361611 107735468564740516184042417)
    ·
      refine ⟨80801601423555387138031813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107735468564740516184042417 80801601423555387138031813)
      ·
        refine ⟨15150300266916635088380965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80801601423555387138031813 15150300266916635088380965)
        ·
          refine ⟨2840681300046869079071431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15150300266916635088380965 2840681300046869079071431)
          ·
            refine ⟨4261021950070303618607147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840681300046869079071431 4261021950070303618607147)
            ·
              refine ⟨6391532925105455427910721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261021950070303618607147 6391532925105455427910721)
              ·
                refine ⟨4793649693829091570933041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391532925105455427910721 4793649693829091570933041)
                ·
                  refine ⟨3595237270371818678199781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4793649693829091570933041 3595237270371818678199781)
                  ·
                    refine ⟨674106988194716002162459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3595237270371818678199781 674106988194716002162459)
                    ·
                      rfl

theorem cell23_3938456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_3938456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938456 prefixEnd_3938456 := by exact prefixLift 3938456
  have htrace : WordTrace (prefixWord ++ tailWord_3938456) baseStart_3938456 baseEnd_3938456 := by
    simpa [prefixWord, tailWord_3938456, baseEnd_3938456] using wordTrace_append hprefix tailTrace_3938456
  have hstable : (prefixWord ++ tailWord_3938456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938456).length < 2 ^ (prefixWord ++ tailWord_3938456).sum := by decide
  have hdescent : baseEnd_3938456 < baseStart_3938456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938489 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 1, 3, 2]
def baseStart_3938489 : Nat := 118140960795 + 3938489 * 2 ^ 59
def prefixEnd_3938489 : Nat := 4983230072969 + 3 ^ 40 * 3938489 * 2
def baseEnd_3938489 : Nat := 2022337909445746377374725

theorem tailTrace_3938489 : CollatzResearch.WordTrace tailWord_3938489 prefixEnd_3938489 2022337909445746377374725 := by
  unfold tailWord_3938489
  simp only [CollatzResearch.WordTrace]
  refine ⟨143648495028534468214674521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95765663352356312143116347 143648495028534468214674521)
  ·
    refine ⟨107736371271400851161005891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143648495028534468214674521 107736371271400851161005891)
    ·
      refine ⟨161604556907101276741508837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107736371271400851161005891 161604556907101276741508837)
      ·
        refine ⟨30300854420081489389032907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161604556907101276741508837 30300854420081489389032907)
        ·
          refine ⟨45451281630122234083549361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30300854420081489389032907 45451281630122234083549361)
          ·
            refine ⟨34088461222591675562662021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45451281630122234083549361 34088461222591675562662021)
            ·
              refine ⟨6391586479235939167999129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34088461222591675562662021 6391586479235939167999129)
              ·
                refine ⟨4793689859426954375999347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391586479235939167999129 4793689859426954375999347)
                ·
                  refine ⟨7190534789140431563999021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793689859426954375999347 7190534789140431563999021)
                  ·
                    refine ⟨2696450545927661836499633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7190534789140431563999021 2696450545927661836499633)
                    ·
                      refine ⟨2022337909445746377374725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696450545927661836499633 2022337909445746377374725)
                      ·
                        rfl

theorem cell23_3938489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_3938489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938489 prefixEnd_3938489 := by exact prefixLift 3938489
  have htrace : WordTrace (prefixWord ++ tailWord_3938489) baseStart_3938489 baseEnd_3938489 := by
    simpa [prefixWord, tailWord_3938489, baseEnd_3938489] using wordTrace_append hprefix tailTrace_3938489
  have hstable : (prefixWord ++ tailWord_3938489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938489).length < 2 ^ (prefixWord ++ tailWord_3938489).sum := by decide
  have hdescent : baseEnd_3938489 < baseStart_3938489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938497 : List Nat := [1, 2, 6, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3938497 : Nat := 118140960795 + 3938497 * 2 ^ 59
def prefixEnd_3938497 : Nat := 4983230072969 + 3 ^ 40 * 3938497 * 2
def baseEnd_3938497 : Nat := 2022342017290982346074689

theorem tailTrace_3938497 : CollatzResearch.WordTrace tailWord_3938497 prefixEnd_3938497 2022342017290982346074689 := by
  unfold tailWord_3938497
  simp only [CollatzResearch.WordTrace]
  refine ⟨143648786812505485580965745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95765857875003657053977163 143648786812505485580965745)
  ·
    refine ⟨107736590109379114185724309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143648786812505485580965745 107736590109379114185724309)
    ·
      refine ⟨5050152661377145977455827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107736590109379114185724309 5050152661377145977455827)
      ·
        refine ⟨7575228992065718966183741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050152661377145977455827 7575228992065718966183741)
        ·
          refine ⟨2840710872024644612318903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7575228992065718966183741 2840710872024644612318903)
          ·
            refine ⟨4261066308036966918478355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840710872024644612318903 4261066308036966918478355)
            ·
              refine ⟨6391599462055450377717533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261066308036966918478355 6391599462055450377717533)
              ·
                refine ⟨2396849798270793891644075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6391599462055450377717533 2396849798270793891644075)
                ·
                  refine ⟨3595274697406190837466113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396849798270793891644075 3595274697406190837466113)
                  ·
                    refine ⟨2696456023054643128099585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3595274697406190837466113 2696456023054643128099585)
                    ·
                      refine ⟨2022342017290982346074689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696456023054643128099585 2022342017290982346074689)
                      ·
                        rfl

theorem cell23_3938497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3938497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938497 prefixEnd_3938497 := by exact prefixLift 3938497
  have htrace : WordTrace (prefixWord ++ tailWord_3938497) baseStart_3938497 baseEnd_3938497 := by
    simpa [prefixWord, tailWord_3938497, baseEnd_3938497] using wordTrace_append hprefix tailTrace_3938497
  have hstable : (prefixWord ++ tailWord_3938497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938497).length < 2 ^ (prefixWord ++ tailWord_3938497).sum := by decide
  have hdescent : baseEnd_3938497 < baseStart_3938497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938519 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 2, 2, 2]
def baseStart_3938519 : Nat := 118140960795 + 3938519 * 2 ^ 59
def prefixEnd_3938519 : Nat := 4983230072969 + 3 ^ 40 * 3938519 * 2
def baseEnd_3938519 : Nat := 2022353313865381259999587

theorem tailTrace_3938519 : CollatzResearch.WordTrace tailWord_3938519 prefixEnd_3938519 2022353313865381259999587 := by
  unfold tailWord_3938519
  simp only [CollatzResearch.WordTrace]
  refine ⟨143649589218425783338266611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95766392812283855558844407 143649589218425783338266611)
  ·
    refine ⟨215474383827638675007399917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143649589218425783338266611 215474383827638675007399917)
    ·
      refine ⟨80802893935364503127774969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215474383827638675007399917 80802893935364503127774969)
      ·
        refine ⟨60602170451523377345831227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80802893935364503127774969 60602170451523377345831227)
        ·
          refine ⟨90903255677285066018746841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60602170451523377345831227 90903255677285066018746841)
          ·
            refine ⟨68177441757963799514060131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90903255677285066018746841 68177441757963799514060131)
            ·
              refine ⟨102266162636945699271090197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68177441757963799514060131 102266162636945699271090197)
              ·
                refine ⟨4793726373606829653332353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102266162636945699271090197 4793726373606829653332353)
                ·
                  refine ⟨3595294780205122239999265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4793726373606829653332353 3595294780205122239999265)
                  ·
                    refine ⟨2696471085153841679999449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3595294780205122239999265 2696471085153841679999449)
                    ·
                      refine ⟨2022353313865381259999587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696471085153841679999449 2022353313865381259999587)
                      ·
                        rfl

theorem cell23_3938519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_3938519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938519 prefixEnd_3938519 := by exact prefixLift 3938519
  have htrace : WordTrace (prefixWord ++ tailWord_3938519) baseStart_3938519 baseEnd_3938519 := by
    simpa [prefixWord, tailWord_3938519, baseEnd_3938519] using wordTrace_append hprefix tailTrace_3938519
  have hstable : (prefixWord ++ tailWord_3938519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938519).length < 2 ^ (prefixWord ++ tailWord_3938519).sum := by decide
  have hdescent : baseEnd_3938519 < baseStart_3938519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938530 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3938530 : Nat := 118140960795 + 3938530 * 2 ^ 59
def prefixEnd_3938530 : Nat := 4983230072969 + 3 ^ 40 * 3938530 * 2
def baseEnd_3938530 : Nat := 2022358962152580716962037

theorem tailTrace_3938530 : CollatzResearch.WordTrace tailWord_3938530 prefixEnd_3938530 2022358962152580716962037 := by
  unfold tailWord_3938530
  simp only [CollatzResearch.WordTrace]
  refine ⟨35912497605346483054229261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95766660280923954811278029 35912497605346483054229261)
  ·
    refine ⟨13467186602004931145335973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35912497605346483054229261 13467186602004931145335973)
    ·
      refine ⟨2525097487875924589750495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13467186602004931145335973 2525097487875924589750495)
      ·
        refine ⟨3787646231813886884625743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525097487875924589750495 3787646231813886884625743)
        ·
          refine ⟨5681469347720830326938615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787646231813886884625743 5681469347720830326938615)
          ·
            refine ⟨8522204021581245490407923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681469347720830326938615 8522204021581245490407923)
            ·
              refine ⟨12783306032371868235611885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522204021581245490407923 12783306032371868235611885)
              ·
                refine ⟨4793739762139450588354457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12783306032371868235611885 4793739762139450588354457)
                ·
                  refine ⟨3595304821604587941265843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4793739762139450588354457 3595304821604587941265843)
                  ·
                    refine ⟨5392957232406881911898765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3595304821604587941265843 5392957232406881911898765)
                    ·
                      refine ⟨2022358962152580716962037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5392957232406881911898765 2022358962152580716962037)
                      ·
                        rfl

theorem cell23_3938530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3938530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938530 prefixEnd_3938530 := by exact prefixLift 3938530
  have htrace : WordTrace (prefixWord ++ tailWord_3938530) baseStart_3938530 baseEnd_3938530 := by
    simpa [prefixWord, tailWord_3938530, baseEnd_3938530] using wordTrace_append hprefix tailTrace_3938530
  have hstable : (prefixWord ++ tailWord_3938530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938530).length < 2 ^ (prefixWord ++ tailWord_3938530).sum := by decide
  have hdescent : baseEnd_3938530 < baseStart_3938530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938536 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_3938536 : Nat := 118140960795 + 3938536 * 2 ^ 59
def prefixEnd_3938536 : Nat := 4983230072969 + 3 ^ 40 * 3938536 * 2
def baseEnd_3938536 : Nat := 2022362043036507693487009

theorem tailTrace_3938536 : CollatzResearch.WordTrace tailWord_3938536 prefixEnd_3938536 2022362043036507693487009 := by
  unfold tailWord_3938536
  simp only [CollatzResearch.WordTrace]
  refine ⟨71825104629682097620817731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95766806172909463494423641 71825104629682097620817731)
  ·
    refine ⟨107737656944523146431226597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71825104629682097620817731 107737656944523146431226597)
    ·
      refine ⟨20200810677098089955854987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107737656944523146431226597 20200810677098089955854987)
      ·
        refine ⟨30301216015647134933782481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20200810677098089955854987 30301216015647134933782481)
        ·
          refine ⟨22725912011735351200336861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30301216015647134933782481 22725912011735351200336861)
          ·
            refine ⟨8522217004400756700126323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22725912011735351200336861 8522217004400756700126323)
            ·
              refine ⟨12783325506601135050189485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522217004400756700126323 12783325506601135050189485)
              ·
                refine ⟨4793747064975425643821057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12783325506601135050189485 4793747064975425643821057)
                ·
                  refine ⟨3595310298731569232865793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4793747064975425643821057 3595310298731569232865793)
                  ·
                    refine ⟨2696482724048676924649345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3595310298731569232865793 2696482724048676924649345)
                    ·
                      refine ⟨2022362043036507693487009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696482724048676924649345 2022362043036507693487009)
                      ·
                        rfl

theorem cell23_3938536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_3938536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938536 prefixEnd_3938536 := by exact prefixLift 3938536
  have htrace : WordTrace (prefixWord ++ tailWord_3938536) baseStart_3938536 baseEnd_3938536 := by
    simpa [prefixWord, tailWord_3938536, baseEnd_3938536] using wordTrace_append hprefix tailTrace_3938536
  have hstable : (prefixWord ++ tailWord_3938536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938536).length < 2 ^ (prefixWord ++ tailWord_3938536).sum := by decide
  have hdescent : baseEnd_3938536 < baseStart_3938536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938622 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3938622 : Nat := 118140960795 + 3938622 * 2 ^ 59
def prefixEnd_3938622 : Nat := 4983230072969 + 3 ^ 40 * 3938622 * 2
def baseEnd_3938622 : Nat := 2022406202372794357011613

theorem tailTrace_3938622 : CollatzResearch.WordTrace tailWord_3938622 prefixEnd_3938622 2022406202372794357011613 := by
  unfold tailWord_3938622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17956668242131578991158265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95768897291368421286177413 17956668242131578991158265)
  ·
    refine ⟨13467501181598684243368699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17956668242131578991158265 13467501181598684243368699)
    ·
      refine ⟨20201251772398026365053049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13467501181598684243368699 20201251772398026365053049)
      ·
        refine ⟨15150938829298519773789787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20201251772398026365053049 15150938829298519773789787)
        ·
          refine ⟨22726408243947779660684681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15150938829298519773789787 22726408243947779660684681)
          ·
            refine ⟨17044806182960834745513511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22726408243947779660684681 17044806182960834745513511)
            ·
              refine ⟨25567209274441252118270267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17044806182960834745513511 25567209274441252118270267)
              ·
                refine ⟨38350813911661878177405401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25567209274441252118270267 38350813911661878177405401)
                ·
                  refine ⟨28763110433746408633054051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38350813911661878177405401 28763110433746408633054051)
                  ·
                    refine ⟨43144665650619612949581077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28763110433746408633054051 43144665650619612949581077)
                    ·
                      refine ⟨2022406202372794357011613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43144665650619612949581077 2022406202372794357011613)
                      ·
                        rfl

theorem cell23_3938622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3938622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938622 prefixEnd_3938622 := by exact prefixLift 3938622
  have htrace : WordTrace (prefixWord ++ tailWord_3938622) baseStart_3938622 baseEnd_3938622 := by
    simpa [prefixWord, tailWord_3938622, baseEnd_3938622] using wordTrace_append hprefix tailTrace_3938622
  have hstable : (prefixWord ++ tailWord_3938622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938622).length < 2 ^ (prefixWord ++ tailWord_3938622).sum := by decide
  have hdescent : baseEnd_3938622 < baseStart_3938622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938632 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 6]
def baseStart_3938632 : Nat := 118140960795 + 3938632 * 2 ^ 59
def prefixEnd_3938632 : Nat := 4983230072969 + 3 ^ 40 * 3938632 * 2
def baseEnd_3938632 : Nat := 224712370797704368654063

theorem tailTrace_3938632 : CollatzResearch.WordTrace tailWord_3938632 prefixEnd_3938632 224712370797704368654063 := by
  unfold tailWord_3938632
  simp only [CollatzResearch.WordTrace]
  refine ⟨71826855333508201818565075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95769140444677602424753433 71826855333508201818565075)
  ·
    refine ⟨107740283000262302727847613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71826855333508201818565075 107740283000262302727847613)
    ·
      refine ⟨40402606125098363522942855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107740283000262302727847613 40402606125098363522942855)
      ·
        refine ⟨60603909187647545284414283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40402606125098363522942855 60603909187647545284414283)
        ·
          refine ⟨90905863781471317926621425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60603909187647545284414283 90905863781471317926621425)
          ·
            refine ⟨68179397836103488444966069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90905863781471317926621425 68179397836103488444966069)
            ·
              refine ⟨6391818547134702041715569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68179397836103488444966069 6391818547134702041715569)
              ·
                refine ⟨4793863910351026531286677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391818547134702041715569 4793863910351026531286677)
                ·
                  refine ⟨224712370797704368654063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4793863910351026531286677 224712370797704368654063)
                  ·
                    rfl

theorem cell23_3938632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 6].length) (baseStart_3938632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938632 prefixEnd_3938632 := by exact prefixLift 3938632
  have htrace : WordTrace (prefixWord ++ tailWord_3938632) baseStart_3938632 baseEnd_3938632 := by
    simpa [prefixWord, tailWord_3938632, baseEnd_3938632] using wordTrace_append hprefix tailTrace_3938632
  have hstable : (prefixWord ++ tailWord_3938632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938632).length < 2 ^ (prefixWord ++ tailWord_3938632).sum := by decide
  have hdescent : baseEnd_3938632 < baseStart_3938632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938655 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_3938655 : Nat := 118140960795 + 3938655 * 2 ^ 59
def prefixEnd_3938655 : Nat := 4983230072969 + 3 ^ 40 * 3938655 * 2
def baseEnd_3938655 : Nat := 2022423147234392727898961

theorem tailTrace_3938655 : CollatzResearch.WordTrace tailWord_3938655 prefixEnd_3938655 2022423147234392727898961 := by
  unfold tailWord_3938655
  simp only [CollatzResearch.WordTrace]
  refine ⟨143654549545933078565217419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95769699697288719043478279 143654549545933078565217419)
  ·
    refine ⟨215481824318899617847826129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143654549545933078565217419 215481824318899617847826129)
    ·
      refine ⟨161611368239174713385869597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215481824318899617847826129 161611368239174713385869597)
      ·
        refine ⟨60604263089690517519701099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161611368239174713385869597 60604263089690517519701099)
        ·
          refine ⟨90906394634535776279551649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60604263089690517519701099 90906394634535776279551649)
          ·
            refine ⟨68179795975901832209663737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90906394634535776279551649 68179795975901832209663737)
            ·
              refine ⟨51134846981926374157247803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68179795975901832209663737 51134846981926374157247803)
              ·
                refine ⟨76702270472889561235871705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51134846981926374157247803 76702270472889561235871705)
                ·
                  refine ⟨57526702854667170926903779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76702270472889561235871705 57526702854667170926903779)
                  ·
                    refine ⟨86290054282000756390355669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57526702854667170926903779 86290054282000756390355669)
                    ·
                      refine ⟨2022423147234392727898961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86290054282000756390355669 2022423147234392727898961)
                      ·
                        rfl

theorem cell23_3938655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_3938655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938655 prefixEnd_3938655 := by exact prefixLift 3938655
  have htrace : WordTrace (prefixWord ++ tailWord_3938655) baseStart_3938655 baseEnd_3938655 := by
    simpa [prefixWord, tailWord_3938655, baseEnd_3938655] using wordTrace_append hprefix tailTrace_3938655
  have hstable : (prefixWord ++ tailWord_3938655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938655).length < 2 ^ (prefixWord ++ tailWord_3938655).sum := by decide
  have hdescent : baseEnd_3938655 < baseStart_3938655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938659 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3938659 : Nat := 118140960795 + 3938659 * 2 ^ 59
def prefixEnd_3938659 : Nat := 4983230072969 + 3 ^ 40 * 3938659 * 2
def baseEnd_3938659 : Nat := 2022425201157010712248943

theorem tailTrace_3938659 : CollatzResearch.WordTrace tailWord_3938659 prefixEnd_3938659 2022425201157010712248943 := by
  unfold tailWord_3938659
  simp only [CollatzResearch.WordTrace]
  refine ⟨143654695437918587248363031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95769796958612391498908687 143654695437918587248363031)
  ·
    refine ⟨215482043156877880872544547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143654695437918587248363031 215482043156877880872544547)
    ·
      refine ⟨323223064735316821308816821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215482043156877880872544547 323223064735316821308816821)
      ·
        refine ⟨30302162318935951997701577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323223064735316821308816821 30302162318935951997701577)
        ·
          refine ⟨22726621739201963998276183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30302162318935951997701577 22726621739201963998276183)
          ·
            refine ⟨34089932608802945997414275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22726621739201963998276183 34089932608802945997414275)
            ·
              refine ⟨51134898913204418996121413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34089932608802945997414275 51134898913204418996121413)
              ·
                refine ⟨9587793546225828561772765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51134898913204418996121413 9587793546225828561772765)
                ·
                  refine ⟨3595422579834685710664787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9587793546225828561772765 3595422579834685710664787)
                  ·
                    refine ⟨5393133869752028565997181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3595422579834685710664787 5393133869752028565997181)
                    ·
                      refine ⟨2022425201157010712248943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393133869752028565997181 2022425201157010712248943)
                      ·
                        rfl

theorem cell23_3938659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3938659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938659 prefixEnd_3938659 := by exact prefixLift 3938659
  have htrace : WordTrace (prefixWord ++ tailWord_3938659) baseStart_3938659 baseEnd_3938659 := by
    simpa [prefixWord, tailWord_3938659, baseEnd_3938659] using wordTrace_append hprefix tailTrace_3938659
  have hstable : (prefixWord ++ tailWord_3938659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938659).length < 2 ^ (prefixWord ++ tailWord_3938659).sum := by decide
  have hdescent : baseEnd_3938659 < baseStart_3938659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938669 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_3938669 : Nat := 118140960795 + 3938669 * 2 ^ 59
def prefixEnd_3938669 : Nat := 4983230072969 + 3 ^ 40 * 3938669 * 2
def baseEnd_3938669 : Nat := 2022430335963555673123897

theorem tailTrace_3938669 : CollatzResearch.WordTrace tailWord_3938669 prefixEnd_3938669 2022430335963555673123897 := by
  unfold tailWord_3938669
  simp only [CollatzResearch.WordTrace]
  refine ⟨143655060167882358956227061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95770040111921572637484707 143655060167882358956227061)
  ·
    refine ⟨13467661890738971152146287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143655060167882358956227061 13467661890738971152146287)
    ·
      refine ⟨20201492836108456728219431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13467661890738971152146287 20201492836108456728219431)
      ·
        refine ⟨30302239254162685092329147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20201492836108456728219431 30302239254162685092329147)
        ·
          refine ⟨45453358881244027638493721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30302239254162685092329147 45453358881244027638493721)
          ·
            refine ⟨34090019160933020728870291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45453358881244027638493721 34090019160933020728870291)
            ·
              refine ⟨51135028741399531093305437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34090019160933020728870291 51135028741399531093305437)
              ·
                refine ⟨19175635778024824159989539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51135028741399531093305437 19175635778024824159989539)
                ·
                  refine ⟨28763453667037236239984309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19175635778024824159989539 28763453667037236239984309)
                  ·
                    refine ⟨2696573781284740897498529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28763453667037236239984309 2696573781284740897498529)
                    ·
                      refine ⟨2022430335963555673123897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696573781284740897498529 2022430335963555673123897)
                      ·
                        rfl

theorem cell23_3938669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_3938669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938669 prefixEnd_3938669 := by exact prefixLift 3938669
  have htrace : WordTrace (prefixWord ++ tailWord_3938669) baseStart_3938669 baseEnd_3938669 := by
    simpa [prefixWord, tailWord_3938669, baseEnd_3938669] using wordTrace_append hprefix tailTrace_3938669
  have hstable : (prefixWord ++ tailWord_3938669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938669).length < 2 ^ (prefixWord ++ tailWord_3938669).sum := by decide
  have hdescent : baseEnd_3938669 < baseStart_3938669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938715 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9]
def baseStart_3938715 : Nat := 118140960795 + 3938715 * 2 ^ 59
def prefixEnd_3938715 : Nat := 4983230072969 + 3 ^ 40 * 3938715 * 2
def baseEnd_3938715 : Nat := 2022453956073662493148685

theorem tailTrace_3938715 : CollatzResearch.WordTrace tailWord_3938715 prefixEnd_3938715 2022453956073662493148685 := by
  unfold tailWord_3938715
  simp only [CollatzResearch.WordTrace]
  refine ⟨143656737925715708812401599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95771158617143805874934399 143656737925715708812401599)
  ·
    refine ⟨215485106888573563218602399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143656737925715708812401599 215485106888573563218602399)
    ·
      refine ⟨323227660332860344827903599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215485106888573563218602399 323227660332860344827903599)
      ·
        refine ⟨484841490499290517241855399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323227660332860344827903599 484841490499290517241855399)
        ·
          refine ⟨727262235748935775862783099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484841490499290517241855399 727262235748935775862783099)
          ·
            refine ⟨1090893353623403663794174649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727262235748935775862783099 1090893353623403663794174649)
            ·
              refine ⟨818170015217552747845630987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090893353623403663794174649 818170015217552747845630987)
              ·
                refine ⟨1227255022826329121768446481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818170015217552747845630987 1227255022826329121768446481)
                ·
                  refine ⟨920441267119746841326334861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1227255022826329121768446481 920441267119746841326334861)
                  ·
                    refine ⟨345165475169905065497375573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920441267119746841326334861 345165475169905065497375573)
                    ·
                      refine ⟨2022453956073662493148685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 345165475169905065497375573 2022453956073662493148685)
                      ·
                        rfl

theorem cell23_3938715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_3938715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938715 prefixEnd_3938715 := by exact prefixLift 3938715
  have htrace : WordTrace (prefixWord ++ tailWord_3938715) baseStart_3938715 baseEnd_3938715 := by
    simpa [prefixWord, tailWord_3938715, baseEnd_3938715] using wordTrace_append hprefix tailTrace_3938715
  have hstable : (prefixWord ++ tailWord_3938715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938715).length < 2 ^ (prefixWord ++ tailWord_3938715).sum := by decide
  have hdescent : baseEnd_3938715 < baseStart_3938715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938719 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 3]
def baseStart_3938719 : Nat := 118140960795 + 3938719 * 2 ^ 59
def prefixEnd_3938719 : Nat := 4983230072969 + 3 ^ 40 * 3938719 * 2
def baseEnd_3938719 : Nat := 2022456009996280477498667

theorem tailTrace_3938719 : CollatzResearch.WordTrace tailWord_3938719 prefixEnd_3938719 2022456009996280477498667 := by
  unfold tailWord_3938719
  simp only [CollatzResearch.WordTrace]
  refine ⟨143656883817701217495547211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95771255878467478330364807 143656883817701217495547211)
  ·
    refine ⟨215485325726551826243320817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143656883817701217495547211 215485325726551826243320817)
    ·
      refine ⟨161613994294913869682490613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215485325726551826243320817 161613994294913869682490613)
      ·
        refine ⟨15151311965148175282733495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161613994294913869682490613 15151311965148175282733495)
        ·
          refine ⟨22726967947722262924100243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15151311965148175282733495 22726967947722262924100243)
          ·
            refine ⟨34090451921583394386150365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22726967947722262924100243 34090451921583394386150365)
            ·
              refine ⟨12783919470593772894806387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34090451921583394386150365 12783919470593772894806387)
              ·
                refine ⟨19175879205890659342209581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12783919470593772894806387 19175879205890659342209581)
                ·
                  refine ⟨7190954702208997253328593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19175879205890659342209581 7190954702208997253328593)
                  ·
                    refine ⟨5393216026656747939996445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7190954702208997253328593 5393216026656747939996445)
                    ·
                      refine ⟨2022456009996280477498667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393216026656747939996445 2022456009996280477498667)
                      ·
                        rfl

theorem cell23_3938719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_3938719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938719 prefixEnd_3938719 := by exact prefixLift 3938719
  have htrace : WordTrace (prefixWord ++ tailWord_3938719) baseStart_3938719 baseEnd_3938719 := by
    simpa [prefixWord, tailWord_3938719, baseEnd_3938719] using wordTrace_append hprefix tailTrace_3938719
  have hstable : (prefixWord ++ tailWord_3938719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938719).length < 2 ^ (prefixWord ++ tailWord_3938719).sum := by decide
  have hdescent : baseEnd_3938719 < baseStart_3938719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938722 : List Nat := [3, 3, 1, 2, 1, 1, 1, 11]
def baseStart_3938722 : Nat := 118140960795 + 3938722 * 2 ^ 59
def prefixEnd_3938722 : Nat := 4983230072969 + 3 ^ 40 * 3938722 * 2
def baseEnd_3938722 : Nat := 74905835201416443176339

theorem tailTrace_3938722 : CollatzResearch.WordTrace tailWord_3938722 prefixEnd_3938722 74905835201416443176339 := by
  unfold tailWord_3938722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35914248309172587251976605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95771328824460232671937613 35914248309172587251976605)
  ·
    refine ⟨13467843115939720219491227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35914248309172587251976605 13467843115939720219491227)
    ·
      refine ⟨20201764673909580329236841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13467843115939720219491227 20201764673909580329236841)
      ·
        refine ⟨15151323505432185246927631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20201764673909580329236841 15151323505432185246927631)
        ·
          refine ⟨22726985258148277870391447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15151323505432185246927631 22726985258148277870391447)
          ·
            refine ⟨34090477887222416805587171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22726985258148277870391447 34090477887222416805587171)
            ·
              refine ⟨51135716830833625208380757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34090477887222416805587171 51135716830833625208380757)
              ·
                refine ⟨74905835201416443176339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 51135716830833625208380757 74905835201416443176339)
                ·
                  rfl

theorem cell23_3938722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 11].length) (baseStart_3938722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938722 prefixEnd_3938722 := by exact prefixLift 3938722
  have htrace : WordTrace (prefixWord ++ tailWord_3938722) baseStart_3938722 baseEnd_3938722 := by
    simpa [prefixWord, tailWord_3938722, baseEnd_3938722] using wordTrace_append hprefix tailTrace_3938722
  have hstable : (prefixWord ++ tailWord_3938722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938722).length < 2 ^ (prefixWord ++ tailWord_3938722).sum := by decide
  have hdescent : baseEnd_3938722 < baseStart_3938722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938756 : List Nat := [2, 3, 3, 2, 2, 2, 1, 8]
def baseStart_3938756 : Nat := 118140960795 + 3938756 * 2 ^ 59
def prefixEnd_3938756 : Nat := 4983230072969 + 3 ^ 40 * 3938756 * 2
def baseEnd_3938756 : Nat := 74906481806685067879111

theorem tailTrace_3938756 : CollatzResearch.WordTrace tailWord_3938756 prefixEnd_3938756 74906481806685067879111 := by
  unfold tailWord_3938756
  simp only [CollatzResearch.WordTrace]
  refine ⟨71829116659283586407322061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95772155545711448543096081 71829116659283586407322061)
  ·
    refine ⟨26935918747231344902745773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71829116659283586407322061 26935918747231344902745773)
    ·
      refine ⟨10100969530211754338529665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26935918747231344902745773 10100969530211754338529665)
      ·
        refine ⟨7575727147658815753897249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10100969530211754338529665 7575727147658815753897249)
        ·
          refine ⟨5681795360744111815422937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7575727147658815753897249 5681795360744111815422937)
          ·
            refine ⟨4261346520558083861567203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5681795360744111815422937 4261346520558083861567203)
            ·
              refine ⟨6392019780837125792350805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261346520558083861567203 6392019780837125792350805)
              ·
                refine ⟨74906481806685067879111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6392019780837125792350805 74906481806685067879111)
                ·
                  rfl

theorem cell23_3938756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 8].length) (baseStart_3938756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938756 prefixEnd_3938756 := by exact prefixLift 3938756
  have htrace : WordTrace (prefixWord ++ tailWord_3938756) baseStart_3938756 baseEnd_3938756 := by
    simpa [prefixWord, tailWord_3938756, baseEnd_3938756] using wordTrace_append hprefix tailTrace_3938756
  have hstable : (prefixWord ++ tailWord_3938756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938756).length < 2 ^ (prefixWord ++ tailWord_3938756).sum := by decide
  have hdescent : baseEnd_3938756 < baseStart_3938756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938776 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 1, 3, 2]
def baseStart_3938776 : Nat := 118140960795 + 3938776 * 2 ^ 59
def prefixEnd_3938776 : Nat := 4983230072969 + 3 ^ 40 * 3938776 * 2
def baseEnd_3938776 : Nat := 2022485278393586754485905

theorem tailTrace_3938776 : CollatzResearch.WordTrace tailWord_3938776 prefixEnd_3938776 2022485278393586754485905 := by
  unfold tailWord_3938776
  simp only [CollatzResearch.WordTrace]
  refine ⟨71829481389247358115186091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95772641852329810820248121 71829481389247358115186091)
  ·
    refine ⟨107744222083871037172779137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71829481389247358115186091 107744222083871037172779137)
    ·
      refine ⟨80808166562903277879584353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107744222083871037172779137 80808166562903277879584353)
      ·
        refine ⟨60606124922177458409688265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80808166562903277879584353 60606124922177458409688265)
        ·
          refine ⟨45454593691633093807266199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60606124922177458409688265 45454593691633093807266199)
          ·
            refine ⟨68181890537449640710899299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45454593691633093807266199 68181890537449640710899299)
            ·
              refine ⟨102272835806174461066348949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68181890537449640710899299 102272835806174461066348949)
              ·
                refine ⟨4794039178414427862485107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102272835806174461066348949 4794039178414427862485107)
                ·
                  refine ⟨7191058767621641793727661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794039178414427862485107 7191058767621641793727661)
                  ·
                    refine ⟨2696647037858115672647873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7191058767621641793727661 2696647037858115672647873)
                    ·
                      refine ⟨2022485278393586754485905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696647037858115672647873 2022485278393586754485905)
                      ·
                        rfl

theorem cell23_3938776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_3938776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938776 prefixEnd_3938776 := by exact prefixLift 3938776
  have htrace : WordTrace (prefixWord ++ tailWord_3938776) baseStart_3938776 baseEnd_3938776 := by
    simpa [prefixWord, tailWord_3938776, baseEnd_3938776] using wordTrace_append hprefix tailTrace_3938776
  have hstable : (prefixWord ++ tailWord_3938776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938776).length < 2 ^ (prefixWord ++ tailWord_3938776).sum := by decide
  have hdescent : baseEnd_3938776 < baseStart_3938776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938869 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3938869 : Nat := 118140960795 + 3938869 * 2 ^ 59
def prefixEnd_3938869 : Nat := 4983230072969 + 3 ^ 40 * 3938869 * 2
def baseEnd_3938869 : Nat := 2022533032094454890622977

theorem tailTrace_3938869 : CollatzResearch.WordTrace tailWord_3938869 prefixEnd_3938869 2022533032094454890622977 := by
  unfold tailWord_3938869
  simp only [CollatzResearch.WordTrace]
  refine ⟨143662354767157793113507661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95774903178105195409005107 143662354767157793113507661)
  ·
    refine ⟨53873383037684172417565373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143662354767157793113507661 53873383037684172417565373)
    ·
      refine ⟨20202518639131564656587015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53873383037684172417565373 20202518639131564656587015)
      ·
        refine ⟨30303777958697346984880523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20202518639131564656587015 30303777958697346984880523)
        ·
          refine ⟨45455666938046020477320785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30303777958697346984880523 45455666938046020477320785)
          ·
            refine ⟨34091750203534515357990589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45455666938046020477320785 34091750203534515357990589)
            ·
              refine ⟨12784406326325443259246471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34091750203534515357990589 12784406326325443259246471)
              ·
                refine ⟨19176609489488164888869707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784406326325443259246471 19176609489488164888869707)
                ·
                  refine ⟨28764914234232247333304561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19176609489488164888869707 28764914234232247333304561)
                  ·
                    refine ⟨21573685675674185499978421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28764914234232247333304561 21573685675674185499978421)
                    ·
                      refine ⟨2022533032094454890622977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21573685675674185499978421 2022533032094454890622977)
                      ·
                        rfl

theorem cell23_3938869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3938869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938869 prefixEnd_3938869 := by exact prefixLift 3938869
  have htrace : WordTrace (prefixWord ++ tailWord_3938869) baseStart_3938869 baseEnd_3938869 := by
    simpa [prefixWord, tailWord_3938869, baseEnd_3938869] using wordTrace_append hprefix tailTrace_3938869
  have hstable : (prefixWord ++ tailWord_3938869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938869).length < 2 ^ (prefixWord ++ tailWord_3938869).sum := by decide
  have hdescent : baseEnd_3938869 < baseStart_3938869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938879 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_3938879 : Nat := 118140960795 + 3938879 * 2 ^ 59
def prefixEnd_3938879 : Nat := 4983230072969 + 3 ^ 40 * 3938879 * 2
def baseEnd_3938879 : Nat := 2022538166900999851497931

theorem tailTrace_3938879 : CollatzResearch.WordTrace tailWord_3938879 prefixEnd_3938879 2022538166900999851497931 := by
  unfold tailWord_3938879
  simp only [CollatzResearch.WordTrace]
  refine ⟨143662719497121564821371691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95775146331414376547581127 143662719497121564821371691)
  ·
    refine ⟨215494079245682347232057537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143662719497121564821371691 215494079245682347232057537)
    ·
      refine ⟨161620559434261760424043153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215494079245682347232057537 161620559434261760424043153)
      ·
        refine ⟨121215419575696320318032365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161620559434261760424043153 121215419575696320318032365)
        ·
          refine ⟨45455782340886120119262137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121215419575696320318032365 45455782340886120119262137)
          ·
            refine ⟨34091836755664590089446603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45455782340886120119262137 34091836755664590089446603)
            ·
              refine ⟨51137755133496885134169905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34091836755664590089446603 51137755133496885134169905)
              ·
                refine ⟨38353316350122663850627429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51137755133496885134169905 38353316350122663850627429)
                ·
                  refine ⟨7191246815647999471992643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38353316350122663850627429 7191246815647999471992643)
                  ·
                    refine ⟨10786870223471999207988965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7191246815647999471992643 10786870223471999207988965)
                    ·
                      refine ⟨2022538166900999851497931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10786870223471999207988965 2022538166900999851497931)
                      ·
                        rfl

theorem cell23_3938879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_3938879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938879 prefixEnd_3938879 := by exact prefixLift 3938879
  have htrace : WordTrace (prefixWord ++ tailWord_3938879) baseStart_3938879 baseEnd_3938879 := by
    simpa [prefixWord, tailWord_3938879, baseEnd_3938879] using wordTrace_append hprefix tailTrace_3938879
  have hstable : (prefixWord ++ tailWord_3938879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938879).length < 2 ^ (prefixWord ++ tailWord_3938879).sum := by decide
  have hdescent : baseEnd_3938879 < baseStart_3938879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938893 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3938893 : Nat := 118140960795 + 3938893 * 2 ^ 59
def prefixEnd_3938893 : Nat := 4983230072969 + 3 ^ 40 * 3938893 * 2
def baseEnd_3938893 : Nat := 674181785210054265574289

theorem tailTrace_3938893 : CollatzResearch.WordTrace tailWord_3938893 prefixEnd_3938893 674181785210054265574289 := by
  unfold tailWord_3938893
  simp only [CollatzResearch.WordTrace]
  refine ⟨143663230119070845212381333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95775486746047230141587555 143663230119070845212381333)
  ·
    refine ⟨6734213911831445869330375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143663230119070845212381333 6734213911831445869330375)
    ·
      refine ⟨10101320867747168803995563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6734213911831445869330375 10101320867747168803995563)
      ·
        refine ⟨15151981301620753205993345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10101320867747168803995563 15151981301620753205993345)
        ·
          refine ⟨11363985976215564904495009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15151981301620753205993345 11363985976215564904495009)
          ·
            refine ⟨8522989482161673678371257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11363985976215564904495009 8522989482161673678371257)
            ·
              refine ⟨6392242111621255258778443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8522989482161673678371257 6392242111621255258778443)
              ·
                refine ⟨9588363167431882888167665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392242111621255258778443 9588363167431882888167665)
                ·
                  refine ⟨7191272375573912166125749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9588363167431882888167665 7191272375573912166125749)
                  ·
                    refine ⟨674181785210054265574289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7191272375573912166125749 674181785210054265574289)
                    ·
                      rfl

theorem cell23_3938893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3938893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938893 prefixEnd_3938893 := by exact prefixLift 3938893
  have htrace : WordTrace (prefixWord ++ tailWord_3938893) baseStart_3938893 baseEnd_3938893 := by
    simpa [prefixWord, tailWord_3938893, baseEnd_3938893] using wordTrace_append hprefix tailTrace_3938893
  have hstable : (prefixWord ++ tailWord_3938893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938893).length < 2 ^ (prefixWord ++ tailWord_3938893).sum := by decide
  have hdescent : baseEnd_3938893 < baseStart_3938893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938914 : List Nat := [3, 3, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3938914 : Nat := 118140960795 + 3938914 * 2 ^ 59
def prefixEnd_3938914 : Nat := 4983230072969 + 3 ^ 40 * 3938914 * 2
def baseEnd_3938914 : Nat := 224728459858211912728919

theorem tailTrace_3938914 : CollatzResearch.WordTrace tailWord_3938914 prefixEnd_3938914 224728459858211912728919 := by
  unfold tailWord_3938914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35915999012998691449723949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95775997367996510532597197 35915999012998691449723949)
  ·
    refine ⟨13468499629874509293646481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35915999012998691449723949 13468499629874509293646481)
    ·
      refine ⟨10101374722405881970234861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13468499629874509293646481 10101374722405881970234861)
      ·
        refine ⟨3788015520902205738838073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10101374722405881970234861 3788015520902205738838073)
        ·
          refine ⟨2841011640676654304128555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3788015520902205738838073 2841011640676654304128555)
          ·
            refine ⟨4261517461014981456192833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841011640676654304128555 4261517461014981456192833)
            ·
              refine ⟨3196138095761236092144625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261517461014981456192833 3196138095761236092144625)
              ·
                refine ⟨2397103571820927069108469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196138095761236092144625 2397103571820927069108469)
                ·
                  refine ⟨224728459858211912728919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397103571820927069108469 224728459858211912728919)
                  ·
                    rfl

theorem cell23_3938914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3938914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938914 prefixEnd_3938914 := by exact prefixLift 3938914
  have htrace : WordTrace (prefixWord ++ tailWord_3938914) baseStart_3938914 baseEnd_3938914 := by
    simpa [prefixWord, tailWord_3938914, baseEnd_3938914] using wordTrace_append hprefix tailTrace_3938914
  have hstable : (prefixWord ++ tailWord_3938914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938914).length < 2 ^ (prefixWord ++ tailWord_3938914).sum := by decide
  have hdescent : baseEnd_3938914 < baseStart_3938914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938916 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_3938916 : Nat := 118140960795 + 3938916 * 2 ^ 59
def prefixEnd_3938916 : Nat := 4983230072969 + 3 ^ 40 * 3938916 * 2
def baseEnd_3938916 : Nat := 2022557165685216206735261

theorem tailTrace_3938916 : CollatzResearch.WordTrace tailWord_3938916 prefixEnd_3938916 2022557165685216206735261 := by
  unfold tailWord_3938916
  simp only [CollatzResearch.WordTrace]
  refine ⟨71832034498993760070234301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95776045998658346760312401 71832034498993760070234301)
  ·
    refine ⟨26937012937122660026337863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71832034498993760070234301 26937012937122660026337863)
    ·
      refine ⟨40405519405683990039506795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26937012937122660026337863 40405519405683990039506795)
      ·
        refine ⟨60608279108525985059260193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40405519405683990039506795 60608279108525985059260193)
        ·
          refine ⟨45456209331394488794445145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60608279108525985059260193 45456209331394488794445145)
          ·
            refine ⟨34092156998545866595833859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45456209331394488794445145 34092156998545866595833859)
            ·
              refine ⟨51138235497818799893750789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34092156998545866595833859 51138235497818799893750789)
              ·
                refine ⟨9588419155841024980078273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51138235497818799893750789 9588419155841024980078273)
                ·
                  refine ⟨7191314366880768735058705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9588419155841024980078273 7191314366880768735058705)
                  ·
                    refine ⟨5393485775160576551294029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191314366880768735058705 5393485775160576551294029)
                    ·
                      refine ⟨2022557165685216206735261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393485775160576551294029 2022557165685216206735261)
                      ·
                        rfl

theorem cell23_3938916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_3938916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938916 prefixEnd_3938916 := by exact prefixLift 3938916
  have htrace : WordTrace (prefixWord ++ tailWord_3938916) baseStart_3938916 baseEnd_3938916 := by
    simpa [prefixWord, tailWord_3938916, baseEnd_3938916] using wordTrace_append hprefix tailTrace_3938916
  have hstable : (prefixWord ++ tailWord_3938916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938916).length < 2 ^ (prefixWord ++ tailWord_3938916).sum := by decide
  have hdescent : baseEnd_3938916 < baseStart_3938916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938929 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_3938929 : Nat := 118140960795 + 3938929 * 2 ^ 59
def prefixEnd_3938929 : Nat := 4983230072969 + 3 ^ 40 * 3938929 * 2
def baseEnd_3938929 : Nat := 2022563840933724655872701

theorem tailTrace_3938929 : CollatzResearch.WordTrace tailWord_3938929 prefixEnd_3938929 2022563840933724655872701 := by
  unfold tailWord_3938929
  simp only [CollatzResearch.WordTrace]
  refine ⟨143664543146940423360691841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95776362097960282240461227 143664543146940423360691841)
  ·
    refine ⟨107748407360205317520518881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143664543146940423360691841 107748407360205317520518881)
    ·
      refine ⟨80811305520153988140389161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107748407360205317520518881 80811305520153988140389161)
      ·
        refine ⟨60608479140115491105291871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80811305520153988140389161 60608479140115491105291871)
        ·
          refine ⟨90912718710173236657937807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60608479140115491105291871 90912718710173236657937807)
          ·
            refine ⟨136369078065259854986906711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90912718710173236657937807 136369078065259854986906711)
            ·
              refine ⟨204553617097889782480360067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136369078065259854986906711 204553617097889782480360067)
              ·
                refine ⟨306830425646834673720540101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204553617097889782480360067 306830425646834673720540101)
                ·
                  refine ⟨57530704808781501322601269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306830425646834673720540101 57530704808781501322601269)
                  ·
                    refine ⟨5393503575823265748993869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57530704808781501322601269 5393503575823265748993869)
                    ·
                      refine ⟨2022563840933724655872701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393503575823265748993869 2022563840933724655872701)
                      ·
                        rfl

theorem cell23_3938929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_3938929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938929 prefixEnd_3938929 := by exact prefixLift 3938929
  have htrace : WordTrace (prefixWord ++ tailWord_3938929) baseStart_3938929 baseEnd_3938929 := by
    simpa [prefixWord, tailWord_3938929, baseEnd_3938929] using wordTrace_append hprefix tailTrace_3938929
  have hstable : (prefixWord ++ tailWord_3938929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938929).length < 2 ^ (prefixWord ++ tailWord_3938929).sum := by decide
  have hdescent : baseEnd_3938929 < baseStart_3938929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938970 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 6]
def baseStart_3938970 : Nat := 118140960795 + 3938970 * 2 ^ 59
def prefixEnd_3938970 : Nat := 4983230072969 + 3 ^ 40 * 3938970 * 2
def baseEnd_3938970 : Nat := 224731654848950999495557

theorem tailTrace_3938970 : CollatzResearch.WordTrace tailWord_3938970 prefixEnd_3938970 224731654848950999495557 := by
  unfold tailWord_3938970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35916509634947971840733591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95777359026527924908622909 35916509634947971840733591)
  ·
    refine ⟨53874764452421957761100387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35916509634947971840733591 53874764452421957761100387)
    ·
      refine ⟨80812146678632936641650581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53874764452421957761100387 80812146678632936641650581)
      ·
        refine ⟨3788069375560918905077371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80812146678632936641650581 3788069375560918905077371)
        ·
          refine ⟨5682104063341378357616057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788069375560918905077371 5682104063341378357616057)
          ·
            refine ⟨4261578047506033768212043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682104063341378357616057 4261578047506033768212043)
            ·
              refine ⟨6392367071259050652318065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261578047506033768212043 6392367071259050652318065)
              ·
                refine ⟨4794275303444287989238549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392367071259050652318065 4794275303444287989238549)
                ·
                  refine ⟨224731654848950999495557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4794275303444287989238549 224731654848950999495557)
                  ·
                    rfl

theorem cell23_3938970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_3938970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938970 prefixEnd_3938970 := by exact prefixLift 3938970
  have htrace : WordTrace (prefixWord ++ tailWord_3938970) baseStart_3938970 baseEnd_3938970 := by
    simpa [prefixWord, tailWord_3938970, baseEnd_3938970] using wordTrace_append hprefix tailTrace_3938970
  have hstable : (prefixWord ++ tailWord_3938970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938970).length < 2 ^ (prefixWord ++ tailWord_3938970).sum := by decide
  have hdescent : baseEnd_3938970 < baseStart_3938970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938973 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_3938973 : Nat := 118140960795 + 3938973 * 2 ^ 59
def prefixEnd_3938973 : Nat := 4983230072969 + 3 ^ 40 * 3938973 * 2
def baseEnd_3938973 : Nat := 2022586434082522483722499

theorem tailTrace_3938973 : CollatzResearch.WordTrace tailWord_3938973 prefixEnd_3938973 2022586434082522483722499 := by
  unfold tailWord_3938973
  simp only [CollatzResearch.WordTrace]
  refine ⟨143666147958781018875293573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95777431972520679250195715 143666147958781018875293573)
  ·
    refine ⟨26937402742271441039117545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143666147958781018875293573 26937402742271441039117545)
    ·
      refine ⟨20203052056703580779338159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26937402742271441039117545 20203052056703580779338159)
      ·
        refine ⟨30304578085055371169007239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20203052056703580779338159 30304578085055371169007239)
        ·
          refine ⟨45456867127583056753510859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30304578085055371169007239 45456867127583056753510859)
          ·
            refine ⟨68185300691374585130266289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45456867127583056753510859 68185300691374585130266289)
            ·
              refine ⟨51138975518530938847699717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68185300691374585130266289 51138975518530938847699717)
              ·
                refine ⟨9588557909724551033943697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51138975518530938847699717 9588557909724551033943697)
                ·
                  refine ⟨7191418432293413275457773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9588557909724551033943697 7191418432293413275457773)
                  ·
                    refine ⟨2696781912110029978296665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7191418432293413275457773 2696781912110029978296665)
                    ·
                      refine ⟨2022586434082522483722499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696781912110029978296665 2022586434082522483722499)
                      ·
                        rfl

theorem cell23_3938973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_3938973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938973 prefixEnd_3938973 := by exact prefixLift 3938973
  have htrace : WordTrace (prefixWord ++ tailWord_3938973) baseStart_3938973 baseEnd_3938973 := by
    simpa [prefixWord, tailWord_3938973, baseEnd_3938973] using wordTrace_append hprefix tailTrace_3938973
  have hstable : (prefixWord ++ tailWord_3938973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938973).length < 2 ^ (prefixWord ++ tailWord_3938973).sum := by decide
  have hdescent : baseEnd_3938973 < baseStart_3938973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938980 : List Nat := [2, 3, 1, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_3938980 : Nat := 118140960795 + 3938980 * 2 ^ 59
def prefixEnd_3938980 : Nat := 4983230072969 + 3 ^ 40 * 3938980 * 2
def baseEnd_3938980 : Nat := 2022590028447103956334967

theorem tailTrace_3938980 : CollatzResearch.WordTrace tailWord_3938980 prefixEnd_3938980 2022590028447103956334967 := by
  unfold tailWord_3938980
  simp only [CollatzResearch.WordTrace]
  refine ⟨71833201634877829535399197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95777602179837106047198929 71833201634877829535399197)
  ·
    refine ⟨26937450613079186075774699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71833201634877829535399197 26937450613079186075774699)
    ·
      refine ⟨40406175919618779113662049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26937450613079186075774699 40406175919618779113662049)
      ·
        refine ⟨30304631939714084335246537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40406175919618779113662049 30304631939714084335246537)
        ·
          refine ⟨22728473954785563251434903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30304631939714084335246537 22728473954785563251434903)
          ·
            refine ⟨34092710932178344877152355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22728473954785563251434903 34092710932178344877152355)
            ·
              refine ⟨51139066398267517315728533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34092710932178344877152355 51139066398267517315728533)
              ·
                refine ⟨2397143737418789874174775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51139066398267517315728533 2397143737418789874174775)
                ·
                  refine ⟨3595715606128184811262163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397143737418789874174775 3595715606128184811262163)
                  ·
                    refine ⟨5393573409192277216893245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3595715606128184811262163 5393573409192277216893245)
                    ·
                      refine ⟨2022590028447103956334967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393573409192277216893245 2022590028447103956334967)
                      ·
                        rfl

theorem cell23_3938980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_3938980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938980 prefixEnd_3938980 := by exact prefixLift 3938980
  have htrace : WordTrace (prefixWord ++ tailWord_3938980) baseStart_3938980 baseEnd_3938980 := by
    simpa [prefixWord, tailWord_3938980, baseEnd_3938980] using wordTrace_append hprefix tailTrace_3938980
  have hstable : (prefixWord ++ tailWord_3938980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938980).length < 2 ^ (prefixWord ++ tailWord_3938980).sum := by decide
  have hdescent : baseEnd_3938980 < baseStart_3938980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938990 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3938990 : Nat := 118140960795 + 3938990 * 2 ^ 59
def prefixEnd_3938990 : Nat := 4983230072969 + 3 ^ 40 * 3938990 * 2
def baseEnd_3938990 : Nat := 2022595163253648917209921

theorem tailTrace_3938990 : CollatzResearch.WordTrace tailWord_3938990 prefixEnd_3938990 2022595163253648917209921 := by
  unfold tailWord_3938990
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958345999964928847332803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95777845333146287185774949 17958345999964928847332803)
  ·
    refine ⟨26937518999947393270999205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17958345999964928847332803 26937518999947393270999205)
    ·
      refine ⟨5050784812490136238312351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26937518999947393270999205 5050784812490136238312351)
      ·
        refine ⟨7576177218735204357468527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050784812490136238312351 7576177218735204357468527)
        ·
          refine ⟨11364265828102806536202791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576177218735204357468527 11364265828102806536202791)
          ·
            refine ⟨17046398742154209804304187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11364265828102806536202791 17046398742154209804304187)
            ·
              refine ⟨25569598113231314706456281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17046398742154209804304187 25569598113231314706456281)
              ·
                refine ⟨19177198584923486029842211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25569598113231314706456281 19177198584923486029842211)
                ·
                  refine ⟨28765797877385229044763317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19177198584923486029842211 28765797877385229044763317)
                  ·
                    refine ⟨2696793551004865222946561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28765797877385229044763317 2696793551004865222946561)
                    ·
                      refine ⟨2022595163253648917209921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696793551004865222946561 2022595163253648917209921)
                      ·
                        rfl

theorem cell23_3938990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3938990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3938990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3938990 prefixEnd_3938990 := by exact prefixLift 3938990
  have htrace : WordTrace (prefixWord ++ tailWord_3938990) baseStart_3938990 baseEnd_3938990 := by
    simpa [prefixWord, tailWord_3938990, baseEnd_3938990] using wordTrace_append hprefix tailTrace_3938990
  have hstable : (prefixWord ++ tailWord_3938990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938990).length < 2 ^ (prefixWord ++ tailWord_3938990).sum := by decide
  have hdescent : baseEnd_3938990 < baseStart_3938990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939006 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3939006 : Nat := 118140960795 + 3939006 * 2 ^ 59
def prefixEnd_3939006 : Nat := 4983230072969 + 3 ^ 40 * 3939006 * 2
def baseEnd_3939006 : Nat := 2022603378944120854609847

theorem tailTrace_3939006 : CollatzResearch.WordTrace tailWord_3939006 prefixEnd_3939006 2022603378944120854609847 := by
  unfold tailWord_3939006
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958418945957683188905609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95778234378440977007496581 17958418945957683188905609)
  ·
    refine ⟨13468814209468262391679207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17958418945957683188905609 13468814209468262391679207)
    ·
      refine ⟨20203221314202393587518811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13468814209468262391679207 20203221314202393587518811)
      ·
        refine ⟨30304831971303590381278217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20203221314202393587518811 30304831971303590381278217)
        ·
          refine ⟨22728623978477692785958663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30304831971303590381278217 22728623978477692785958663)
          ·
            refine ⟨34092935967716539178937995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22728623978477692785958663 34092935967716539178937995)
            ·
              refine ⟨51139403951574808768406993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34092935967716539178937995 51139403951574808768406993)
              ·
                refine ⟨38354552963681106576305245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51139403951574808768406993 38354552963681106576305245)
                ·
                  refine ⟨14382957361380414966114467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38354552963681106576305245 14382957361380414966114467)
                  ·
                    refine ⟨21574436042070622449171701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14382957361380414966114467 21574436042070622449171701)
                    ·
                      refine ⟨2022603378944120854609847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21574436042070622449171701 2022603378944120854609847)
                      ·
                        rfl

theorem cell23_3939006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3939006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939006 prefixEnd_3939006 := by exact prefixLift 3939006
  have htrace : WordTrace (prefixWord ++ tailWord_3939006) baseStart_3939006 baseEnd_3939006 := by
    simpa [prefixWord, tailWord_3939006, baseEnd_3939006] using wordTrace_append hprefix tailTrace_3939006
  have hstable : (prefixWord ++ tailWord_3939006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939006).length < 2 ^ (prefixWord ++ tailWord_3939006).sum := by decide
  have hdescent : baseEnd_3939006 < baseStart_3939006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939053 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3939053 : Nat := 118140960795 + 3939053 * 2 ^ 59
def prefixEnd_3939053 : Nat := 4983230072969 + 3 ^ 40 * 3939053 * 2
def baseEnd_3939053 : Nat := 2022627512534882170722131

theorem tailTrace_3939053 : CollatzResearch.WordTrace tailWord_3939053 prefixEnd_3939053 2022627512534882170722131 := by
  unfold tailWord_3939053
  simp only [CollatzResearch.WordTrace]
  refine ⟨143669065798491192538205813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95779377198994128358803875 143669065798491192538205813)
  ·
    refine ⟨13468974918608549300456795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143669065798491192538205813 13468974918608549300456795)
    ·
      refine ⟨20203462377912823950685193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13468974918608549300456795 20203462377912823950685193)
      ·
        refine ⟨15152596783434617963013895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20203462377912823950685193 15152596783434617963013895)
        ·
          refine ⟨22728895175151926944520843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15152596783434617963013895 22728895175151926944520843)
          ·
            refine ⟨34093342762727890416781265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22728895175151926944520843 34093342762727890416781265)
            ·
              refine ⟨25570007072045917812585949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34093342762727890416781265 25570007072045917812585949)
              ·
                refine ⟨9588752652017219179719731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25570007072045917812585949 9588752652017219179719731)
                ·
                  refine ⟨14383128978025828769579597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9588752652017219179719731 14383128978025828769579597)
                  ·
                    refine ⟨5393673366759685788592349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14383128978025828769579597 5393673366759685788592349)
                    ·
                      refine ⟨2022627512534882170722131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393673366759685788592349 2022627512534882170722131)
                      ·
                        rfl

theorem cell23_3939053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3939053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939053 prefixEnd_3939053 := by exact prefixLift 3939053
  have htrace : WordTrace (prefixWord ++ tailWord_3939053) baseStart_3939053 baseEnd_3939053 := by
    simpa [prefixWord, tailWord_3939053, baseEnd_3939053] using wordTrace_append hprefix tailTrace_3939053
  have hstable : (prefixWord ++ tailWord_3939053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939053).length < 2 ^ (prefixWord ++ tailWord_3939053).sum := by decide
  have hdescent : baseEnd_3939053 < baseStart_3939053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939059 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8]
def baseStart_3939059 : Nat := 118140960795 + 3939059 * 2 ^ 59
def prefixEnd_3939059 : Nat := 4983230072969 + 3 ^ 40 * 3939059 * 2
def baseEnd_3939059 : Nat := 2022630593418809147247103

theorem tailTrace_3939059 : CollatzResearch.WordTrace tailWord_3939059 prefixEnd_3939059 2022630593418809147247103 := by
  unfold tailWord_3939059
  simp only [CollatzResearch.WordTrace]
  refine ⟨143669284636469455562924231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95779523090979637041949487 143669284636469455562924231)
  ·
    refine ⟨215503926954704183344386347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143669284636469455562924231 215503926954704183344386347)
    ·
      refine ⟨323255890432056275016579521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215503926954704183344386347 323255890432056275016579521)
      ·
        refine ⟨242441917824042206262434641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323255890432056275016579521 242441917824042206262434641)
        ·
          refine ⟨181831438368031654696825981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242441917824042206262434641 181831438368031654696825981)
          ·
            refine ⟨68186789388011870511309743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181831438368031654696825981 68186789388011870511309743)
            ·
              refine ⟨102280184082017805766964615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68186789388011870511309743 102280184082017805766964615)
              ·
                refine ⟨153420276123026708650446923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102280184082017805766964615 153420276123026708650446923)
                ·
                  refine ⟨230130414184540062975670385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153420276123026708650446923 230130414184540062975670385)
                  ·
                    refine ⟨172597810638405047231752789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230130414184540062975670385 172597810638405047231752789)
                    ·
                      refine ⟨2022630593418809147247103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 172597810638405047231752789 2022630593418809147247103)
                      ·
                        rfl

theorem cell23_3939059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_3939059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939059 prefixEnd_3939059 := by exact prefixLift 3939059
  have htrace : WordTrace (prefixWord ++ tailWord_3939059) baseStart_3939059 baseEnd_3939059 := by
    simpa [prefixWord, tailWord_3939059, baseEnd_3939059] using wordTrace_append hprefix tailTrace_3939059
  have hstable : (prefixWord ++ tailWord_3939059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939059).length < 2 ^ (prefixWord ++ tailWord_3939059).sum := by decide
  have hdescent : baseEnd_3939059 < baseStart_3939059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939070 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3939070 : Nat := 118140960795 + 3939070 * 2 ^ 59
def prefixEnd_3939070 : Nat := 4983230072969 + 3 ^ 40 * 3939070 * 2
def baseEnd_3939070 : Nat := 2022636241706008604209553

theorem tailTrace_3939070 : CollatzResearch.WordTrace tailWord_3939070 prefixEnd_3939070 2022636241706008604209553 := by
  unfold tailWord_3939070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958710729928700555196833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95779790559619736294383109 17958710729928700555196833)
  ·
    refine ⟨13469033047446525416397625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17958710729928700555196833 13469033047446525416397625)
    ·
      refine ⟨10101774785584894062298219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13469033047446525416397625 10101774785584894062298219)
      ·
        refine ⟨15152662178377341093447329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10101774785584894062298219 15152662178377341093447329)
        ·
          refine ⟨11364496633783005820085497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15152662178377341093447329 11364496633783005820085497)
          ·
            refine ⟨8523372475337254365064123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11364496633783005820085497 8523372475337254365064123)
            ·
              refine ⟨12785058713005881547596185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8523372475337254365064123 12785058713005881547596185)
              ·
                refine ⟨9588794034754411160697139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12785058713005881547596185 9588794034754411160697139)
                ·
                  refine ⟨14383191052131616741045709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9588794034754411160697139 14383191052131616741045709)
                  ·
                    refine ⟨5393696644549356277892141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14383191052131616741045709 5393696644549356277892141)
                    ·
                      refine ⟨2022636241706008604209553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393696644549356277892141 2022636241706008604209553)
                      ·
                        rfl

theorem cell23_3939070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3939070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939070 prefixEnd_3939070 := by exact prefixLift 3939070
  have htrace : WordTrace (prefixWord ++ tailWord_3939070) baseStart_3939070 baseEnd_3939070 := by
    simpa [prefixWord, tailWord_3939070, baseEnd_3939070] using wordTrace_append hprefix tailTrace_3939070
  have hstable : (prefixWord ++ tailWord_3939070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939070).length < 2 ^ (prefixWord ++ tailWord_3939070).sum := by decide
  have hdescent : baseEnd_3939070 < baseStart_3939070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939086 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_3939086 : Nat := 118140960795 + 3939086 * 2 ^ 59
def prefixEnd_3939086 : Nat := 4983230072969 + 3 ^ 40 * 3939086 * 2
def baseEnd_3939086 : Nat := 674214819132160180536493

theorem tailTrace_3939086 : CollatzResearch.WordTrace tailWord_3939086 prefixEnd_3939086 674214819132160180536493 := by
  unfold tailWord_3939086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958783675921454896769639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95780179604914426116104741 17958783675921454896769639)
  ·
    refine ⟨26938175513882182345154459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17958783675921454896769639 26938175513882182345154459)
    ·
      refine ⟨40407263270823273517731689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26938175513882182345154459 40407263270823273517731689)
      ·
        refine ⟨30305447453117455138298767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40407263270823273517731689 30305447453117455138298767)
        ·
          refine ⟨45458171179676182707448151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30305447453117455138298767 45458171179676182707448151)
          ·
            refine ⟨68187256769514274061172227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45458171179676182707448151 68187256769514274061172227)
            ·
              refine ⟨102280885154271411091758341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68187256769514274061172227 102280885154271411091758341)
              ·
                refine ⟨19177665966425889579704689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102280885154271411091758341 19177665966425889579704689)
                ·
                  refine ⟨14383249474819417184778517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19177665966425889579704689 14383249474819417184778517)
                  ·
                    refine ⟨674214819132160180536493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14383249474819417184778517 674214819132160180536493)
                    ·
                      rfl

theorem cell23_3939086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_3939086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939086 prefixEnd_3939086 := by exact prefixLift 3939086
  have htrace : WordTrace (prefixWord ++ tailWord_3939086) baseStart_3939086 baseEnd_3939086 := by
    simpa [prefixWord, tailWord_3939086, baseEnd_3939086] using wordTrace_append hprefix tailTrace_3939086
  have hstable : (prefixWord ++ tailWord_3939086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939086).length < 2 ^ (prefixWord ++ tailWord_3939086).sum := by decide
  have hdescent : baseEnd_3939086 < baseStart_3939086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939093 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_3939093 : Nat := 118140960795 + 3939093 * 2 ^ 59
def prefixEnd_3939093 : Nat := 4983230072969 + 3 ^ 40 * 3939093 * 2
def baseEnd_3939093 : Nat := 2022648051761062014221947

theorem tailTrace_3939093 : CollatzResearch.WordTrace tailWord_3939093 prefixEnd_3939093 2022648051761062014221947 := by
  unfold tailWord_3939093
  simp only [CollatzResearch.WordTrace]
  refine ⟨143670524718346279369661933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95780349812230852913107955 143670524718346279369661933)
  ·
    refine ⟨53876446769379854763623225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143670524718346279369661933 53876446769379854763623225)
    ·
      refine ⟨40407335077034891072717419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53876446769379854763623225 40407335077034891072717419)
      ·
        refine ⟨60611002615552336609076129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40407335077034891072717419 60611002615552336609076129)
        ·
          refine ⟨45458251961664252456807097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60611002615552336609076129 45458251961664252456807097)
          ·
            refine ⟨34093688971248189342605323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45458251961664252456807097 34093688971248189342605323)
            ·
              refine ⟨51140533456872284013907985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34093688971248189342605323 51140533456872284013907985)
              ·
                refine ⟨38355400092654213010430989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51140533456872284013907985 38355400092654213010430989)
                ·
                  refine ⟨14383275034745329878911621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38355400092654213010430989 14383275034745329878911621)
                  ·
                    refine ⟨2696864069014749352295929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14383275034745329878911621 2696864069014749352295929)
                    ·
                      refine ⟨2022648051761062014221947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696864069014749352295929 2022648051761062014221947)
                      ·
                        rfl

theorem cell23_3939093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_3939093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939093 prefixEnd_3939093 := by exact prefixLift 3939093
  have htrace : WordTrace (prefixWord ++ tailWord_3939093) baseStart_3939093 baseEnd_3939093 := by
    simpa [prefixWord, tailWord_3939093, baseEnd_3939093] using wordTrace_append hprefix tailTrace_3939093
  have hstable : (prefixWord ++ tailWord_3939093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939093).length < 2 ^ (prefixWord ++ tailWord_3939093).sum := by decide
  have hdescent : baseEnd_3939093 < baseStart_3939093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939116 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 7]
def baseStart_3939116 : Nat := 118140960795 + 3939116 * 2 ^ 59
def prefixEnd_3939116 : Nat := 4983230072969 + 3 ^ 40 * 3939116 * 2
def baseEnd_3939116 : Nat := 224739984646235047137149

theorem tailTrace_3939116 : CollatzResearch.WordTrace tailWord_3939116 prefixEnd_3939116 224739984646235047137149 := by
  unfold tailWord_3939116
  simp only [CollatzResearch.WordTrace]
  refine ⟨71835681798631477148874601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95780909064841969531832801 71835681798631477148874601)
  ·
    refine ⟨53876761348973607861655951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71835681798631477148874601 53876761348973607861655951)
    ·
      refine ⟨80815142023460411792483927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53876761348973607861655951 80815142023460411792483927)
      ·
        refine ⟨121222713035190617688725891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80815142023460411792483927 121222713035190617688725891)
        ·
          refine ⟨181834069552785926533088837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121222713035190617688725891 181834069552785926533088837)
          ·
            refine ⟨34093888041147361224954157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181834069552785926533088837 34093888041147361224954157)
            ·
              refine ⟨12785208015430260459357809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34093888041147361224954157 12785208015430260459357809)
              ·
                refine ⟨9588906011572695344518357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12785208015430260459357809 9588906011572695344518357)
                ·
                  refine ⟨224739984646235047137149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9588906011572695344518357 224739984646235047137149)
                  ·
                    rfl

theorem cell23_3939116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_3939116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939116 prefixEnd_3939116 := by exact prefixLift 3939116
  have htrace : WordTrace (prefixWord ++ tailWord_3939116) baseStart_3939116 baseEnd_3939116 := by
    simpa [prefixWord, tailWord_3939116, baseEnd_3939116] using wordTrace_append hprefix tailTrace_3939116
  have hstable : (prefixWord ++ tailWord_3939116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939116).length < 2 ^ (prefixWord ++ tailWord_3939116).sum := by decide
  have hdescent : baseEnd_3939116 < baseStart_3939116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939183 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 1, 6, 2]
def baseStart_3939183 : Nat := 118140960795 + 3939183 * 2 ^ 59
def prefixEnd_3939183 : Nat := 4983230072969 + 3 ^ 40 * 3939183 * 2
def baseEnd_3939183 : Nat := 2022694265019966662096533

theorem tailTrace_3939183 : CollatzResearch.WordTrace tailWord_3939183 prefixEnd_3939183 2022694265019966662096533 := by
  unfold tailWord_3939183
  simp only [CollatzResearch.WordTrace]
  refine ⟨143673807288020224740438203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95782538192013483160292135 143673807288020224740438203)
  ·
    refine ⟨215510710932030337110657305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143673807288020224740438203 215510710932030337110657305)
    ·
      refine ⟨161633033199022752832992979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215510710932030337110657305 161633033199022752832992979)
      ·
        refine ⟨242449549798534129249489469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161633033199022752832992979 242449549798534129249489469)
        ·
          refine ⟨90918581174450298468558551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242449549798534129249489469 90918581174450298468558551)
          ·
            refine ⟨136377871761675447702837827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90918581174450298468558551 136377871761675447702837827)
            ·
              refine ⟨204566807642513171554256741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136377871761675447702837827 204566807642513171554256741)
              ·
                refine ⟨38356276432971219666423139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204566807642513171554256741 38356276432971219666423139)
                ·
                  refine ⟨57534414649456829499634709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38356276432971219666423139 57534414649456829499634709)
                  ·
                    refine ⟨2696925686693288882795377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57534414649456829499634709 2696925686693288882795377)
                    ·
                      refine ⟨2022694265019966662096533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2696925686693288882795377 2022694265019966662096533)
                      ·
                        rfl

theorem cell23_3939183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6, 2].length) (baseStart_3939183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939183 prefixEnd_3939183 := by exact prefixLift 3939183
  have htrace : WordTrace (prefixWord ++ tailWord_3939183) baseStart_3939183 baseEnd_3939183 := by
    simpa [prefixWord, tailWord_3939183, baseEnd_3939183] using wordTrace_append hprefix tailTrace_3939183
  have hstable : (prefixWord ++ tailWord_3939183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939183).length < 2 ^ (prefixWord ++ tailWord_3939183).sum := by decide
  have hdescent : baseEnd_3939183 < baseStart_3939183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939196 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3939196 : Nat := 118140960795 + 3939196 * 2 ^ 59
def prefixEnd_3939196 : Nat := 4983230072969 + 3 ^ 40 * 3939196 * 2
def baseEnd_3939196 : Nat := 2022700940268475111233973

theorem tailTrace_3939196 : CollatzResearch.WordTrace tailWord_3939196 prefixEnd_3939196 2022700940268475111233973 := by
  unfold tailWord_3939196
  simp only [CollatzResearch.WordTrace]
  refine ⟨71837140718486563980330721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95782854291315418640440961 71837140718486563980330721)
  ·
    refine ⟨53877855538864922985248041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71837140718486563980330721 53877855538864922985248041)
    ·
      refine ⟨40408391654148692238936031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53877855538864922985248041 40408391654148692238936031)
      ·
        refine ⟨60612587481223038358404047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40408391654148692238936031 60612587481223038358404047)
        ·
          refine ⟨90918881221834557537606071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60612587481223038358404047 90918881221834557537606071)
          ·
            refine ⟨136378321832751836306409107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90918881221834557537606071 136378321832751836306409107)
            ·
              refine ⟨204567482749127754459613661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136378321832751836306409107 204567482749127754459613661)
              ·
                refine ⟨76712806030922907922355123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204567482749127754459613661 76712806030922907922355123)
                ·
                  refine ⟨115069209046384361883532685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76712806030922907922355123 115069209046384361883532685)
                  ·
                    refine ⟨43150953392394135706324757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115069209046384361883532685 43150953392394135706324757)
                    ·
                      refine ⟨2022700940268475111233973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43150953392394135706324757 2022700940268475111233973)
                      ·
                        rfl

theorem cell23_3939196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3939196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939196 prefixEnd_3939196 := by exact prefixLift 3939196
  have htrace : WordTrace (prefixWord ++ tailWord_3939196) baseStart_3939196 baseEnd_3939196 := by
    simpa [prefixWord, tailWord_3939196, baseEnd_3939196] using wordTrace_append hprefix tailTrace_3939196
  have hstable : (prefixWord ++ tailWord_3939196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939196).length < 2 ^ (prefixWord ++ tailWord_3939196).sum := by decide
  have hdescent : baseEnd_3939196 < baseStart_3939196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939220 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3939220 : Nat := 118140960795 + 3939220 * 2 ^ 59
def prefixEnd_3939220 : Nat := 4983230072969 + 3 ^ 40 * 3939220 * 2
def baseEnd_3939220 : Nat := 2022713263804183017333863

theorem tailTrace_3939220 : CollatzResearch.WordTrace tailWord_3939220 prefixEnd_3939220 2022713263804183017333863 := by
  unfold tailWord_3939220
  simp only [CollatzResearch.WordTrace]
  refine ⟨71837578394443090029767557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95783437859257453373023409 71837578394443090029767557)
  ·
    refine ⟨13469545948958079380581417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71837578394443090029767557 13469545948958079380581417)
    ·
      refine ⟨10102159461718559535436063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13469545948958079380581417 10102159461718559535436063)
      ·
        refine ⟨15153239192577839303154095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10102159461718559535436063 15153239192577839303154095)
        ·
          refine ⟨22729858788866758954731143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15153239192577839303154095 22729858788866758954731143)
          ·
            refine ⟨34094788183300138432096715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22729858788866758954731143 34094788183300138432096715)
            ·
              refine ⟨51142182274950207648145073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34094788183300138432096715 51142182274950207648145073)
              ·
                refine ⟨38356636706212655736108805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51142182274950207648145073 38356636706212655736108805)
                ·
                  refine ⟨7191869382414872950520401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38356636706212655736108805 7191869382414872950520401)
                  ·
                    refine ⟨5393902036811154712890301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7191869382414872950520401 5393902036811154712890301)
                    ·
                      refine ⟨2022713263804183017333863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393902036811154712890301 2022713263804183017333863)
                      ·
                        rfl

theorem cell23_3939220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3939220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939220 prefixEnd_3939220 := by exact prefixLift 3939220
  have htrace : WordTrace (prefixWord ++ tailWord_3939220) baseStart_3939220 baseEnd_3939220 := by
    simpa [prefixWord, tailWord_3939220, baseEnd_3939220] using wordTrace_append hprefix tailTrace_3939220
  have hstable : (prefixWord ++ tailWord_3939220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939220).length < 2 ^ (prefixWord ++ tailWord_3939220).sum := by decide
  have hdescent : baseEnd_3939220 < baseStart_3939220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939223 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 6]
def baseStart_3939223 : Nat := 118140960795 + 3939223 * 2 ^ 59
def prefixEnd_3939223 : Nat := 4983230072969 + 3 ^ 40 * 3939223 * 2
def baseEnd_3939223 : Nat := 224746089360682945066261

theorem tailTrace_3939223 : CollatzResearch.WordTrace tailWord_3939223 prefixEnd_3939223 224746089360682945066261 := by
  unfold tailWord_3939223
  simp only [CollatzResearch.WordTrace]
  refine ⟨143675266207875311571894323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95783510805250207714596215 143675266207875311571894323)
  ·
    refine ⟨215512899311812967357841485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143675266207875311571894323 215512899311812967357841485)
    ·
      refine ⟨80817337241929862759190557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215512899311812967357841485 80817337241929862759190557)
      ·
        refine ⟨30306501465723698534696459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80817337241929862759190557 30306501465723698534696459)
        ·
          refine ⟨45459752198585547802044689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30306501465723698534696459 45459752198585547802044689)
          ·
            refine ⟨34094814148939160851533517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45459752198585547802044689 34094814148939160851533517)
            ·
              refine ⟨12785555305852185319325069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34094814148939160851533517 12785555305852185319325069)
              ·
                refine ⟨4794583239694569494746901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12785555305852185319325069 4794583239694569494746901)
                ·
                  refine ⟨224746089360682945066261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4794583239694569494746901 224746089360682945066261)
                  ·
                    rfl

theorem cell23_3939223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 6].length) (baseStart_3939223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939223 prefixEnd_3939223 := by exact prefixLift 3939223
  have htrace : WordTrace (prefixWord ++ tailWord_3939223) baseStart_3939223 baseEnd_3939223 := by
    simpa [prefixWord, tailWord_3939223, baseEnd_3939223] using wordTrace_append hprefix tailTrace_3939223
  have hstable : (prefixWord ++ tailWord_3939223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939223).length < 2 ^ (prefixWord ++ tailWord_3939223).sum := by decide
  have hdescent : baseEnd_3939223 < baseStart_3939223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939261 : List Nat := [1, 4, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_3939261 : Nat := 118140960795 + 3939261 * 2 ^ 59
def prefixEnd_3939261 : Nat := 4983230072969 + 3 ^ 40 * 3939261 * 2
def baseEnd_3939261 : Nat := 674244772170339118973725

theorem tailTrace_3939261 : CollatzResearch.WordTrace tailWord_3939261 prefixEnd_3939261 674244772170339118973725 := by
  unfold tailWord_3939261
  simp only [CollatzResearch.WordTrace]
  refine ⟨143676652181737644061777637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95784434787825096041185091 143676652181737644061777637)
  ·
    refine ⟨26939372284075808261583307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143676652181737644061777637 26939372284075808261583307)
    ·
      refine ⟨40409058426113712392374961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26939372284075808261583307 40409058426113712392374961)
      ·
        refine ⟨30306793819585284294281221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40409058426113712392374961 30306793819585284294281221)
        ·
          refine ⟨5682523841172240805177729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30306793819585284294281221 5682523841172240805177729)
          ·
            refine ⟨4261892880879180603883297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682523841172240805177729 4261892880879180603883297)
            ·
              refine ⟨3196419660659385452912473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261892880879180603883297 3196419660659385452912473)
              ·
                refine ⟨2397314745494539089684355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196419660659385452912473 2397314745494539089684355)
                ·
                  refine ⟨3595972118241808634526533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397314745494539089684355 3595972118241808634526533)
                  ·
                    refine ⟨674244772170339118973725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3595972118241808634526533 674244772170339118973725)
                    ·
                      rfl

theorem cell23_3939261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_3939261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939261 prefixEnd_3939261 := by exact prefixLift 3939261
  have htrace : WordTrace (prefixWord ++ tailWord_3939261) baseStart_3939261 baseEnd_3939261 := by
    simpa [prefixWord, tailWord_3939261, baseEnd_3939261] using wordTrace_append hprefix tailTrace_3939261
  have hstable : (prefixWord ++ tailWord_3939261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939261).length < 2 ^ (prefixWord ++ tailWord_3939261).sum := by decide
  have hdescent : baseEnd_3939261 < baseStart_3939261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939267 : List Nat := [1, 1, 1, 3, 1, 1, 2, 8, 1, 1, 3]
def baseStart_3939267 : Nat := 118140960795 + 3939267 * 2 ^ 59
def prefixEnd_3939267 : Nat := 4983230072969 + 3 ^ 40 * 3939267 * 2
def baseEnd_3939267 : Nat := 2022737397394944333446147

theorem tailTrace_3939267 : CollatzResearch.WordTrace tailWord_3939267 prefixEnd_3939267 2022737397394944333446147 := by
  unfold tailWord_3939267
  simp only [CollatzResearch.WordTrace]
  refine ⟨143676871019715907086496055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95784580679810604724330703 143676871019715907086496055)
  ·
    refine ⟨215515306529573860629744083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143676871019715907086496055 215515306529573860629744083)
    ·
      refine ⟨323272959794360790944616125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215515306529573860629744083 323272959794360790944616125)
      ·
        refine ⟨121227359922885296604231047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323272959794360790944616125 121227359922885296604231047)
        ·
          refine ⟨181841039884327944906346571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121227359922885296604231047 181841039884327944906346571)
          ·
            refine ⟨272761559826491917359519857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181841039884327944906346571 272761559826491917359519857)
            ·
              refine ⟨204571169869868938019639893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272761559826491917359519857 204571169869868938019639893)
              ·
                refine ⟨2397318396912526617417655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 204571169869868938019639893 2397318396912526617417655)
                ·
                  refine ⟨3595977595368789926126483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397318396912526617417655 3595977595368789926126483)
                  ·
                    refine ⟨5393966393053184889189725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3595977595368789926126483 5393966393053184889189725)
                    ·
                      refine ⟨2022737397394944333446147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5393966393053184889189725 2022737397394944333446147)
                      ·
                        rfl

theorem cell23_3939267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_3939267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939267 prefixEnd_3939267 := by exact prefixLift 3939267
  have htrace : WordTrace (prefixWord ++ tailWord_3939267) baseStart_3939267 baseEnd_3939267 := by
    simpa [prefixWord, tailWord_3939267, baseEnd_3939267] using wordTrace_append hprefix tailTrace_3939267
  have hstable : (prefixWord ++ tailWord_3939267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939267).length < 2 ^ (prefixWord ++ tailWord_3939267).sum := by decide
  have hdescent : baseEnd_3939267 < baseStart_3939267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939290 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_3939290 : Nat := 118140960795 + 3939290 * 2 ^ 59
def prefixEnd_3939290 : Nat := 4983230072969 + 3 ^ 40 * 3939290 * 2
def baseEnd_3939290 : Nat := 2022749207449997743458541

theorem tailTrace_3939290 : CollatzResearch.WordTrace tailWord_3939290 prefixEnd_3939290 2022749207449997743458541 := by
  unfold tailWord_3939290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35919427474658145503645831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95785139932421721343055549 35919427474658145503645831)
  ·
    refine ⟨53879141211987218255468747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35919427474658145503645831 53879141211987218255468747)
    ·
      refine ⟨80818711817980827383203121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53879141211987218255468747 80818711817980827383203121)
      ·
        refine ⟨60614033863485620537402341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80818711817980827383203121 60614033863485620537402341)
        ·
          refine ⟨11365131349403553850762939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60614033863485620537402341 11365131349403553850762939)
          ·
            refine ⟨17047697024105330776144409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365131349403553850762939 17047697024105330776144409)
            ·
              refine ⟨12785772768078998082108307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17047697024105330776144409 12785772768078998082108307)
              ·
                refine ⟨19178659152118497123162461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12785772768078998082108307 19178659152118497123162461)
                ·
                  refine ⟨7191997182044436421185923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19178659152118497123162461 7191997182044436421185923)
                  ·
                    refine ⟨10787995773066654631778885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7191997182044436421185923 10787995773066654631778885)
                    ·
                      refine ⟨2022749207449997743458541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10787995773066654631778885 2022749207449997743458541)
                      ·
                        rfl

theorem cell23_3939290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_3939290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939290 prefixEnd_3939290 := by exact prefixLift 3939290
  have htrace : WordTrace (prefixWord ++ tailWord_3939290) baseStart_3939290 baseEnd_3939290 := by
    simpa [prefixWord, tailWord_3939290, baseEnd_3939290] using wordTrace_append hprefix tailTrace_3939290
  have hstable : (prefixWord ++ tailWord_3939290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939290).length < 2 ^ (prefixWord ++ tailWord_3939290).sum := by decide
  have hdescent : baseEnd_3939290 < baseStart_3939290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939313 : List Nat := [1, 2, 2, 2, 4, 2, 10]
def baseStart_3939313 : Nat := 118140960795 + 3939313 * 2 ^ 59
def prefixEnd_3939313 : Nat := 4983230072969 + 3 ^ 40 * 3939313 * 2
def baseEnd_3939313 : Nat := 24972358240803100660135

theorem tailTrace_3939313 : CollatzResearch.WordTrace tailWord_3939313 prefixEnd_3939313 24972358240803100660135 := by
  unfold tailWord_3939313
  simp only [CollatzResearch.WordTrace]
  refine ⟨143678548777549256942670593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95785699185032837961780395 143678548777549256942670593)
  ·
    refine ⟨107758911583161942707002945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143678548777549256942670593 107758911583161942707002945)
    ·
      refine ⟨80819183687371457030252209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107758911583161942707002945 80819183687371457030252209)
      ·
        refine ⟨60614387765528592772689157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80819183687371457030252209 60614387765528592772689157)
        ·
          refine ⟨11365197706036611144879217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60614387765528592772689157 11365197706036611144879217)
          ·
            refine ⟨8523898279527458358659413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11365197706036611144879217 8523898279527458358659413)
            ·
              refine ⟨24972358240803100660135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8523898279527458358659413 24972358240803100660135)
              ·
                rfl

theorem cell23_3939313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 10].length) (baseStart_3939313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939313 prefixEnd_3939313 := by exact prefixLift 3939313
  have htrace : WordTrace (prefixWord ++ tailWord_3939313) baseStart_3939313 baseEnd_3939313 := by
    simpa [prefixWord, tailWord_3939313, baseEnd_3939313] using wordTrace_append hprefix tailTrace_3939313
  have hstable : (prefixWord ++ tailWord_3939313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939313).length < 2 ^ (prefixWord ++ tailWord_3939313).sum := by decide
  have hdescent : baseEnd_3939313 < baseStart_3939313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939324 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_3939324 : Nat := 118140960795 + 3939324 * 2 ^ 59
def prefixEnd_3939324 : Nat := 4983230072969 + 3 ^ 40 * 3939324 * 2
def baseEnd_3939324 : Nat := 2022766665792250610433385

theorem tailTrace_3939324 : CollatzResearch.WordTrace tailWord_3939324 prefixEnd_3939324 2022766665792250610433385 := by
  unfold tailWord_3939324
  simp only [CollatzResearch.WordTrace]
  refine ⟨71839474990254702910660513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95785966653672937214214017 71839474990254702910660513)
  ·
    refine ⟨53879606242691027182995385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71839474990254702910660513 53879606242691027182995385)
    ·
      refine ⟨40409704682018270387246539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53879606242691027182995385 40409704682018270387246539)
      ·
        refine ⟨60614557023027405580869809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40409704682018270387246539 60614557023027405580869809)
        ·
          refine ⟨45460917767270554185652357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60614557023027405580869809 45460917767270554185652357)
          ·
            refine ⟨8523922081363228909809817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45460917767270554185652357 8523922081363228909809817)
            ·
              refine ⟨6392941561022421682357363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8523922081363228909809817 6392941561022421682357363)
              ·
                refine ⟨9589412341533632523536045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392941561022421682357363 9589412341533632523536045)
                ·
                  refine ⟨3596029628075112196326017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9589412341533632523536045 3596029628075112196326017)
                  ·
                    refine ⟨2697022221056334147244513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3596029628075112196326017 2697022221056334147244513)
                    ·
                      refine ⟨2022766665792250610433385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697022221056334147244513 2022766665792250610433385)
                      ·
                        rfl

theorem cell23_3939324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_3939324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939324 prefixEnd_3939324 := by exact prefixLift 3939324
  have htrace : WordTrace (prefixWord ++ tailWord_3939324) baseStart_3939324 baseEnd_3939324 := by
    simpa [prefixWord, tailWord_3939324, baseEnd_3939324] using wordTrace_append hprefix tailTrace_3939324
  have hstable : (prefixWord ++ tailWord_3939324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939324).length < 2 ^ (prefixWord ++ tailWord_3939324).sum := by decide
  have hdescent : baseEnd_3939324 < baseStart_3939324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939353 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_3939353 : Nat := 118140960795 + 3939353 * 2 ^ 59
def prefixEnd_3939353 : Nat := 4983230072969 + 3 ^ 40 * 3939353 * 2
def baseEnd_3939353 : Nat := 2022781556731230996970751

theorem tailTrace_3939353 : CollatzResearch.WordTrace tailWord_3939353 prefixEnd_3939353 2022781556731230996970751 := by
  unfold tailWord_3939353
  simp only [CollatzResearch.WordTrace]
  refine ⟨143680007697404343774126713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95786671798269562516084475 143680007697404343774126713)
  ·
    refine ⟨107760005773053257830595035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143680007697404343774126713 107760005773053257830595035)
    ·
      refine ⟨161640008659579886745892553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107760005773053257830595035 161640008659579886745892553)
      ·
        refine ⟨121230006494684915059419415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161640008659579886745892553 121230006494684915059419415)
        ·
          refine ⟨181845009742027372589129123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121230006494684915059419415 181845009742027372589129123)
          ·
            refine ⟨272767514613041058883693685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181845009742027372589129123 272767514613041058883693685)
            ·
              refine ⟨25571954494972599270346283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272767514613041058883693685 25571954494972599270346283)
              ·
                refine ⟨38357931742458898905519425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25571954494972599270346283 38357931742458898905519425)
                ·
                  refine ⟨28768448806844174179139569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38357931742458898905519425 28768448806844174179139569)
                  ·
                    refine ⟨21576336605133130634354677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28768448806844174179139569 21576336605133130634354677)
                    ·
                      refine ⟨2022781556731230996970751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21576336605133130634354677 2022781556731230996970751)
                      ·
                        rfl

theorem cell23_3939353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_3939353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939353 prefixEnd_3939353 := by exact prefixLift 3939353
  have htrace : WordTrace (prefixWord ++ tailWord_3939353) baseStart_3939353 baseEnd_3939353 := by
    simpa [prefixWord, tailWord_3939353, baseEnd_3939353] using wordTrace_append hprefix tailTrace_3939353
  have hstable : (prefixWord ++ tailWord_3939353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939353).length < 2 ^ (prefixWord ++ tailWord_3939353).sum := by decide
  have hdescent : baseEnd_3939353 < baseStart_3939353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939374 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3939374 : Nat := 118140960795 + 3939374 * 2 ^ 59
def prefixEnd_3939374 : Nat := 4983230072969 + 3 ^ 40 * 3939374 * 2
def baseEnd_3939374 : Nat := 2022792339824975414808155

theorem tailTrace_3939374 : CollatzResearch.WordTrace tailWord_3939374 prefixEnd_3939374 2022792339824975414808155 := by
  unfold tailWord_3939374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960096703791033045080147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95787182420218842907094117 17960096703791033045080147)
  ·
    refine ⟨26940145055686549567620221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960096703791033045080147 26940145055686549567620221)
    ·
      refine ⟨10102554395882456087857583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26940145055686549567620221 10102554395882456087857583)
      ·
        refine ⟨15153831593823684131786375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10102554395882456087857583 15153831593823684131786375)
        ·
          refine ⟨22730747390735526197679563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15153831593823684131786375 22730747390735526197679563)
          ·
            refine ⟨34096121086103289296519345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22730747390735526197679563 34096121086103289296519345)
            ·
              refine ⟨25572090814577466972389509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34096121086103289296519345 25572090814577466972389509)
              ·
                refine ⟨4794767027733275057323033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25572090814577466972389509 4794767027733275057323033)
                ·
                  refine ⟨3596075270799956292992275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4794767027733275057323033 3596075270799956292992275)
                  ·
                    refine ⟨5394112906199934439488413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3596075270799956292992275 5394112906199934439488413)
                    ·
                      refine ⟨2022792339824975414808155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5394112906199934439488413 2022792339824975414808155)
                      ·
                        rfl

theorem cell23_3939374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3939374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939374 prefixEnd_3939374 := by exact prefixLift 3939374
  have htrace : WordTrace (prefixWord ++ tailWord_3939374) baseStart_3939374 baseEnd_3939374 := by
    simpa [prefixWord, tailWord_3939374, baseEnd_3939374] using wordTrace_append hprefix tailTrace_3939374
  have hstable : (prefixWord ++ tailWord_3939374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939374).length < 2 ^ (prefixWord ++ tailWord_3939374).sum := by decide
  have hdescent : baseEnd_3939374 < baseStart_3939374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939383 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_3939383 : Nat := 118140960795 + 3939383 * 2 ^ 59
def prefixEnd_3939383 : Nat := 4983230072969 + 3 ^ 40 * 3939383 * 2
def baseEnd_3939383 : Nat := 2022796961150865879595613

theorem tailTrace_3939383 : CollatzResearch.WordTrace tailWord_3939383 prefixEnd_3939383 2022796961150865879595613 := by
  unfold tailWord_3939383
  simp only [CollatzResearch.WordTrace]
  refine ⟨143681101887295658897718803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95787401258197105931812535 143681101887295658897718803)
  ·
    refine ⟨215521652830943488346578205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143681101887295658897718803 215521652830943488346578205)
    ·
      refine ⟨80820619811603808129966827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215521652830943488346578205 80820619811603808129966827)
      ·
        refine ⟨121230929717405712194950241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80820619811603808129966827 121230929717405712194950241)
        ·
          refine ⟨90923197288054284146212681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121230929717405712194950241 90923197288054284146212681)
          ·
            refine ⟨68192397966040713109659511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90923197288054284146212681 68192397966040713109659511)
            ·
              refine ⟨102288596949061069664489267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68192397966040713109659511 102288596949061069664489267)
              ·
                refine ⟨153432895423591604496733901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102288596949061069664489267 153432895423591604496733901)
                ·
                  refine ⟨57537335783846851686275213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153432895423591604496733901 57537335783846851686275213)
                  ·
                    refine ⟨21576500918942569382353205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57537335783846851686275213 21576500918942569382353205)
                    ·
                      refine ⟨2022796961150865879595613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21576500918942569382353205 2022796961150865879595613)
                      ·
                        rfl

theorem cell23_3939383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_3939383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939383 prefixEnd_3939383 := by exact prefixLift 3939383
  have htrace : WordTrace (prefixWord ++ tailWord_3939383) baseStart_3939383 baseEnd_3939383 := by
    simpa [prefixWord, tailWord_3939383, baseEnd_3939383] using wordTrace_append hprefix tailTrace_3939383
  have hstable : (prefixWord ++ tailWord_3939383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939383).length < 2 ^ (prefixWord ++ tailWord_3939383).sum := by decide
  have hdescent : baseEnd_3939383 < baseStart_3939383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939431 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_3939431 : Nat := 118140960795 + 3939431 * 2 ^ 59
def prefixEnd_3939431 : Nat := 4983230072969 + 3 ^ 40 * 3939431 * 2
def baseEnd_3939431 : Nat := 2022821608222281691795393

theorem tailTrace_3939431 : CollatzResearch.WordTrace tailWord_3939431 prefixEnd_3939431 2022821608222281691795393 := by
  unfold tailWord_3939431
  simp only [CollatzResearch.WordTrace]
  refine ⟨143682852591121763095466147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95788568394081175396977431 143682852591121763095466147)
  ·
    refine ⟨215524278886682644643199221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143682852591121763095466147 215524278886682644643199221)
    ·
      refine ⟨20205401145626497935299927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215524278886682644643199221 20205401145626497935299927)
      ·
        refine ⟨30308101718439746902949891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20205401145626497935299927 30308101718439746902949891)
        ·
          refine ⟨45462152577659620354424837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30308101718439746902949891 45462152577659620354424837)
          ·
            refine ⟨8524153608311178816454657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45462152577659620354424837 8524153608311178816454657)
            ·
              refine ⟨6393115206233384112340993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8524153608311178816454657 6393115206233384112340993)
              ·
                refine ⟨4794836404675038084255745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6393115206233384112340993 4794836404675038084255745)
                ·
                  refine ⟨3596127303506278563191809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4794836404675038084255745 3596127303506278563191809)
                  ·
                    refine ⟨2697095477629708922393857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3596127303506278563191809 2697095477629708922393857)
                    ·
                      refine ⟨2022821608222281691795393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697095477629708922393857 2022821608222281691795393)
                      ·
                        rfl

theorem cell23_3939431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_3939431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939431 prefixEnd_3939431 := by exact prefixLift 3939431
  have htrace : WordTrace (prefixWord ++ tailWord_3939431) baseStart_3939431 baseEnd_3939431 := by
    simpa [prefixWord, tailWord_3939431, baseEnd_3939431] using wordTrace_append hprefix tailTrace_3939431
  have hstable : (prefixWord ++ tailWord_3939431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939431).length < 2 ^ (prefixWord ++ tailWord_3939431).sum := by decide
  have hdescent : baseEnd_3939431 < baseStart_3939431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939577 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_3939577 : Nat := 118140960795 + 3939577 * 2 ^ 59
def prefixEnd_3939577 : Nat := 4983230072969 + 3 ^ 40 * 3939577 * 2
def baseEnd_3939577 : Nat := 2022896576397838120569721

theorem tailTrace_3939577 : CollatzResearch.WordTrace tailWord_3939577 prefixEnd_3939577 2022896576397838120569721 := by
  unfold tailWord_3939577
  simp only [CollatzResearch.WordTrace]
  refine ⟨143688177648592830030280985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95792118432395220020187323 143688177648592830030280985)
  ·
    refine ⟨107766133236444622522710739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143688177648592830030280985 107766133236444622522710739)
    ·
      refine ⟨161649199854666933784066109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107766133236444622522710739 161649199854666933784066109)
      ·
        refine ⟨60618449945500100169024791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161649199854666933784066109 60618449945500100169024791)
        ·
          refine ⟨90927674918250150253537187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60618449945500100169024791 90927674918250150253537187)
          ·
            refine ⟨136391512377375225380305781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90927674918250150253537187 136391512377375225380305781)
            ·
              refine ⟨12786704285378927379403667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136391512377375225380305781 12786704285378927379403667)
              ·
                refine ⟨19180056428068391069105501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12786704285378927379403667 19180056428068391069105501)
                ·
                  refine ⟨7192521160525646650914563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19180056428068391069105501 7192521160525646650914563)
                  ·
                    refine ⟨10788781740788469976371845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7192521160525646650914563 10788781740788469976371845)
                    ·
                      refine ⟨2022896576397838120569721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10788781740788469976371845 2022896576397838120569721)
                      ·
                        rfl

theorem cell23_3939577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_3939577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939577 prefixEnd_3939577 := by exact prefixLift 3939577
  have htrace : WordTrace (prefixWord ++ tailWord_3939577) baseStart_3939577 baseEnd_3939577 := by
    simpa [prefixWord, tailWord_3939577, baseEnd_3939577] using wordTrace_append hprefix tailTrace_3939577
  have hstable : (prefixWord ++ tailWord_3939577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939577).length < 2 ^ (prefixWord ++ tailWord_3939577).sum := by decide
  have hdescent : baseEnd_3939577 < baseStart_3939577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939587 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 1, 6]
def baseStart_3939587 : Nat := 118140960795 + 3939587 * 2 ^ 59
def prefixEnd_3939587 : Nat := 4983230072969 + 3 ^ 40 * 3939587 * 2
def baseEnd_3939587 : Nat := 674300570401461027148225

theorem tailTrace_3939587 : CollatzResearch.WordTrace tailWord_3939587 prefixEnd_3939587 674300570401461027148225 := by
  unfold tailWord_3939587
  simp only [CollatzResearch.WordTrace]
  refine ⟨143688542378556601738145015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95792361585704401158763343 143688542378556601738145015)
  ·
    refine ⟨215532813567834902607217523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143688542378556601738145015 215532813567834902607217523)
    ·
      refine ⟨323299220351752353910826285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215532813567834902607217523 323299220351752353910826285)
      ·
        refine ⟨121237207631907132716559857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323299220351752353910826285 121237207631907132716559857)
        ·
          refine ⟨90927905723930349537419893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121237207631907132716559857 90927905723930349537419893)
          ·
            refine ⟨8524491161618470269133115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90927905723930349537419893 8524491161618470269133115)
            ·
              refine ⟨12786736742427705403699673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524491161618470269133115 12786736742427705403699673)
              ·
                refine ⟨9590052556820779052774755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12786736742427705403699673 9590052556820779052774755)
                ·
                  refine ⟨14385078835231168579162133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590052556820779052774755 14385078835231168579162133)
                  ·
                    refine ⟨674300570401461027148225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14385078835231168579162133 674300570401461027148225)
                    ·
                      rfl

theorem cell23_3939587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 6].length) (baseStart_3939587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939587 prefixEnd_3939587 := by exact prefixLift 3939587
  have htrace : WordTrace (prefixWord ++ tailWord_3939587) baseStart_3939587 baseEnd_3939587 := by
    simpa [prefixWord, tailWord_3939587, baseEnd_3939587] using wordTrace_append hprefix tailTrace_3939587
  have hstable : (prefixWord ++ tailWord_3939587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939587).length < 2 ^ (prefixWord ++ tailWord_3939587).sum := by decide
  have hdescent : baseEnd_3939587 < baseStart_3939587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939607 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3939607 : Nat := 118140960795 + 3939607 * 2 ^ 59
def prefixEnd_3939607 : Nat := 4983230072969 + 3 ^ 40 * 3939607 * 2
def baseEnd_3939607 : Nat := 2022911980817473003194583

theorem tailTrace_3939607 : CollatzResearch.WordTrace tailWord_3939607 prefixEnd_3939607 2022911980817473003194583 := by
  unfold tailWord_3939607
  simp only [CollatzResearch.WordTrace]
  refine ⟨143689271838484145153873075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95792847892322763435915383 143689271838484145153873075)
  ·
    refine ⟨215533907757726217730809613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143689271838484145153873075 215533907757726217730809613)
    ·
      refine ⟨80825215409147331649053605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215533907757726217730809613 80825215409147331649053605)
      ·
        refine ⟨15154727889215124684197551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80825215409147331649053605 15154727889215124684197551)
        ·
          refine ⟨22732091833822687026296327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154727889215124684197551 22732091833822687026296327)
          ·
            refine ⟨34098137750734030539444491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22732091833822687026296327 34098137750734030539444491)
            ·
              refine ⟨51147206626101045809166737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34098137750734030539444491 51147206626101045809166737)
              ·
                refine ⟨38360404969575784356875053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51147206626101045809166737 38360404969575784356875053)
                ·
                  refine ⟨14385151863590919133828145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38360404969575784356875053 14385151863590919133828145)
                  ·
                    refine ⟨10788863897693189350371109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14385151863590919133828145 10788863897693189350371109)
                    ·
                      refine ⟨2022911980817473003194583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10788863897693189350371109 2022911980817473003194583)
                      ·
                        rfl

theorem cell23_3939607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3939607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939607 prefixEnd_3939607 := by exact prefixLift 3939607
  have htrace : WordTrace (prefixWord ++ tailWord_3939607) baseStart_3939607 baseEnd_3939607 := by
    simpa [prefixWord, tailWord_3939607, baseEnd_3939607] using wordTrace_append hprefix tailTrace_3939607
  have hstable : (prefixWord ++ tailWord_3939607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939607).length < 2 ^ (prefixWord ++ tailWord_3939607).sum := by decide
  have hdescent : baseEnd_3939607 < baseStart_3939607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939624 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3939624 : Nat := 118140960795 + 3939624 * 2 ^ 59
def prefixEnd_3939624 : Nat := 4983230072969 + 3 ^ 40 * 3939624 * 2
def baseEnd_3939624 : Nat := 2022920709988599436682005

theorem tailTrace_3939624 : CollatzResearch.WordTrace tailWord_3939624 prefixEnd_3939624 2022920709988599436682005 := by
  unfold tailWord_3939624
  simp only [CollatzResearch.WordTrace]
  refine ⟨71844945939711278528620963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95793261252948371371494617 71844945939711278528620963)
  ·
    refine ⟨107767418909566917792931445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71844945939711278528620963 107767418909566917792931445)
    ·
      refine ⟨10103195522771898543087323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107767418909566917792931445 10103195522771898543087323)
      ·
        refine ⟨15154793284157847814630985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103195522771898543087323 15154793284157847814630985)
        ·
          refine ⟨11366094963118385860973239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15154793284157847814630985 11366094963118385860973239)
          ·
            refine ⟨17049142444677578791459859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366094963118385860973239 17049142444677578791459859)
            ·
              refine ⟨25573713667016368187189789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17049142444677578791459859 25573713667016368187189789)
              ·
                refine ⟨9590142625131138070196171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25573713667016368187189789 9590142625131138070196171)
                ·
                  refine ⟨14385213937696707105294257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590142625131138070196171 14385213937696707105294257)
                  ·
                    refine ⟨10788910453272530328970693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14385213937696707105294257 10788910453272530328970693)
                    ·
                      refine ⟨2022920709988599436682005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10788910453272530328970693 2022920709988599436682005)
                      ·
                        rfl

theorem cell23_3939624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3939624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939624 prefixEnd_3939624 := by exact prefixLift 3939624
  have htrace : WordTrace (prefixWord ++ tailWord_3939624) baseStart_3939624 baseEnd_3939624 := by
    simpa [prefixWord, tailWord_3939624, baseEnd_3939624] using wordTrace_append hprefix tailTrace_3939624
  have hstable : (prefixWord ++ tailWord_3939624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939624).length < 2 ^ (prefixWord ++ tailWord_3939624).sum := by decide
  have hdescent : baseEnd_3939624 < baseStart_3939624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939634 : List Nat := [3, 2, 1, 1, 4, 2, 3, 7]
def baseStart_3939634 : Nat := 118140960795 + 3939634 * 2 ^ 59
def prefixEnd_3939634 : Nat := 4983230072969 + 3 ^ 40 * 3939634 * 2
def baseEnd_3939634 : Nat := 74923179436857199909517

theorem tailTrace_3939634 : CollatzResearch.WordTrace tailWord_3939634 prefixEnd_3939634 74923179436857199909517 := by
  unfold tailWord_3939634
  simp only [CollatzResearch.WordTrace]
  refine ⟨35922564152346582191276489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95793504406257552510070637 35922564152346582191276489)
  ·
    refine ⟨26941923114259936643457367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35922564152346582191276489 26941923114259936643457367)
    ·
      refine ⟨40412884671389904965186051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26941923114259936643457367 40412884671389904965186051)
      ·
        refine ⟨60619327007084857447779077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40412884671389904965186051 60619327007084857447779077)
        ·
          refine ⟨11366123813828410771458577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60619327007084857447779077 11366123813828410771458577)
          ·
            refine ⟨8524592860371308078593933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11366123813828410771458577 8524592860371308078593933)
            ·
              refine ⟨3196722322639240529472725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8524592860371308078593933 3196722322639240529472725)
              ·
                refine ⟨74923179436857199909517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3196722322639240529472725 74923179436857199909517)
                ·
                  rfl

theorem cell23_3939634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 7].length) (baseStart_3939634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939634 prefixEnd_3939634 := by exact prefixLift 3939634
  have htrace : WordTrace (prefixWord ++ tailWord_3939634) baseStart_3939634 baseEnd_3939634 := by
    simpa [prefixWord, tailWord_3939634, baseEnd_3939634] using wordTrace_append hprefix tailTrace_3939634
  have hstable : (prefixWord ++ tailWord_3939634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939634).length < 2 ^ (prefixWord ++ tailWord_3939634).sum := by decide
  have hdescent : baseEnd_3939634 < baseStart_3939634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939644 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3939644 : Nat := 118140960795 + 3939644 * 2 ^ 59
def prefixEnd_3939644 : Nat := 4983230072969 + 3 ^ 40 * 3939644 * 2
def baseEnd_3939644 : Nat := 2022930979601689358431913

theorem tailTrace_3939644 : CollatzResearch.WordTrace tailWord_3939644 prefixEnd_3939644 2022930979601689358431913 := by
  unfold tailWord_3939644
  simp only [CollatzResearch.WordTrace]
  refine ⟨71845310669675050236484993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95793747559566733648646657 71845310669675050236484993)
  ·
    refine ⟨53883983002256287677363745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71845310669675050236484993 53883983002256287677363745)
    ·
      refine ⟨40412987251692215758022809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53883983002256287677363745 40412987251692215758022809)
      ·
        refine ⟨30309740438769161818517107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40412987251692215758022809 30309740438769161818517107)
        ·
          refine ⟨45464610658153742727775661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30309740438769161818517107 45464610658153742727775661)
          ·
            refine ⟨17049228996807653522915873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45464610658153742727775661 17049228996807653522915873)
            ·
              refine ⟨12786921747605740142186905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17049228996807653522915873 12786921747605740142186905)
              ·
                refine ⟨9590191310704305106640179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12786921747605740142186905 9590191310704305106640179)
                ·
                  refine ⟨14385286966056457659960269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590191310704305106640179 14385286966056457659960269)
                  ·
                    refine ⟨5394482612271171622485101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14385286966056457659960269 5394482612271171622485101)
                    ·
                      refine ⟨2022930979601689358431913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5394482612271171622485101 2022930979601689358431913)
                      ·
                        rfl

theorem cell23_3939644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3939644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939644 prefixEnd_3939644 := by exact prefixLift 3939644
  have htrace : WordTrace (prefixWord ++ tailWord_3939644) baseStart_3939644 baseEnd_3939644 := by
    simpa [prefixWord, tailWord_3939644, baseEnd_3939644] using wordTrace_append hprefix tailTrace_3939644
  have hstable : (prefixWord ++ tailWord_3939644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939644).length < 2 ^ (prefixWord ++ tailWord_3939644).sum := by decide
  have hdescent : baseEnd_3939644 < baseStart_3939644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939645 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3939645 : Nat := 118140960795 + 3939645 * 2 ^ 59
def prefixEnd_3939645 : Nat := 4983230072969 + 3 ^ 40 * 3939645 * 2
def baseEnd_3939645 : Nat := 2022931493082343854519409

theorem tailTrace_3939645 : CollatzResearch.WordTrace tailWord_3939645 prefixEnd_3939645 2022931493082343854519409 := by
  unfold tailWord_3939645
  simp only [CollatzResearch.WordTrace]
  refine ⟨143690657812346477643756389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95793771874897651762504259 143690657812346477643756389)
  ·
    refine ⟨26941998339814964558204323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143690657812346477643756389 26941998339814964558204323)
    ·
      refine ⟨40412997509722446837306485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26941998339814964558204323 40412997509722446837306485)
      ·
        refine ⟨3788718516536479390997483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40412997509722446837306485 3788718516536479390997483)
        ·
          refine ⟨5683077774804719086496225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788718516536479390997483 5683077774804719086496225)
          ·
            refine ⟨4262308331103539314872169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5683077774804719086496225 4262308331103539314872169)
            ·
              refine ⟨3196731248327654486154127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4262308331103539314872169 3196731248327654486154127)
              ·
                refine ⟨4795096872491481729231191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196731248327654486154127 4795096872491481729231191)
                ·
                  refine ⟨7192645308737222593846787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795096872491481729231191 7192645308737222593846787)
                  ·
                    refine ⟨10788967963105833890770181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7192645308737222593846787 10788967963105833890770181)
                    ·
                      refine ⟨2022931493082343854519409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10788967963105833890770181 2022931493082343854519409)
                      ·
                        rfl

theorem cell23_3939645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3939645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939645 prefixEnd_3939645 := by exact prefixLift 3939645
  have htrace : WordTrace (prefixWord ++ tailWord_3939645) baseStart_3939645 baseEnd_3939645 := by
    simpa [prefixWord, tailWord_3939645, baseEnd_3939645] using wordTrace_append hprefix tailTrace_3939645
  have hstable : (prefixWord ++ tailWord_3939645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939645).length < 2 ^ (prefixWord ++ tailWord_3939645).sum := by decide
  have hdescent : baseEnd_3939645 < baseStart_3939645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939697 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_3939697 : Nat := 118140960795 + 3939697 * 2 ^ 59
def prefixEnd_3939697 : Nat := 4983230072969 + 3 ^ 40 * 3939697 * 2
def baseEnd_3939697 : Nat := 2022958194076377651069169

theorem tailTrace_3939697 : CollatzResearch.WordTrace tailWord_3939697 prefixEnd_3939697 2022958194076377651069169 := by
  unfold tailWord_3939697
  simp only [CollatzResearch.WordTrace]
  refine ⟨143692554408158090524649345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95795036272105393683099563 143692554408158090524649345)
  ·
    refine ⟨107769415806118567893487009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143692554408158090524649345 107769415806118567893487009)
    ·
      refine ⟨80827061854588925920115257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107769415806118567893487009 80827061854588925920115257)
      ·
        refine ⟨60620296390941694440086443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80827061854588925920115257 60620296390941694440086443)
        ·
          refine ⟨90930444586412541660129665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60620296390941694440086443 90930444586412541660129665)
          ·
            refine ⟨68197833439809406245097249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90930444586412541660129665 68197833439809406245097249)
            ·
              refine ⟨51148375079857054683822937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68197833439809406245097249 51148375079857054683822937)
              ·
                refine ⟨38361281309892791012867203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51148375079857054683822937 38361281309892791012867203)
                ·
                  refine ⟨57541921964839186519300805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38361281309892791012867203 57541921964839186519300805)
                  ·
                    refine ⟨10789110368407347472368901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57541921964839186519300805 10789110368407347472368901)
                    ·
                      refine ⟨2022958194076377651069169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10789110368407347472368901 2022958194076377651069169)
                      ·
                        rfl

theorem cell23_3939697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_3939697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939697 prefixEnd_3939697 := by exact prefixLift 3939697
  have htrace : WordTrace (prefixWord ++ tailWord_3939697) baseStart_3939697 baseEnd_3939697 := by
    simpa [prefixWord, tailWord_3939697, baseEnd_3939697] using wordTrace_append hprefix tailTrace_3939697
  have hstable : (prefixWord ++ tailWord_3939697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939697).length < 2 ^ (prefixWord ++ tailWord_3939697).sum := by decide
  have hdescent : baseEnd_3939697 < baseStart_3939697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939747 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3939747 : Nat := 118140960795 + 3939747 * 2 ^ 59
def prefixEnd_3939747 : Nat := 4983230072969 + 3 ^ 40 * 3939747 * 2
def baseEnd_3939747 : Nat := 2022983868109102455443939

theorem tailTrace_3939747 : CollatzResearch.WordTrace tailWord_3939747 prefixEnd_3939747 2022983868109102455443939 := by
  unfold tailWord_3939747
  simp only [CollatzResearch.WordTrace]
  refine ⟨143694378057976949063969495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95796252038651299375979663 143694378057976949063969495)
  ·
    refine ⟨215541567086965423595954243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143694378057976949063969495 215541567086965423595954243)
    ·
      refine ⟨323312350630448135393931365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215541567086965423595954243 323312350630448135393931365)
      ·
        refine ⟨60621065743209025386362131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323312350630448135393931365 60621065743209025386362131)
        ·
          refine ⟨90931598614813538079543197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60621065743209025386362131 90931598614813538079543197)
          ·
            refine ⟨34099349480555076779828699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90931598614813538079543197 34099349480555076779828699)
            ·
              refine ⟨51149024220832615169743049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34099349480555076779828699 51149024220832615169743049)
              ·
                refine ⟨38361768165624461377307287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51149024220832615169743049 38361768165624461377307287)
                ·
                  refine ⟨57542652248436692065960931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38361768165624461377307287 57542652248436692065960931)
                  ·
                    refine ⟨86313978372655038098941397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57542652248436692065960931 86313978372655038098941397)
                    ·
                      refine ⟨2022983868109102455443939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86313978372655038098941397 2022983868109102455443939)
                      ·
                        rfl

theorem cell23_3939747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3939747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939747 prefixEnd_3939747 := by exact prefixLift 3939747
  have htrace : WordTrace (prefixWord ++ tailWord_3939747) baseStart_3939747 baseEnd_3939747 := by
    simpa [prefixWord, tailWord_3939747, baseEnd_3939747] using wordTrace_append hprefix tailTrace_3939747
  have hstable : (prefixWord ++ tailWord_3939747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939747).length < 2 ^ (prefixWord ++ tailWord_3939747).sum := by decide
  have hdescent : baseEnd_3939747 < baseStart_3939747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939774 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3939774 : Nat := 118140960795 + 3939774 * 2 ^ 59
def prefixEnd_3939774 : Nat := 4983230072969 + 3 ^ 40 * 3939774 * 2
def baseEnd_3939774 : Nat := 2022997732086773849806315

theorem tailTrace_3939774 : CollatzResearch.WordTrace tailWord_3939774 prefixEnd_3939774 2022997732086773849806315 := by
  unfold tailWord_3939774
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961920353609891584400297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95796908552586088450134917 17961920353609891584400297)
  ·
    refine ⟨13471440265207418688300223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17961920353609891584400297 13471440265207418688300223)
    ·
      refine ⟨20207160397811128032450335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13471440265207418688300223 20207160397811128032450335)
      ·
        refine ⟨30310740596716692048675503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20207160397811128032450335 30310740596716692048675503)
        ·
          refine ⟨45466110895075038073013255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30310740596716692048675503 45466110895075038073013255)
          ·
            refine ⟨68199166342612557109519883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45466110895075038073013255 68199166342612557109519883)
            ·
              refine ⟨102298749513918835664279825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68199166342612557109519883 102298749513918835664279825)
              ·
                refine ⟨76724062135439126748209869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102298749513918835664279825 76724062135439126748209869)
                ·
                  refine ⟨28771523300789672530578701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76724062135439126748209869 28771523300789672530578701)
                  ·
                    refine ⟨10789321237796127198967013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28771523300789672530578701 10789321237796127198967013)
                    ·
                      refine ⟨2022997732086773849806315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10789321237796127198967013 2022997732086773849806315)
                      ·
                        rfl

theorem cell23_3939774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3939774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939774 prefixEnd_3939774 := by exact prefixLift 3939774
  have htrace : WordTrace (prefixWord ++ tailWord_3939774) baseStart_3939774 baseEnd_3939774 := by
    simpa [prefixWord, tailWord_3939774, baseEnd_3939774] using wordTrace_append hprefix tailTrace_3939774
  have hstable : (prefixWord ++ tailWord_3939774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939774).length < 2 ^ (prefixWord ++ tailWord_3939774).sum := by decide
  have hdescent : baseEnd_3939774 < baseStart_3939774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939801 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 3, 4]
def baseStart_3939801 : Nat := 118140960795 + 3939801 * 2 ^ 59
def prefixEnd_3939801 : Nat := 4983230072969 + 3 ^ 40 * 3939801 * 2
def baseEnd_3939801 : Nat := 674337198688148414722897

theorem tailTrace_3939801 : CollatzResearch.WordTrace tailWord_3939801 prefixEnd_3939801 674337198688148414722897 := by
  unfold tailWord_3939801
  simp only [CollatzResearch.WordTrace]
  refine ⟨143696347599781316286435257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95797565066520877524290171 143696347599781316286435257)
  ·
    refine ⟨107772260699835987214826443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143696347599781316286435257 107772260699835987214826443)
    ·
      refine ⟨161658391049753980822239665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107772260699835987214826443 161658391049753980822239665)
      ·
        refine ⟨121243793287315485616679749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161658391049753980822239665 121243793287315485616679749)
        ·
          refine ⟨22733211241371653553127453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121243793287315485616679749 22733211241371653553127453)
          ·
            refine ⟨8524954215514370082422795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22733211241371653553127453 8524954215514370082422795)
            ·
              refine ⟨12787431323271555123634193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524954215514370082422795 12787431323271555123634193)
              ·
                refine ⟨9590573492453666342725645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12787431323271555123634193 9590573492453666342725645)
                ·
                  refine ⟨3596465059670124878522117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9590573492453666342725645 3596465059670124878522117)
                  ·
                    refine ⟨674337198688148414722897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3596465059670124878522117 674337198688148414722897)
                    ·
                      rfl

theorem cell23_3939801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_3939801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939801 prefixEnd_3939801 := by exact prefixLift 3939801
  have htrace : WordTrace (prefixWord ++ tailWord_3939801) baseStart_3939801 baseEnd_3939801 := by
    simpa [prefixWord, tailWord_3939801, baseEnd_3939801] using wordTrace_append hprefix tailTrace_3939801
  have hstable : (prefixWord ++ tailWord_3939801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939801).length < 2 ^ (prefixWord ++ tailWord_3939801).sum := by decide
  have hdescent : baseEnd_3939801 < baseStart_3939801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939811 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3939811 : Nat := 118140960795 + 3939811 * 2 ^ 59
def prefixEnd_3939811 : Nat := 4983230072969 + 3 ^ 40 * 3939811 * 2
def baseEnd_3939811 : Nat := 2023016730870990205043645

theorem tailTrace_3939811 : CollatzResearch.WordTrace tailWord_3939811 prefixEnd_3939811 2023016730870990205043645 := by
  unfold tailWord_3939811
  simp only [CollatzResearch.WordTrace]
  refine ⟨143696712329745087994299287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95797808219830058662866191 143696712329745087994299287)
  ·
    refine ⟨215545068494617631991448931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143696712329745087994299287 215545068494617631991448931)
    ·
      refine ⟨323317602741926447987173397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215545068494617631991448931 323317602741926447987173397)
      ·
        refine ⟨15155512628527802249398753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323317602741926447987173397 15155512628527802249398753)
        ·
          refine ⟨11366634471395851687049065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15155512628527802249398753 11366634471395851687049065)
          ·
            refine ⟨8524975853546888765286799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11366634471395851687049065 8524975853546888765286799)
            ·
              refine ⟨12787463780320333147930199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524975853546888765286799 12787463780320333147930199)
              ·
                refine ⟨19181195670480499721895299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12787463780320333147930199 19181195670480499721895299)
                ·
                  refine ⟨28771793505720749582842949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19181195670480499721895299 28771793505720749582842949)
                  ·
                    refine ⟨5394711282322640546783053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28771793505720749582842949 5394711282322640546783053)
                    ·
                      refine ⟨2023016730870990205043645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5394711282322640546783053 2023016730870990205043645)
                      ·
                        rfl

theorem cell23_3939811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3939811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939811 prefixEnd_3939811 := by exact prefixLift 3939811
  have htrace : WordTrace (prefixWord ++ tailWord_3939811) baseStart_3939811 baseEnd_3939811 := by
    simpa [prefixWord, tailWord_3939811, baseEnd_3939811] using wordTrace_append hprefix tailTrace_3939811
  have hstable : (prefixWord ++ tailWord_3939811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939811).length < 2 ^ (prefixWord ++ tailWord_3939811).sum := by decide
  have hdescent : baseEnd_3939811 < baseStart_3939811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939861 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3939861 : Nat := 118140960795 + 3939861 * 2 ^ 59
def prefixEnd_3939861 : Nat := 4983230072969 + 3 ^ 40 * 3939861 * 2
def baseEnd_3939861 : Nat := 674347468301238336472805

theorem tailTrace_3939861 : CollatzResearch.WordTrace tailWord_3939861 prefixEnd_3939861 674347468301238336472805 := by
  unfold tailWord_3939861
  simp only [CollatzResearch.WordTrace]
  refine ⟨143698535979563946533619437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95799023986375964355746291 143698535979563946533619437)
  ·
    refine ⟨53886950992336479950107289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143698535979563946533619437 53886950992336479950107289)
    ·
      refine ⟨40415213244252359962580467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53886950992336479950107289 40415213244252359962580467)
      ·
        refine ⟨60622819866378539943870701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40415213244252359962580467 60622819866378539943870701)
        ·
          refine ⟨22733557449891952478951513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60622819866378539943870701 22733557449891952478951513)
          ·
            refine ⟨17050168087418964359213635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22733557449891952478951513 17050168087418964359213635)
            ·
              refine ⟨25575252131128446538820453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17050168087418964359213635 25575252131128446538820453)
              ·
                refine ⟨4795359774586583726028835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25575252131128446538820453 4795359774586583726028835)
                ·
                  refine ⟨7193039661879875589043253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795359774586583726028835 7193039661879875589043253)
                  ·
                    refine ⟨674347468301238336472805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7193039661879875589043253 674347468301238336472805)
                    ·
                      rfl

theorem cell23_3939861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3939861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939861 prefixEnd_3939861 := by exact prefixLift 3939861
  have htrace : WordTrace (prefixWord ++ tailWord_3939861) baseStart_3939861 baseEnd_3939861 := by
    simpa [prefixWord, tailWord_3939861, baseEnd_3939861] using wordTrace_append hprefix tailTrace_3939861
  have hstable : (prefixWord ++ tailWord_3939861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939861).length < 2 ^ (prefixWord ++ tailWord_3939861).sum := by decide
  have hdescent : baseEnd_3939861 < baseStart_3939861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939868 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_3939868 : Nat := 118140960795 + 3939868 * 2 ^ 59
def prefixEnd_3939868 : Nat := 4983230072969 + 3 ^ 40 * 3939868 * 2
def baseEnd_3939868 : Nat := 2023045999268296482030883

theorem tailTrace_3939868 : CollatzResearch.WordTrace tailWord_3939868 prefixEnd_3939868 2023045999268296482030883 := by
  unfold tailWord_3939868
  simp only [CollatzResearch.WordTrace]
  refine ⟨71849395645269293364562129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95799194193692391152749505 71849395645269293364562129)
  ·
    refine ⟨53887046733951970023421597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71849395645269293364562129 53887046733951970023421597)
    ·
      refine ⟨20207642525231988758783099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53887046733951970023421597 20207642525231988758783099)
      ·
        refine ⟨30311463787847983138174649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20207642525231988758783099 30311463787847983138174649)
        ·
          refine ⟨22733597840885987353630987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30311463787847983138174649 22733597840885987353630987)
          ·
            refine ⟨34100396761328981030446481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22733597840885987353630987 34100396761328981030446481)
            ·
              refine ⟨25575297570996735772834861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34100396761328981030446481 25575297570996735772834861)
              ·
                refine ⟨9590736589123775914813073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25575297570996735772834861 9590736589123775914813073)
                ·
                  refine ⟨7193052441842831936109805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9590736589123775914813073 7193052441842831936109805)
                  ·
                    refine ⟨2697394665691061976041177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7193052441842831936109805 2697394665691061976041177)
                    ·
                      refine ⟨2023045999268296482030883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697394665691061976041177 2023045999268296482030883)
                      ·
                        rfl

theorem cell23_3939868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_3939868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939868 prefixEnd_3939868 := by exact prefixLift 3939868
  have htrace : WordTrace (prefixWord ++ tailWord_3939868) baseStart_3939868 baseEnd_3939868 := by
    simpa [prefixWord, tailWord_3939868, baseEnd_3939868] using wordTrace_append hprefix tailTrace_3939868
  have hstable : (prefixWord ++ tailWord_3939868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939868).length < 2 ^ (prefixWord ++ tailWord_3939868).sum := by decide
  have hdescent : baseEnd_3939868 < baseStart_3939868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939891 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 4, 4]
def baseStart_3939891 : Nat := 118140960795 + 3939891 * 2 ^ 59
def prefixEnd_3939891 : Nat := 4983230072969 + 3 ^ 40 * 3939891 * 2
def baseEnd_3939891 : Nat := 674352603107783297347759

theorem tailTrace_3939891 : CollatzResearch.WordTrace tailWord_3939891 prefixEnd_3939891 674352603107783297347759 := by
  unfold tailWord_3939891
  simp only [CollatzResearch.WordTrace]
  refine ⟨143699630169455261657211527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95799753446303507771474351 143699630169455261657211527)
  ·
    refine ⟨215549445254182892485817291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143699630169455261657211527 215549445254182892485817291)
    ·
      refine ⟨323324167881274338728725937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215549445254182892485817291 323324167881274338728725937)
      ·
        refine ⟨242493125910955754046544453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323324167881274338728725937 242493125910955754046544453)
        ·
          refine ⟨45467461108304203883727085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242493125910955754046544453 45467461108304203883727085)
          ·
            refine ⟨17050297915614076456397657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45467461108304203883727085 17050297915614076456397657)
            ·
              refine ⟨12787723436710557342298243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17050297915614076456397657 12787723436710557342298243)
              ·
                refine ⟨19181585155065836013447365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12787723436710557342298243 19181585155065836013447365)
                ·
                  refine ⟨3596547216574844252521381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19181585155065836013447365 3596547216574844252521381)
                  ·
                    refine ⟨674352603107783297347759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3596547216574844252521381 674352603107783297347759)
                    ·
                      rfl

theorem cell23_3939891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 4].length) (baseStart_3939891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939891 prefixEnd_3939891 := by exact prefixLift 3939891
  have htrace : WordTrace (prefixWord ++ tailWord_3939891) baseStart_3939891 baseEnd_3939891 := by
    simpa [prefixWord, tailWord_3939891, baseEnd_3939891] using wordTrace_append hprefix tailTrace_3939891
  have hstable : (prefixWord ++ tailWord_3939891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939891).length < 2 ^ (prefixWord ++ tailWord_3939891).sum := by decide
  have hdescent : baseEnd_3939891 < baseStart_3939891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939949 : List Nat := [1, 5, 1, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_3939949 : Nat := 118140960795 + 3939949 * 2 ^ 59
def prefixEnd_3939949 : Nat := 4983230072969 + 3 ^ 40 * 3939949 * 2
def baseEnd_3939949 : Nat := 2023087591201310665118011

theorem tailTrace_3939949 : CollatzResearch.WordTrace tailWord_3939949 prefixEnd_3939949 2023087591201310665118011 := by
  unfold tailWord_3939949
  simp only [CollatzResearch.WordTrace]
  refine ⟨143701745603245137562822901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95801163735496758375215267 143701745603245137562822901)
  ·
    refine ⟨13472038650304231646514647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143701745603245137562822901 13472038650304231646514647)
    ·
      refine ⟨20208057975456347469771971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13472038650304231646514647 20208057975456347469771971)
      ·
        refine ⟨30312086963184521204657957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20208057975456347469771971 30312086963184521204657957)
        ·
          refine ⟨5683516305597097725873367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30312086963184521204657957 5683516305597097725873367)
          ·
            refine ⟨8525274458395646588810051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683516305597097725873367 8525274458395646588810051)
            ·
              refine ⟨12787911687593469883215077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8525274458395646588810051 12787911687593469883215077)
              ·
                refine ⟨2397733441423775603102827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12787911687593469883215077 2397733441423775603102827)
                ·
                  refine ⟨3596600162135663404654241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397733441423775603102827 3596600162135663404654241)
                  ·
                    refine ⟨2697450121601747553490681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3596600162135663404654241 2697450121601747553490681)
                    ·
                      refine ⟨2023087591201310665118011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697450121601747553490681 2023087591201310665118011)
                      ·
                        rfl

theorem cell23_3939949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_3939949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939949 prefixEnd_3939949 := by exact prefixLift 3939949
  have htrace : WordTrace (prefixWord ++ tailWord_3939949) baseStart_3939949 baseEnd_3939949 := by
    simpa [prefixWord, tailWord_3939949, baseEnd_3939949] using wordTrace_append hprefix tailTrace_3939949
  have hstable : (prefixWord ++ tailWord_3939949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939949).length < 2 ^ (prefixWord ++ tailWord_3939949).sum := by decide
  have hdescent : baseEnd_3939949 < baseStart_3939949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939965 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_3939965 : Nat := 118140960795 + 3939965 * 2 ^ 59
def prefixEnd_3939965 : Nat := 4983230072969 + 3 ^ 40 * 3939965 * 2
def baseEnd_3939965 : Nat := 2023095806891782602517937

theorem tailTrace_3939965 : CollatzResearch.WordTrace tailWord_3939965 prefixEnd_3939965 2023095806891782602517937 := by
  unfold tailWord_3939965
  simp only [CollatzResearch.WordTrace]
  refine ⟨143702329171187172295405349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95801552780791448196936899 143702329171187172295405349)
  ·
    refine ⟨26944186719597594805388503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143702329171187172295405349 26944186719597594805388503)
    ·
      refine ⟨40416280079396392208082755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26944186719597594805388503 40416280079396392208082755)
      ·
        refine ⟨60624420119094588312124133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40416280079396392208082755 60624420119094588312124133)
        ·
          refine ⟨11367078772330235308523275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60624420119094588312124133 11367078772330235308523275)
          ·
            refine ⟨17050618158495352962784913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367078772330235308523275 17050618158495352962784913)
            ·
              refine ⟨12787963618871514722088685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17050618158495352962784913 12787963618871514722088685)
              ·
                refine ⟨4795486357076818020783257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12787963618871514722088685 4795486357076818020783257)
                ·
                  refine ⟨3596614767807613515587443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795486357076818020783257 3596614767807613515587443)
                  ·
                    refine ⟨5394922151711420273381165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3596614767807613515587443 5394922151711420273381165)
                    ·
                      refine ⟨2023095806891782602517937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5394922151711420273381165 2023095806891782602517937)
                      ·
                        rfl

theorem cell23_3939965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_3939965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939965 prefixEnd_3939965 := by exact prefixLift 3939965
  have htrace : WordTrace (prefixWord ++ tailWord_3939965) baseStart_3939965 baseEnd_3939965 := by
    simpa [prefixWord, tailWord_3939965, baseEnd_3939965] using wordTrace_append hprefix tailTrace_3939965
  have hstable : (prefixWord ++ tailWord_3939965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939965).length < 2 ^ (prefixWord ++ tailWord_3939965).sum := by decide
  have hdescent : baseEnd_3939965 < baseStart_3939965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939992 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 1, 3, 2]
def baseStart_3939992 : Nat := 118140960795 + 3939992 * 2 ^ 59
def prefixEnd_3939992 : Nat := 4983230072969 + 3 ^ 40 * 3939992 * 2
def baseEnd_3939992 : Nat := 2023109670869453996880313

theorem tailTrace_3939992 : CollatzResearch.WordTrace tailWord_3939992 prefixEnd_3939992 2023109670869453996880313 := by
  unfold tailWord_3939992
  simp only [CollatzResearch.WordTrace]
  refine ⟨71851656971044677953319115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95802209294726237271092153 71851656971044677953319115)
  ·
    refine ⟨107777485456567016929978673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71851656971044677953319115 107777485456567016929978673)
    ·
      refine ⟨80833114092425262697484005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107777485456567016929978673 80833114092425262697484005)
      ·
        refine ⟨15156208892329736755778251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80833114092425262697484005 15156208892329736755778251)
        ·
          refine ⟨22734313338494605133667377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156208892329736755778251 22734313338494605133667377)
          ·
            refine ⟨17050735003870953850250533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22734313338494605133667377 17050735003870953850250533)
            ·
              refine ⟨3197012813225803846921975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17050735003870953850250533 3197012813225803846921975)
              ·
                refine ⟨4795519219838705770382963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197012813225803846921975 4795519219838705770382963)
                ·
                  refine ⟨7193278829758058655574445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795519219838705770382963 7193278829758058655574445)
                  ·
                    refine ⟨2697479561159271995840417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7193278829758058655574445 2697479561159271995840417)
                    ·
                      refine ⟨2023109670869453996880313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697479561159271995840417 2023109670869453996880313)
                      ·
                        rfl

theorem cell23_3939992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_3939992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939992 prefixEnd_3939992 := by exact prefixLift 3939992
  have htrace : WordTrace (prefixWord ++ tailWord_3939992) baseStart_3939992 baseEnd_3939992 := by
    simpa [prefixWord, tailWord_3939992, baseEnd_3939992] using wordTrace_append hprefix tailTrace_3939992
  have hstable : (prefixWord ++ tailWord_3939992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939992).length < 2 ^ (prefixWord ++ tailWord_3939992).sum := by decide
  have hdescent : baseEnd_3939992 < baseStart_3939992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939998 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3939998 : Nat := 118140960795 + 3939998 * 2 ^ 59
def prefixEnd_3939998 : Nat := 4983230072969 + 3 ^ 40 * 3939998 * 2
def baseEnd_3939998 : Nat := 674370917251126991135095

theorem tailTrace_3939998 : CollatzResearch.WordTrace tailWord_3939998 prefixEnd_3939998 674370917251126991135095 := by
  unfold tailWord_3939998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962941597508452366419581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95802355186711745954237765 17962941597508452366419581)
  ·
    refine ⟨6736103099065669637407343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17962941597508452366419581 6736103099065669637407343)
    ·
      refine ⟨10104154648598504456111015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736103099065669637407343 10104154648598504456111015)
      ·
        refine ⟨15156231972897756684166523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104154648598504456111015 15156231972897756684166523)
        ·
          refine ⟨22734347959346635026249785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156231972897756684166523 22734347959346635026249785)
          ·
            refine ⟨17050760969509976269687339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22734347959346635026249785 17050760969509976269687339)
            ·
              refine ⟨25576141454264964404531009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17050760969509976269687339 25576141454264964404531009)
              ·
                refine ⟨19182106090698723303398257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25576141454264964404531009 19182106090698723303398257)
                ·
                  refine ⟨14386579568024042477548693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19182106090698723303398257 14386579568024042477548693)
                  ·
                    refine ⟨674370917251126991135095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14386579568024042477548693 674370917251126991135095)
                    ·
                      rfl

theorem cell23_3939998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3939998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939998 prefixEnd_3939998 := by exact prefixLift 3939998
  have htrace : WordTrace (prefixWord ++ tailWord_3939998) baseStart_3939998 baseEnd_3939998 := by
    simpa [prefixWord, tailWord_3939998, baseEnd_3939998] using wordTrace_append hprefix tailTrace_3939998
  have hstable : (prefixWord ++ tailWord_3939998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939998).length < 2 ^ (prefixWord ++ tailWord_3939998).sum := by decide
  have hdescent : baseEnd_3939998 < baseStart_3939998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939999 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3939999 : Nat := 118140960795 + 3939999 * 2 ^ 59
def prefixEnd_3939999 : Nat := 4983230072969 + 3 ^ 40 * 3939999 * 2
def baseEnd_3939999 : Nat := 2023113265234035469492781

theorem tailTrace_3939999 : CollatzResearch.WordTrace tailWord_3939999 prefixEnd_3939999 2023113265234035469492781 := by
  unfold tailWord_3939999
  simp only [CollatzResearch.WordTrace]
  refine ⟨143703569253063996102143051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95802379502042664068095367 143703569253063996102143051)
  ·
    refine ⟨215555353879595994153214577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143703569253063996102143051 215555353879595994153214577)
    ·
      refine ⟨161666515409696995614910933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215555353879595994153214577 161666515409696995614910933)
      ·
        refine ⟨3789058954914773334724475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 161666515409696995614910933 3789058954914773334724475)
        ·
          refine ⟨5683588432372160002086713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789058954914773334724475 5683588432372160002086713)
          ·
            refine ⟨4262691324279120001565035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5683588432372160002086713 4262691324279120001565035)
            ·
              refine ⟨6394036986418680002347553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262691324279120001565035 6394036986418680002347553)
              ·
                refine ⟨4795527739814010001760665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6394036986418680002347553 4795527739814010001760665)
                ·
                  refine ⟨3596645804860507501320499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795527739814010001760665 3596645804860507501320499)
                  ·
                    refine ⟨5394968707290761251980749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3596645804860507501320499 5394968707290761251980749)
                    ·
                      refine ⟨2023113265234035469492781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5394968707290761251980749 2023113265234035469492781)
                      ·
                        rfl

theorem cell23_3939999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3939999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3939999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3939999 prefixEnd_3939999 := by exact prefixLift 3939999
  have htrace : WordTrace (prefixWord ++ tailWord_3939999) baseStart_3939999 baseEnd_3939999 := by
    simpa [prefixWord, tailWord_3939999, baseEnd_3939999] using wordTrace_append hprefix tailTrace_3939999
  have hstable : (prefixWord ++ tailWord_3939999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939999).length < 2 ^ (prefixWord ++ tailWord_3939999).sum := by decide
  have hdescent : baseEnd_3939999 < baseStart_3939999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940058 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_3940058 : Nat := 118140960795 + 3940058 * 2 ^ 59
def prefixEnd_3940058 : Nat := 4983230072969 + 3 ^ 40 * 3940058 * 2
def baseEnd_3940058 : Nat := 674381186864216912885003

theorem tailTrace_3940058 : CollatzResearch.WordTrace tailWord_3940058 prefixEnd_3940058 674381186864216912885003 := by
  unfold tailWord_3940058
  simp only [CollatzResearch.WordTrace]
  refine ⟨35926430289962562294635207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95803814106566832785693885 35926430289962562294635207)
  ·
    refine ⟨53889645434943843441952811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35926430289962562294635207 53889645434943843441952811)
    ·
      refine ⟨80834468152415765162929217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53889645434943843441952811 80834468152415765162929217)
      ·
        refine ⟨60625851114311823872196913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80834468152415765162929217 60625851114311823872196913)
        ·
          refine ⟨45469388335733867904147685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60625851114311823872196913 45469388335733867904147685)
          ·
            refine ⟨8525510312950100232027691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45469388335733867904147685 8525510312950100232027691)
            ·
              refine ⟨12788265469425150348041537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8525510312950100232027691 12788265469425150348041537)
              ·
                refine ⟨9591199102068862761031153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12788265469425150348041537 9591199102068862761031153)
                ·
                  refine ⟨7193399326551647070773365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9591199102068862761031153 7193399326551647070773365)
                  ·
                    refine ⟨674381186864216912885003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7193399326551647070773365 674381186864216912885003)
                    ·
                      rfl

theorem cell23_3940058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_3940058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940058 prefixEnd_3940058 := by exact prefixLift 3940058
  have htrace : WordTrace (prefixWord ++ tailWord_3940058) baseStart_3940058 baseEnd_3940058 := by
    simpa [prefixWord, tailWord_3940058, baseEnd_3940058] using wordTrace_append hprefix tailTrace_3940058
  have hstable : (prefixWord ++ tailWord_3940058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940058).length < 2 ^ (prefixWord ++ tailWord_3940058).sum := by decide
  have hdescent : baseEnd_3940058 < baseStart_3940058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940078 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3940078 : Nat := 118140960795 + 3940078 * 2 ^ 59
def prefixEnd_3940078 : Nat := 4983230072969 + 3 ^ 40 * 3940078 * 2
def baseEnd_3940078 : Nat := 2023153830205740660404917

theorem tailTrace_3940078 : CollatzResearch.WordTrace tailWord_3940078 prefixEnd_3940078 2023153830205740660404917 := by
  unfold tailWord_3940078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17963306327472224074283611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95804300413185195062845925 17963306327472224074283611)
  ·
    refine ⟨26944959491208336111425417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17963306327472224074283611 26944959491208336111425417)
    ·
      refine ⟨20208719618406252083569063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26944959491208336111425417 20208719618406252083569063)
      ·
        refine ⟨30313079427609378125353595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20208719618406252083569063 30313079427609378125353595)
        ·
          refine ⟨45469619141414067188030393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30313079427609378125353595 45469619141414067188030393)
          ·
            refine ⟨34102214356060550391022795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45469619141414067188030393 34102214356060550391022795)
            ·
              refine ⟨51153321534090825586534193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34102214356060550391022795 51153321534090825586534193)
              ·
                refine ⟨38364991150568119189900645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51153321534090825586534193 38364991150568119189900645)
                ·
                  refine ⟨7193435840731522348106371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38364991150568119189900645 7193435840731522348106371)
                  ·
                    refine ⟨10790153761097283522159557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7193435840731522348106371 10790153761097283522159557)
                    ·
                      refine ⟨2023153830205740660404917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10790153761097283522159557 2023153830205740660404917)
                      ·
                        rfl

theorem cell23_3940078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3940078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940078 prefixEnd_3940078 := by exact prefixLift 3940078
  have htrace : WordTrace (prefixWord ++ tailWord_3940078) baseStart_3940078 baseEnd_3940078 := by
    simpa [prefixWord, tailWord_3940078, baseEnd_3940078] using wordTrace_append hprefix tailTrace_3940078
  have hstable : (prefixWord ++ tailWord_3940078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940078).length < 2 ^ (prefixWord ++ tailWord_3940078).sum := by decide
  have hdescent : baseEnd_3940078 < baseStart_3940078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940105 : List Nat := [1, 2, 1, 1, 3, 2, 1, 7, 1, 4]
def baseStart_3940105 : Nat := 118140960795 + 3940105 * 2 ^ 59
def prefixEnd_3940105 : Nat := 4983230072969 + 3 ^ 40 * 3940105 * 2
def baseEnd_3940105 : Nat := 674389231394470684922431

theorem tailTrace_3940105 : CollatzResearch.WordTrace tailWord_3940105 prefixEnd_3940105 674389231394470684922431 := by
  unfold tailWord_3940105
  simp only [CollatzResearch.WordTrace]
  refine ⟨143707435390679976205501769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95804956927119984137001179 143707435390679976205501769)
  ·
    refine ⟨107780576543009982154126327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143707435390679976205501769 107780576543009982154126327)
    ·
      refine ⟨161670864814514973231189491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107780576543009982154126327 161670864814514973231189491)
      ·
        refine ⟨242506297221772459846784237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161670864814514973231189491 242506297221772459846784237)
        ·
          refine ⟨90939861458164672442544089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242506297221772459846784237 90939861458164672442544089)
          ·
            refine ⟨68204896093623504331908067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90939861458164672442544089 68204896093623504331908067)
            ·
              refine ⟨102307344140435256497862101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68204896093623504331908067 102307344140435256497862101)
              ·
                refine ⟨2397828378291451324168643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102307344140435256497862101 2397828378291451324168643)
                ·
                  refine ⟨3596742567437176986252965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397828378291451324168643 3596742567437176986252965)
                  ·
                    refine ⟨674389231394470684922431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3596742567437176986252965 674389231394470684922431)
                    ·
                      rfl

theorem cell23_3940105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 4].length) (baseStart_3940105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940105 prefixEnd_3940105 := by exact prefixLift 3940105
  have htrace : WordTrace (prefixWord ++ tailWord_3940105) baseStart_3940105 baseEnd_3940105 := by
    simpa [prefixWord, tailWord_3940105, baseEnd_3940105] using wordTrace_append hprefix tailTrace_3940105
  have hstable : (prefixWord ++ tailWord_3940105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940105).length < 2 ^ (prefixWord ++ tailWord_3940105).sum := by decide
  have hdescent : baseEnd_3940105 < baseStart_3940105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940122 : List Nat := [3, 1, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_3940122 : Nat := 118140960795 + 3940122 * 2 ^ 59
def prefixEnd_3940122 : Nat := 4983230072969 + 3 ^ 40 * 3940122 * 2
def baseEnd_3940122 : Nat := 674392141118179496084905

theorem tailTrace_3940122 : CollatzResearch.WordTrace tailWord_3940122 prefixEnd_3940122 674392141118179496084905 := by
  unfold tailWord_3940122
  simp only [CollatzResearch.WordTrace]
  refine ⟨35927013857904597027217655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95805370287745592072580413 35927013857904597027217655)
  ·
    refine ⟨53890520786856895540826483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35927013857904597027217655 53890520786856895540826483)
    ·
      refine ⟨80835781180285343311239725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53890520786856895540826483 80835781180285343311239725)
      ·
        refine ⟨30313417942607003741714897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80835781180285343311239725 30313417942607003741714897)
        ·
          refine ⟨22735063456955252806286173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30313417942607003741714897 22735063456955252806286173)
          ·
            refine ⟨8525648796358219802357315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22735063456955252806286173 8525648796358219802357315)
            ·
              refine ⟨12788473194537329703535973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8525648796358219802357315 12788473194537329703535973)
              ·
                refine ⟨2397838723975749319412995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12788473194537329703535973 2397838723975749319412995)
                ·
                  refine ⟨3596758085963623979119493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397838723975749319412995 3596758085963623979119493)
                  ·
                    refine ⟨674392141118179496084905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3596758085963623979119493 674392141118179496084905)
                    ·
                      rfl

theorem cell23_3940122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_3940122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940122 prefixEnd_3940122 := by exact prefixLift 3940122
  have htrace : WordTrace (prefixWord ++ tailWord_3940122) baseStart_3940122 baseEnd_3940122 := by
    simpa [prefixWord, tailWord_3940122, baseEnd_3940122] using wordTrace_append hprefix tailTrace_3940122
  have hstable : (prefixWord ++ tailWord_3940122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940122).length < 2 ^ (prefixWord ++ tailWord_3940122).sum := by decide
  have hdescent : baseEnd_3940122 < baseStart_3940122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940145 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_3940145 : Nat := 118140960795 + 3940145 * 2 ^ 59
def prefixEnd_3940145 : Nat := 4983230072969 + 3 ^ 40 * 3940145 * 2
def baseEnd_3940145 : Nat := 2023188233409591898267109

theorem tailTrace_3940145 : CollatzResearch.WordTrace tailWord_3940145 prefixEnd_3940145 2023188233409591898267109 := by
  unfold tailWord_3940145
  simp only [CollatzResearch.WordTrace]
  refine ⟨143708894310535063036957889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95805929540356708691305259 143708894310535063036957889)
  ·
    refine ⟨107781670732901297277718417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143708894310535063036957889 107781670732901297277718417)
    ·
      refine ⟨80836253049675972958288813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107781670732901297277718417 80836253049675972958288813)
      ·
        refine ⟨30313594893628489859358305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80836253049675972958288813 30313594893628489859358305)
        ·
          refine ⟨22735196170221367394518729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30313594893628489859358305 22735196170221367394518729)
          ·
            refine ⟨17051397127666025545889047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22735196170221367394518729 17051397127666025545889047)
            ·
              refine ⟨25577095691499038318833571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17051397127666025545889047 25577095691499038318833571)
              ·
                refine ⟨38365643537248557478250357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25577095691499038318833571 38365643537248557478250357)
                ·
                  refine ⟨3596779081617052263585971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38365643537248557478250357 3596779081617052263585971)
                  ·
                    refine ⟨5395168622425578395378957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3596779081617052263585971 5395168622425578395378957)
                    ·
                      refine ⟨2023188233409591898267109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5395168622425578395378957 2023188233409591898267109)
                      ·
                        rfl

theorem cell23_3940145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_3940145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940145 prefixEnd_3940145 := by exact prefixLift 3940145
  have htrace : WordTrace (prefixWord ++ tailWord_3940145) baseStart_3940145 baseEnd_3940145 := by
    simpa [prefixWord, tailWord_3940145, baseEnd_3940145] using wordTrace_append hprefix tailTrace_3940145
  have hstable : (prefixWord ++ tailWord_3940145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940145).length < 2 ^ (prefixWord ++ tailWord_3940145).sum := by decide
  have hdescent : baseEnd_3940145 < baseStart_3940145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940149 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_3940149 : Nat := 118140960795 + 3940149 * 2 ^ 59
def prefixEnd_3940149 : Nat := 4983230072969 + 3 ^ 40 * 3940149 * 2
def baseEnd_3940149 : Nat := 2023190287332209882617091

theorem tailTrace_3940149 : CollatzResearch.WordTrace tailWord_3940149 prefixEnd_3940149 2023190287332209882617091 := by
  unfold tailWord_3940149
  simp only [CollatzResearch.WordTrace]
  refine ⟨143709040202520571720103501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95806026801680381146735667 143709040202520571720103501)
  ·
    refine ⟨53890890075945214395038813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143709040202520571720103501 53890890075945214395038813)
    ·
      refine ⟨20209083778479455398139555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53890890075945214395038813 20209083778479455398139555)
      ·
        refine ⟨30313625667719183097209333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20209083778479455398139555 30313625667719183097209333)
        ·
          refine ⟨2841902406348673415363375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30313625667719183097209333 2841902406348673415363375)
          ·
            refine ⟨4262853609523010123045063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841902406348673415363375 4262853609523010123045063)
            ·
              refine ⟨6394280414284515184567595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262853609523010123045063 6394280414284515184567595)
              ·
                refine ⟨9591420621426772776851393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394280414284515184567595 9591420621426772776851393)
                ·
                  refine ⟨7193565466070079582638545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9591420621426772776851393 7193565466070079582638545)
                  ·
                    refine ⟨5395174099552559686978909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7193565466070079582638545 5395174099552559686978909)
                    ·
                      refine ⟨2023190287332209882617091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5395174099552559686978909 2023190287332209882617091)
                      ·
                        rfl

theorem cell23_3940149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_3940149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940149 prefixEnd_3940149 := by exact prefixLift 3940149
  have htrace : WordTrace (prefixWord ++ tailWord_3940149) baseStart_3940149 baseEnd_3940149 := by
    simpa [prefixWord, tailWord_3940149, baseEnd_3940149] using wordTrace_append hprefix tailTrace_3940149
  have hstable : (prefixWord ++ tailWord_3940149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940149).length < 2 ^ (prefixWord ++ tailWord_3940149).sum := by decide
  have hdescent : baseEnd_3940149 < baseStart_3940149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940205 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_3940205 : Nat := 118140960795 + 3940205 * 2 ^ 59
def prefixEnd_3940205 : Nat := 4983230072969 + 3 ^ 40 * 3940205 * 2
def baseEnd_3940205 : Nat := 2023219042248861663516833

theorem tailTrace_3940205 : CollatzResearch.WordTrace tailWord_3940205 prefixEnd_3940205 2023219042248861663516833 := by
  unfold tailWord_3940205
  simp only [CollatzResearch.WordTrace]
  refine ⟨143711082690317693284142069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95807388460211795522761379 143711082690317693284142069)
  ·
    refine ⟨13472914002217283745388319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143711082690317693284142069 13472914002217283745388319)
    ·
      refine ⟨20209371003325925618082479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13472914002217283745388319 20209371003325925618082479)
      ·
        refine ⟨30314056504988888427123719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20209371003325925618082479 30314056504988888427123719)
        ·
          refine ⟨45471084757483332640685579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30314056504988888427123719 45471084757483332640685579)
          ·
            refine ⟨68206627136224998961028369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45471084757483332640685579 68206627136224998961028369)
            ·
              refine ⟨51154970352168749220771277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68206627136224998961028369 51154970352168749220771277)
              ·
                refine ⟨19183113882063280957789229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51154970352168749220771277 19183113882063280957789229)
                ·
                  refine ⟨7193667705773730359170961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19183113882063280957789229 7193667705773730359170961)
                  ·
                    refine ⟨5395250779330297769378221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7193667705773730359170961 5395250779330297769378221)
                    ·
                      refine ⟨2023219042248861663516833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5395250779330297769378221 2023219042248861663516833)
                      ·
                        rfl

theorem cell23_3940205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_3940205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940205 prefixEnd_3940205 := by exact prefixLift 3940205
  have htrace : WordTrace (prefixWord ++ tailWord_3940205) baseStart_3940205 baseEnd_3940205 := by
    simpa [prefixWord, tailWord_3940205, baseEnd_3940205] using wordTrace_append hprefix tailTrace_3940205
  have hstable : (prefixWord ++ tailWord_3940205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940205).length < 2 ^ (prefixWord ++ tailWord_3940205).sum := by decide
  have hdescent : baseEnd_3940205 < baseStart_3940205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940222 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3940222 : Nat := 118140960795 + 3940222 * 2 ^ 59
def prefixEnd_3940222 : Nat := 4983230072969 + 3 ^ 40 * 3940222 * 2
def baseEnd_3940222 : Nat := 2023227771419988097004255

theorem tailTrace_3940222 : CollatzResearch.WordTrace tailWord_3940222 prefixEnd_3940222 2023227771419988097004255 := by
  unfold tailWord_3940222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17963962841407013148438865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95807801820837403458340613 17963962841407013148438865)
  ·
    refine ⟨13472972131055259861329149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17963962841407013148438865 13472972131055259861329149)
    ·
      refine ⟨5052364549145722447998431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13472972131055259861329149 5052364549145722447998431)
      ·
        refine ⟨7578546823718583671997647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5052364549145722447998431 7578546823718583671997647)
        ·
          refine ⟨11367820235577875507996471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578546823718583671997647 11367820235577875507996471)
          ·
            refine ⟨17051730353366813261994707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367820235577875507996471 17051730353366813261994707)
            ·
              refine ⟨25577595530050219892992061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17051730353366813261994707 25577595530050219892992061)
              ·
                refine ⟨9591598323768832459872023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25577595530050219892992061 9591598323768832459872023)
                ·
                  refine ⟨14387397485653248689808035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591598323768832459872023 14387397485653248689808035)
                  ·
                    refine ⟨21581096228479873034712053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14387397485653248689808035 21581096228479873034712053)
                    ·
                      refine ⟨2023227771419988097004255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21581096228479873034712053 2023227771419988097004255)
                      ·
                        rfl

theorem cell23_3940222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3940222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940222 prefixEnd_3940222 := by exact prefixLift 3940222
  have htrace : WordTrace (prefixWord ++ tailWord_3940222) baseStart_3940222 baseEnd_3940222 := by
    simpa [prefixWord, tailWord_3940222, baseEnd_3940222] using wordTrace_append hprefix tailTrace_3940222
  have hstable : (prefixWord ++ tailWord_3940222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940222).length < 2 ^ (prefixWord ++ tailWord_3940222).sum := by decide
  have hdescent : baseEnd_3940222 < baseStart_3940222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940309 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3940309 : Nat := 118140960795 + 3940309 * 2 ^ 59
def prefixEnd_3940309 : Nat := 4983230072969 + 3 ^ 40 * 3940309 * 2
def baseEnd_3940309 : Nat := 2023272444236929256616355

theorem tailTrace_3940309 : CollatzResearch.WordTrace tailWord_3940309 prefixEnd_3940309 2023272444236929256616355 := by
  unfold tailWord_3940309
  simp only [CollatzResearch.WordTrace]
  refine ⟨143714875881940919045927981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95809917254627279363951987 143714875881940919045927981)
  ·
    refine ⟨53893078455727844642222993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143714875881940919045927981 53893078455727844642222993)
    ·
      refine ⟨40419808841795883481667245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53893078455727844642222993 40419808841795883481667245)
      ·
        refine ⟨15157428315673456305625217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40419808841795883481667245 15157428315673456305625217)
        ·
          refine ⟨11368071236755092229218913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15157428315673456305625217 11368071236755092229218913)
          ·
            refine ⟨8526053427566319171914185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368071236755092229218913 8526053427566319171914185)
            ·
              refine ⟨6394540070674739378935639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8526053427566319171914185 6394540070674739378935639)
              ·
                refine ⟨9591810106012109068403459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394540070674739378935639 9591810106012109068403459)
                ·
                  refine ⟨14387715159018163602605189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591810106012109068403459 14387715159018163602605189)
                  ·
                    refine ⟨2697696592315905675488473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14387715159018163602605189 2697696592315905675488473)
                    ·
                      refine ⟨2023272444236929256616355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697696592315905675488473 2023272444236929256616355)
                      ·
                        rfl

theorem cell23_3940309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3940309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940309 prefixEnd_3940309 := by exact prefixLift 3940309
  have htrace : WordTrace (prefixWord ++ tailWord_3940309) baseStart_3940309 baseEnd_3940309 := by
    simpa [prefixWord, tailWord_3940309, baseEnd_3940309] using wordTrace_append hprefix tailTrace_3940309
  have hstable : (prefixWord ++ tailWord_3940309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940309).length < 2 ^ (prefixWord ++ tailWord_3940309).sum := by decide
  have hdescent : baseEnd_3940309 < baseStart_3940309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940402 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_3940402 : Nat := 118140960795 + 3940402 * 2 ^ 59
def prefixEnd_3940402 : Nat := 4983230072969 + 3 ^ 40 * 3940402 * 2
def baseEnd_3940402 : Nat := 2023320197937797392753427

theorem tailTrace_3940402 : CollatzResearch.WordTrace tailWord_3940402 prefixEnd_3940402 2023320197937797392753427 := by
  unfold tailWord_3940402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35929566967650998982265865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95812178580402663952708973 35929566967650998982265865)
  ·
    refine ⟨26947175225738249236699399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35929566967650998982265865 26947175225738249236699399)
    ·
      refine ⟨40420762838607373855049099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26947175225738249236699399 40420762838607373855049099)
      ·
        refine ⟨60631144257911060782573649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40420762838607373855049099 60631144257911060782573649)
        ·
          refine ⟨45473358193433295586930237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60631144257911060782573649 45473358193433295586930237)
          ·
            refine ⟨17052509322537485845098839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45473358193433295586930237 17052509322537485845098839)
            ·
              refine ⟨25578763983806228767648259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17052509322537485845098839 25578763983806228767648259)
              ·
                refine ⟨38368145975709343151472389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25578763983806228767648259 38368145975709343151472389)
                ·
                  refine ⟨7194027370445501840901073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38368145975709343151472389 7194027370445501840901073)
                  ·
                    refine ⟨5395520527834126380675805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7194027370445501840901073 5395520527834126380675805)
                    ·
                      refine ⟨2023320197937797392753427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5395520527834126380675805 2023320197937797392753427)
                      ·
                        rfl

theorem cell23_3940402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_3940402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940402 prefixEnd_3940402 := by exact prefixLift 3940402
  have htrace : WordTrace (prefixWord ++ tailWord_3940402) baseStart_3940402 baseEnd_3940402 := by
    simpa [prefixWord, tailWord_3940402, baseEnd_3940402] using wordTrace_append hprefix tailTrace_3940402
  have hstable : (prefixWord ++ tailWord_3940402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940402).length < 2 ^ (prefixWord ++ tailWord_3940402).sum := by decide
  have hdescent : baseEnd_3940402 < baseStart_3940402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940405 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 8]
def baseStart_3940405 : Nat := 118140960795 + 3940405 * 2 ^ 59
def prefixEnd_3940405 : Nat := 4983230072969 + 3 ^ 40 * 3940405 * 2
def baseEnd_3940405 : Nat := 224813526486640097890657

theorem tailTrace_3940405 : CollatzResearch.WordTrace tailWord_3940405 prefixEnd_3940405 224813526486640097890657 := by
  unfold tailWord_3940405
  simp only [CollatzResearch.WordTrace]
  refine ⟨143718377289593127441422669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95812251526395418294281779 143718377289593127441422669)
  ·
    refine ⟨53894391483597422790533501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143718377289593127441422669 53894391483597422790533501)
    ·
      refine ⟨20210396806349033546450063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53894391483597422790533501 20210396806349033546450063)
      ·
        refine ⟨30315595209523550319675095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20210396806349033546450063 30315595209523550319675095)
        ·
          refine ⟨45473392814285325479512643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30315595209523550319675095 45473392814285325479512643)
          ·
            refine ⟨68210089221427988219268965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45473392814285325479512643 68210089221427988219268965)
            ·
              refine ⟨12789391729017747791112931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68210089221427988219268965 12789391729017747791112931)
              ·
                refine ⟨19184087593526621686669397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12789391729017747791112931 19184087593526621686669397)
                ·
                  refine ⟨224813526486640097890657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19184087593526621686669397 224813526486640097890657)
                  ·
                    rfl

theorem cell23_3940405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_3940405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940405 prefixEnd_3940405 := by exact prefixLift 3940405
  have htrace : WordTrace (prefixWord ++ tailWord_3940405) baseStart_3940405 baseEnd_3940405 := by
    simpa [prefixWord, tailWord_3940405, baseEnd_3940405] using wordTrace_append hprefix tailTrace_3940405
  have hstable : (prefixWord ++ tailWord_3940405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940405).length < 2 ^ (prefixWord ++ tailWord_3940405).sum := by decide
  have hdescent : baseEnd_3940405 < baseStart_3940405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940452 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_3940452 : Nat := 118140960795 + 3940452 * 2 ^ 59
def prefixEnd_3940452 : Nat := 4983230072969 + 3 ^ 40 * 3940452 * 2
def baseEnd_3940452 : Nat := 674448623990174065709399

theorem tailTrace_3940452 : CollatzResearch.WordTrace tailWord_3940452 prefixEnd_3940452 674448623990174065709399 := by
  unfold tailWord_3940452
  simp only [CollatzResearch.WordTrace]
  refine ⟨71860045760211427234191805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95813394346948569645589073 71860045760211427234191805)
  ·
    refine ⟨26947517160079285212821927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71860045760211427234191805 26947517160079285212821927)
    ·
      refine ⟨40421275740118927819232891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26947517160079285212821927 40421275740118927819232891)
      ·
        refine ⟨60631913610178391728849337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40421275740118927819232891 60631913610178391728849337)
        ·
          refine ⟨45473935207633793796637003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60631913610178391728849337 45473935207633793796637003)
          ·
            refine ⟨68210902811450690694955505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45473935207633793796637003 68210902811450690694955505)
            ·
              refine ⟨51158177108588018021216629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68210902811450690694955505 51158177108588018021216629)
              ·
                refine ⟨4796079103930126689489059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51158177108588018021216629 4796079103930126689489059)
                ·
                  refine ⟨7194118655895190034233589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796079103930126689489059 7194118655895190034233589)
                  ·
                    refine ⟨674448623990174065709399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7194118655895190034233589 674448623990174065709399)
                    ·
                      rfl

theorem cell23_3940452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_3940452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940452 prefixEnd_3940452 := by exact prefixLift 3940452
  have htrace : WordTrace (prefixWord ++ tailWord_3940452) baseStart_3940452 baseEnd_3940452 := by
    simpa [prefixWord, tailWord_3940452, baseEnd_3940452] using wordTrace_append hprefix tailTrace_3940452
  have hstable : (prefixWord ++ tailWord_3940452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940452).length < 2 ^ (prefixWord ++ tailWord_3940452).sum := by decide
  have hdescent : baseEnd_3940452 < baseStart_3940452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940465 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 3, 6]
def baseStart_3940465 : Nat := 118140960795 + 3940465 * 2 ^ 59
def prefixEnd_3940465 : Nat := 4983230072969 + 3 ^ 40 * 3940465 * 2
def baseEnd_3940465 : Nat := 674450849073010215421879

theorem tailTrace_3940465 : CollatzResearch.WordTrace tailWord_3940465 prefixEnd_3940465 674450849073010215421879 := by
  unfold tailWord_3940465
  simp only [CollatzResearch.WordTrace]
  refine ⟨143720565669375757688606849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95813710446250505125737899 143720565669375757688606849)
  ·
    refine ⟨107790424252031818266455137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143720565669375757688606849 107790424252031818266455137)
    ·
      refine ⟨80842818189023863699841353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107790424252031818266455137 80842818189023863699841353)
      ·
        refine ⟨60632113641767897774881015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80842818189023863699841353 60632113641767897774881015)
        ·
          refine ⟨90948170462651846662321523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60632113641767897774881015 90948170462651846662321523)
          ·
            refine ⟨136422255693977769993482285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90948170462651846662321523 136422255693977769993482285)
            ·
              refine ⟨51158345885241663747555857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136422255693977769993482285 51158345885241663747555857)
              ·
                refine ⟨38368759413931247810666893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51158345885241663747555857 38368759413931247810666893)
                ·
                  refine ⟨14388284780224217929000085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38368759413931247810666893 14388284780224217929000085)
                  ·
                    refine ⟨674450849073010215421879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14388284780224217929000085 674450849073010215421879)
                    ·
                      rfl

theorem cell23_3940465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_3940465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940465 prefixEnd_3940465 := by exact prefixLift 3940465
  have htrace : WordTrace (prefixWord ++ tailWord_3940465) baseStart_3940465 baseEnd_3940465 := by
    simpa [prefixWord, tailWord_3940465, baseEnd_3940465] using wordTrace_append hprefix tailTrace_3940465
  have hstable : (prefixWord ++ tailWord_3940465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940465).length < 2 ^ (prefixWord ++ tailWord_3940465).sum := by decide
  have hdescent : baseEnd_3940465 < baseStart_3940465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940472 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 2, 6, 2]
def baseStart_3940472 : Nat := 118140960795 + 3940472 * 2 ^ 59
def prefixEnd_3940472 : Nat := 4983230072969 + 3 ^ 40 * 3940472 * 2
def baseEnd_3940472 : Nat := 2023356141583612118878105

theorem tailTrace_3940472 : CollatzResearch.WordTrace tailWord_3940472 prefixEnd_3940472 2023356141583612118878105 := by
  unfold tailWord_3940472
  simp only [CollatzResearch.WordTrace]
  refine ⟨71860410490175198942055835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95813880653566931922741113 71860410490175198942055835)
  ·
    refine ⟨107790615735262798413083753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71860410490175198942055835 107790615735262798413083753)
    ·
      refine ⟨80842961801447098809812815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107790615735262798413083753 80842961801447098809812815)
      ·
        refine ⟨121264442702170648214719223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80842961801447098809812815 121264442702170648214719223)
        ·
          refine ⟨181896664053255972322078835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121264442702170648214719223 181896664053255972322078835)
          ·
            refine ⟨272844996079883958483118253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181896664053255972322078835 272844996079883958483118253)
            ·
              refine ⟨102316873529956484431169345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272844996079883958483118253 102316873529956484431169345)
              ·
                refine ⟨76737655147467363323377009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102316873529956484431169345 76737655147467363323377009)
                ·
                  refine ⟨57553241360600522492532757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76737655147467363323377009 57553241360600522492532757)
                  ·
                    refine ⟨2697808188778149491837473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57553241360600522492532757 2697808188778149491837473)
                    ·
                      refine ⟨2023356141583612118878105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697808188778149491837473 2023356141583612118878105)
                      ·
                        rfl

theorem cell23_3940472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_3940472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940472 prefixEnd_3940472 := by exact prefixLift 3940472
  have htrace : WordTrace (prefixWord ++ tailWord_3940472) baseStart_3940472 baseEnd_3940472 := by
    simpa [prefixWord, tailWord_3940472, baseEnd_3940472] using wordTrace_append hprefix tailTrace_3940472
  have hstable : (prefixWord ++ tailWord_3940472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940472).length < 2 ^ (prefixWord ++ tailWord_3940472).sum := by decide
  have hdescent : baseEnd_3940472 < baseStart_3940472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940503 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 1, 5]
def baseStart_3940503 : Nat := 118140960795 + 3940503 * 2 ^ 59
def prefixEnd_3940503 : Nat := 4983230072969 + 3 ^ 40 * 3940503 * 2
def baseEnd_3940503 : Nat := 674457353161300499196821

theorem tailTrace_3940503 : CollatzResearch.WordTrace tailWord_3940503 prefixEnd_3940503 674457353161300499196821 := by
  unfold tailWord_3940503
  simp only [CollatzResearch.WordTrace]
  refine ⟨143721951643238090178490163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95814634428825393452326775 143721951643238090178490163)
  ·
    refine ⟨215582927464857135267735245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143721951643238090178490163 215582927464857135267735245)
    ·
      refine ⟨80843597799321425725400717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215582927464857135267735245 80843597799321425725400717)
      ·
        refine ⟨30316349174745534647025269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80843597799321425725400717 30316349174745534647025269)
        ·
          refine ⟨2842157735132393873158619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30316349174745534647025269 2842157735132393873158619)
          ·
            refine ⟨4263236602698590809737929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842157735132393873158619 4263236602698590809737929)
            ·
              refine ⟨3197427452023943107303447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4263236602698590809737929 3197427452023943107303447)
              ·
                refine ⟨4796141178035914660955171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197427452023943107303447 4796141178035914660955171)
                ·
                  refine ⟨7194211767053871991432757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796141178035914660955171 7194211767053871991432757)
                  ·
                    refine ⟨674457353161300499196821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7194211767053871991432757 674457353161300499196821)
                    ·
                      rfl

theorem cell23_3940503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_3940503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940503 prefixEnd_3940503 := by exact prefixLift 3940503
  have htrace : WordTrace (prefixWord ++ tailWord_3940503) baseStart_3940503 baseEnd_3940503 := by
    simpa [prefixWord, tailWord_3940503, baseEnd_3940503] using wordTrace_append hprefix tailTrace_3940503
  have hstable : (prefixWord ++ tailWord_3940503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940503).length < 2 ^ (prefixWord ++ tailWord_3940503).sum := by decide
  have hdescent : baseEnd_3940503 < baseStart_3940503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940506 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3940506 : Nat := 118140960795 + 3940506 * 2 ^ 59
def prefixEnd_3940506 : Nat := 4983230072969 + 3 ^ 40 * 3940506 * 2
def baseEnd_3940506 : Nat := 2023373599925864985852949

theorem tailTrace_3940506 : CollatzResearch.WordTrace tailWord_3940506 prefixEnd_3940506 2023373599925864985852949 := by
  unfold tailWord_3940506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35930515265556805422712343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95814707374818147793899581 35930515265556805422712343)
  ·
    refine ⟨53895772898335208134068515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35930515265556805422712343 53895772898335208134068515)
    ·
      refine ⟨80843659347502812201102773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53895772898335208134068515 80843659347502812201102773)
      ·
        refine ⟨7579093063828388643853385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80843659347502812201102773 7579093063828388643853385)
        ·
          refine ⟨5684319797871291482890039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7579093063828388643853385 5684319797871291482890039)
          ·
            refine ⟨8526479696806937224335059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684319797871291482890039 8526479696806937224335059)
            ·
              refine ⟨12789719545210405836502589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526479696806937224335059 12789719545210405836502589)
              ·
                refine ⟨4796144829453902188688471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12789719545210405836502589 4796144829453902188688471)
                ·
                  refine ⟨7194217244180853283032707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796144829453902188688471 7194217244180853283032707)
                  ·
                    refine ⟨10791325866271279924549061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7194217244180853283032707 10791325866271279924549061)
                    ·
                      refine ⟨2023373599925864985852949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10791325866271279924549061 2023373599925864985852949)
                      ·
                        rfl

theorem cell23_3940506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3940506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940506 prefixEnd_3940506 := by exact prefixLift 3940506
  have htrace : WordTrace (prefixWord ++ tailWord_3940506) baseStart_3940506 baseEnd_3940506 := by
    simpa [prefixWord, tailWord_3940506, baseEnd_3940506] using wordTrace_append hprefix tailTrace_3940506
  have hstable : (prefixWord ++ tailWord_3940506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940506).length < 2 ^ (prefixWord ++ tailWord_3940506).sum := by decide
  have hdescent : baseEnd_3940506 < baseStart_3940506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940515 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3940515 : Nat := 118140960795 + 3940515 * 2 ^ 59
def prefixEnd_3940515 : Nat := 4983230072969 + 3 ^ 40 * 3940515 * 2
def baseEnd_3940515 : Nat := 2023378221251755450640407

theorem tailTrace_3940515 : CollatzResearch.WordTrace tailWord_3940515 prefixEnd_3940515 2023378221251755450640407 := by
  unfold tailWord_3940515
  simp only [CollatzResearch.WordTrace]
  refine ⟨143722389319194616227926999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95814926212796410818617999 143722389319194616227926999)
  ·
    refine ⟨215583583978791924341890499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143722389319194616227926999 215583583978791924341890499)
    ·
      refine ⟨323375375968187886512835749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215583583978791924341890499 323375375968187886512835749)
      ·
        refine ⟨60632882994035228721156703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323375375968187886512835749 60632882994035228721156703)
        ·
          refine ⟨90949324491052843081735055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60632882994035228721156703 90949324491052843081735055)
          ·
            refine ⟨136423986736579264622602583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90949324491052843081735055 136423986736579264622602583)
            ·
              refine ⟨204635980104868896933903875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136423986736579264622602583 204635980104868896933903875)
              ·
                refine ⟨306953970157303345400855813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204635980104868896933903875 306953970157303345400855813)
                ·
                  refine ⟨57553869404494377262660465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306953970157303345400855813 57553869404494377262660465)
                  ·
                    refine ⟨43165402053370782946995349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57553869404494377262660465 43165402053370782946995349)
                    ·
                      refine ⟨2023378221251755450640407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43165402053370782946995349 2023378221251755450640407)
                      ·
                        rfl

theorem cell23_3940515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3940515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940515 prefixEnd_3940515 := by exact prefixLift 3940515
  have htrace : WordTrace (prefixWord ++ tailWord_3940515) baseStart_3940515 baseEnd_3940515 := by
    simpa [prefixWord, tailWord_3940515, baseEnd_3940515] using wordTrace_append hprefix tailTrace_3940515
  have hstable : (prefixWord ++ tailWord_3940515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940515).length < 2 ^ (prefixWord ++ tailWord_3940515).sum := by decide
  have hdescent : baseEnd_3940515 < baseStart_3940515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940533 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3940533 : Nat := 118140960795 + 3940533 * 2 ^ 59
def prefixEnd_3940533 : Nat := 4983230072969 + 3 ^ 40 * 3940533 * 2
def baseEnd_3940533 : Nat := 674462487967845460071775

theorem tailTrace_3940533 : CollatzResearch.WordTrace tailWord_3940533 prefixEnd_3940533 674462487967845460071775 := by
  unfold tailWord_3940533
  simp only [CollatzResearch.WordTrace]
  refine ⟨143723045833129405302082253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95815363888752936868054835 143723045833129405302082253)
  ·
    refine ⟨53896142187423526988280845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143723045833129405302082253 53896142187423526988280845)
    ·
      refine ⟨20211053320283822620605317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53896142187423526988280845 20211053320283822620605317)
      ·
        refine ⟨3789572497553216741363497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20211053320283822620605317 3789572497553216741363497)
        ·
          refine ⟨2842179373164912556022623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3789572497553216741363497 2842179373164912556022623)
          ·
            refine ⟨4263269059747368834033935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842179373164912556022623 4263269059747368834033935)
            ·
              refine ⟨6394903589621053251050903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263269059747368834033935 6394903589621053251050903)
              ·
                refine ⟨9592355384431579876576355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394903589621053251050903 9592355384431579876576355)
                ·
                  refine ⟨14388533076647369814864533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9592355384431579876576355 14388533076647369814864533)
                  ·
                    refine ⟨674462487967845460071775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14388533076647369814864533 674462487967845460071775)
                    ·
                      rfl

theorem cell23_3940533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3940533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940533 prefixEnd_3940533 := by exact prefixLift 3940533
  have htrace : WordTrace (prefixWord ++ tailWord_3940533) baseStart_3940533 baseEnd_3940533 := by
    simpa [prefixWord, tailWord_3940533, baseEnd_3940533] using wordTrace_append hprefix tailTrace_3940533
  have hstable : (prefixWord ++ tailWord_3940533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940533).length < 2 ^ (prefixWord ++ tailWord_3940533).sum := by decide
  have hdescent : baseEnd_3940533 < baseStart_3940533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940546 : List Nat := [3, 5, 1, 1, 1, 2, 1, 9]
def baseStart_3940546 : Nat := 118140960795 + 3940546 * 2 ^ 59
def prefixEnd_3940546 : Nat := 4983230072969 + 3 ^ 40 * 3940546 * 2
def baseEnd_3940546 : Nat := 74940523672297956642695

theorem tailTrace_3940546 : CollatzResearch.WordTrace tailWord_3940546 prefixEnd_3940546 74940523672297956642695 := by
  unfold tailWord_3940546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35930879995520577130576373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95815679988054872348203661 35930879995520577130576373)
  ·
    refine ⟨3368519999580054105991535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35930879995520577130576373 3368519999580054105991535)
    ·
      refine ⟨5052779999370081158987303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368519999580054105991535 5052779999370081158987303)
      ·
        refine ⟨7579169999055121738480955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5052779999370081158987303 7579169999055121738480955)
        ·
          refine ⟨11368754998582682607721433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7579169999055121738480955 11368754998582682607721433)
          ·
            refine ⟨8526566248937011955791075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368754998582682607721433 8526566248937011955791075)
            ·
              refine ⟨12789849373405517933686613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526566248937011955791075 12789849373405517933686613)
              ·
                refine ⟨74940523672297956642695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12789849373405517933686613 74940523672297956642695)
                ·
                  rfl

theorem cell23_3940546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 9].length) (baseStart_3940546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940546 prefixEnd_3940546 := by exact prefixLift 3940546
  have htrace : WordTrace (prefixWord ++ tailWord_3940546) baseStart_3940546 baseEnd_3940546 := by
    simpa [prefixWord, tailWord_3940546, baseEnd_3940546] using wordTrace_append hprefix tailTrace_3940546
  have hstable : (prefixWord ++ tailWord_3940546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940546).length < 2 ^ (prefixWord ++ tailWord_3940546).sum := by decide
  have hdescent : baseEnd_3940546 < baseStart_3940546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940549 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 3, 3, 2]
def baseStart_3940549 : Nat := 118140960795 + 3940549 * 2 ^ 59
def prefixEnd_3940549 : Nat := 4983230072969 + 3 ^ 40 * 3940549 * 2
def baseEnd_3940549 : Nat := 2023395679594008317615251

theorem tailTrace_3940549 : CollatzResearch.WordTrace tailWord_3940549 prefixEnd_3940549 2023395679594008317615251 := by
  unfold tailWord_3940549
  simp only [CollatzResearch.WordTrace]
  refine ⟨143723629401071440034664701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95815752934047626689776467 143723629401071440034664701)
  ·
    refine ⟨53896361025401790012999263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143723629401071440034664701 53896361025401790012999263)
    ·
      refine ⟨80844541538102685019498895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53896361025401790012999263 80844541538102685019498895)
      ·
        refine ⟨121266812307154027529248343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80844541538102685019498895 121266812307154027529248343)
        ·
          refine ⟨181900218460731041293872515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121266812307154027529248343 181900218460731041293872515)
          ·
            refine ⟨272850327691096561940808773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181900218460731041293872515 272850327691096561940808773)
            ·
              refine ⟨51159436442080605363901645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272850327691096561940808773 51159436442080605363901645)
              ·
                refine ⟨19184788665780227011463117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51159436442080605363901645 19184788665780227011463117)
                ·
                  refine ⟨7194295749667585129298669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19184788665780227011463117 7194295749667585129298669)
                  ·
                    refine ⟨2697860906125344423487001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7194295749667585129298669 2697860906125344423487001)
                    ·
                      refine ⟨2023395679594008317615251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697860906125344423487001 2023395679594008317615251)
                      ·
                        rfl

theorem cell23_3940549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_3940549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940549 prefixEnd_3940549 := by exact prefixLift 3940549
  have htrace : WordTrace (prefixWord ++ tailWord_3940549) baseStart_3940549 baseEnd_3940549 := by
    simpa [prefixWord, tailWord_3940549, baseEnd_3940549] using wordTrace_append hprefix tailTrace_3940549
  have hstable : (prefixWord ++ tailWord_3940549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940549).length < 2 ^ (prefixWord ++ tailWord_3940549).sum := by decide
  have hdescent : baseEnd_3940549 < baseStart_3940549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940592 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_3940592 : Nat := 118140960795 + 3940592 * 2 ^ 59
def prefixEnd_3940592 : Nat := 4983230072969 + 3 ^ 40 * 3940592 * 2
def baseEnd_3940592 : Nat := 2023417759262151649377553

theorem tailTrace_3940592 : CollatzResearch.WordTrace tailWord_3940592 prefixEnd_3940592 2023417759262151649377553 := by
  unfold tailWord_3940592
  simp only [CollatzResearch.WordTrace]
  refine ⟨71862598869957829189240015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95816798493277105585653353 71862598869957829189240015)
  ·
    refine ⟨107793898304936743783860023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71862598869957829189240015 107793898304936743783860023)
    ·
      refine ⟨161690847457405115675790035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107793898304936743783860023 161690847457405115675790035)
      ·
        refine ⟨242536271186107673513685053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161690847457405115675790035 242536271186107673513685053)
        ·
          refine ⟨90951101694790377567631895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242536271186107673513685053 90951101694790377567631895)
          ·
            refine ⟨136426652542185566351447843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90951101694790377567631895 136426652542185566351447843)
            ·
              refine ⟨204639978813278349527171765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136426652542185566351447843 204639978813278349527171765)
              ·
                refine ⟨19184998013744845268172353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204639978813278349527171765 19184998013744845268172353)
                ·
                  refine ⟨14388748510308633951129265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19184998013744845268172353 14388748510308633951129265)
                  ·
                    refine ⟨10791561382731475463346949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14388748510308633951129265 10791561382731475463346949)
                    ·
                      refine ⟨2023417759262151649377553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10791561382731475463346949 2023417759262151649377553)
                      ·
                        rfl

theorem cell23_3940592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_3940592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940592 prefixEnd_3940592 := by exact prefixLift 3940592
  have htrace : WordTrace (prefixWord ++ tailWord_3940592) baseStart_3940592 baseEnd_3940592 := by
    simpa [prefixWord, tailWord_3940592, baseEnd_3940592] using wordTrace_append hprefix tailTrace_3940592
  have hstable : (prefixWord ++ tailWord_3940592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940592).length < 2 ^ (prefixWord ++ tailWord_3940592).sum := by decide
  have hdescent : baseEnd_3940592 < baseStart_3940592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940619 : List Nat := [1, 1, 1, 1, 5, 2, 2, 5, 5]
def baseStart_3940619 : Nat := 118140960795 + 3940619 * 2 ^ 59
def prefixEnd_3940619 : Nat := 4983230072969 + 3 ^ 40 * 3940619 * 2
def baseEnd_3940619 : Nat := 224825735915535893748881

theorem tailTrace_3940619 : CollatzResearch.WordTrace tailWord_3940619 prefixEnd_3940619 224825735915535893748881 := by
  unfold tailWord_3940619
  simp only [CollatzResearch.WordTrace]
  refine ⟨143726182510817841989712911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95817455007211894659808607 143726182510817841989712911)
  ·
    refine ⟨215589273766226762984569367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143726182510817841989712911 215589273766226762984569367)
    ·
      refine ⟨323383910649340144476854051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215589273766226762984569367 323383910649340144476854051)
      ·
        refine ⟨485075865974010216715281077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323383910649340144476854051 485075865974010216715281077)
        ·
          refine ⟨45475862435063457817057601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 485075865974010216715281077 45475862435063457817057601)
          ·
            refine ⟨34106896826297593362793201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45475862435063457817057601 34106896826297593362793201)
            ·
              refine ⟨25580172619723195022094901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34106896826297593362793201 25580172619723195022094901)
              ·
                refine ⟨2398141183099049533321397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25580172619723195022094901 2398141183099049533321397)
                ·
                  refine ⟨224825735915535893748881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2398141183099049533321397 224825735915535893748881)
                  ·
                    rfl

theorem cell23_3940619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 5].length) (baseStart_3940619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940619 prefixEnd_3940619 := by exact prefixLift 3940619
  have htrace : WordTrace (prefixWord ++ tailWord_3940619) baseStart_3940619 baseEnd_3940619 := by
    simpa [prefixWord, tailWord_3940619, baseEnd_3940619] using wordTrace_append hprefix tailTrace_3940619
  have hstable : (prefixWord ++ tailWord_3940619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940619).length < 2 ^ (prefixWord ++ tailWord_3940619).sum := by decide
  have hdescent : baseEnd_3940619 < baseStart_3940619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940647 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3940647 : Nat := 118140960795 + 3940647 * 2 ^ 59
def prefixEnd_3940647 : Nat := 4983230072969 + 3 ^ 40 * 3940647 * 2
def baseEnd_3940647 : Nat := 2023446000698148934189801

theorem tailTrace_3940647 : CollatzResearch.WordTrace tailWord_3940647 prefixEnd_3940647 2023446000698148934189801 := by
  unfold tailWord_3940647
  simp only [CollatzResearch.WordTrace]
  refine ⟨143727203754716402771732195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95818135836477601847821463 143727203754716402771732195)
  ·
    refine ⟨215590805632074604157598293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143727203754716402771732195 215590805632074604157598293)
    ·
      refine ⟨2526454753500874267471855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 215590805632074604157598293 2526454753500874267471855)
      ·
        refine ⟨3789682130251311401207783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526454753500874267471855 3789682130251311401207783)
        ·
          refine ⟨5684523195376967101811675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789682130251311401207783 5684523195376967101811675)
          ·
            refine ⟨8526784793065450652717513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684523195376967101811675 8526784793065450652717513)
            ·
              refine ⟨6395088594799087989538135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8526784793065450652717513 6395088594799087989538135)
              ·
                refine ⟨9592632892198631984307203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395088594799087989538135 9592632892198631984307203)
                ·
                  refine ⟨14388949338297947976460805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9592632892198631984307203 14388949338297947976460805)
                  ·
                    refine ⟨2697928000930865245586401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14388949338297947976460805 2697928000930865245586401)
                    ·
                      refine ⟨2023446000698148934189801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2697928000930865245586401 2023446000698148934189801)
                      ·
                        rfl

theorem cell23_3940647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3940647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940647 prefixEnd_3940647 := by exact prefixLift 3940647
  have htrace : WordTrace (prefixWord ++ tailWord_3940647) baseStart_3940647 baseEnd_3940647 := by
    simpa [prefixWord, tailWord_3940647, baseEnd_3940647] using wordTrace_append hprefix tailTrace_3940647
  have hstable : (prefixWord ++ tailWord_3940647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940647).length < 2 ^ (prefixWord ++ tailWord_3940647).sum := by decide
  have hdescent : baseEnd_3940647 < baseStart_3940647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940666 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_3940666 : Nat := 118140960795 + 3940666 * 2 ^ 59
def prefixEnd_3940666 : Nat := 4983230072969 + 3 ^ 40 * 3940666 * 2
def baseEnd_3940666 : Nat := 674485252276861453284071

theorem tailTrace_3940666 : CollatzResearch.WordTrace tailWord_3940666 prefixEnd_3940666 674485252276861453284071 := by
  unfold tailWord_3940666
  simp only [CollatzResearch.WordTrace]
  refine ⟨35931974185411892254168463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95818597827765046011115901 35931974185411892254168463)
  ·
    refine ⟨53897961278117838381252695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35931974185411892254168463 53897961278117838381252695)
    ·
      refine ⟨80846941917176757571879043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53897961278117838381252695 80846941917176757571879043)
      ·
        refine ⟨121270412875765136357818565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80846941917176757571879043 121270412875765136357818565)
        ·
          refine ⟨22738202414205963067090981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121270412875765136357818565 22738202414205963067090981)
          ·
            refine ⟨4263412952663618075079559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22738202414205963067090981 4263412952663618075079559)
            ·
              refine ⟨6395119428995427112619339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263412952663618075079559 6395119428995427112619339)
              ·
                refine ⟨9592679143493140668929009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395119428995427112619339 9592679143493140668929009)
                ·
                  refine ⟨7194509357619855501696757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9592679143493140668929009 7194509357619855501696757)
                  ·
                    refine ⟨674485252276861453284071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7194509357619855501696757 674485252276861453284071)
                    ·
                      rfl

theorem cell23_3940666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_3940666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940666 prefixEnd_3940666 := by exact prefixLift 3940666
  have htrace : WordTrace (prefixWord ++ tailWord_3940666) baseStart_3940666 baseEnd_3940666 := by
    simpa [prefixWord, tailWord_3940666, baseEnd_3940666] using wordTrace_append hprefix tailTrace_3940666
  have hstable : (prefixWord ++ tailWord_3940666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940666).length < 2 ^ (prefixWord ++ tailWord_3940666).sum := by decide
  have hdescent : baseEnd_3940666 < baseStart_3940666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940672 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_3940672 : Nat := 118140960795 + 3940672 * 2 ^ 59
def prefixEnd_3940672 : Nat := 4983230072969 + 3 ^ 40 * 3940672 * 2
def baseEnd_3940672 : Nat := 2023458837714511336377185

theorem tailTrace_3940672 : CollatzResearch.WordTrace tailWord_3940672 prefixEnd_3940672 2023458837714511336377185 := by
  unfold tailWord_3940672
  simp only [CollatzResearch.WordTrace]
  refine ⟨71864057789812916020696135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95818743719750554694261513 71864057789812916020696135)
  ·
    refine ⟨107796086684719374031044203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71864057789812916020696135 107796086684719374031044203)
    ·
      refine ⟨161694130027079061046566305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107796086684719374031044203 161694130027079061046566305)
      ·
        refine ⟨121270597520309295784924729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161694130027079061046566305 121270597520309295784924729)
        ·
          refine ⟨90952948140231971838693547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121270597520309295784924729 90952948140231971838693547)
          ·
            refine ⟨136429422210347957758040321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90952948140231971838693547 136429422210347957758040321)
            ·
              refine ⟨102322066657760968318530241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136429422210347957758040321 102322066657760968318530241)
              ·
                refine ⟨76741549993320726238897681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102322066657760968318530241 76741549993320726238897681)
                ·
                  refine ⟨57556162494990544679173261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76741549993320726238897681 57556162494990544679173261)
                  ·
                    refine ⟨21583560935621454254689973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57556162494990544679173261 21583560935621454254689973)
                    ·
                      refine ⟨2023458837714511336377185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21583560935621454254689973 2023458837714511336377185)
                      ·
                        rfl

theorem cell23_3940672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_3940672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940672 prefixEnd_3940672 := by exact prefixLift 3940672
  have htrace : WordTrace (prefixWord ++ tailWord_3940672) baseStart_3940672 baseEnd_3940672 := by
    simpa [prefixWord, tailWord_3940672, baseEnd_3940672] using wordTrace_append hprefix tailTrace_3940672
  have hstable : (prefixWord ++ tailWord_3940672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940672).length < 2 ^ (prefixWord ++ tailWord_3940672).sum := by decide
  have hdescent : baseEnd_3940672 < baseStart_3940672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940679 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 5, 4]
def baseStart_3940679 : Nat := 118140960795 + 3940679 * 2 ^ 59
def prefixEnd_3940679 : Nat := 4983230072969 + 3 ^ 40 * 3940679 * 2
def baseEnd_3940679 : Nat := 674487477359697602996551

theorem tailTrace_3940679 : CollatzResearch.WordTrace tailWord_3940679 prefixEnd_3940679 674487477359697602996551 := by
  unfold tailWord_3940679
  simp only [CollatzResearch.WordTrace]
  refine ⟨143728370890600472236897091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95818913927066981491264727 143728370890600472236897091)
  ·
    refine ⟨215592556335900708355345637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143728370890600472236897091 215592556335900708355345637)
    ·
      refine ⟨40423604312981382816627307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215592556335900708355345637 40423604312981382816627307)
      ·
        refine ⟨60635406469472074224940961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40423604312981382816627307 60635406469472074224940961)
        ·
          refine ⟨45476554852104055668705721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60635406469472074224940961 45476554852104055668705721)
          ·
            refine ⟨34107416139078041751529291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45476554852104055668705721 34107416139078041751529291)
            ·
              refine ⟨51161124208617062627293937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34107416139078041751529291 51161124208617062627293937)
              ·
                refine ⟨38370843156462796970470453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51161124208617062627293937 38370843156462796970470453)
                ·
                  refine ⟨3597266545918387215981605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38370843156462796970470453 3597266545918387215981605)
                  ·
                    refine ⟨674487477359697602996551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3597266545918387215981605 674487477359697602996551)
                    ·
                      rfl

theorem cell23_3940679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_3940679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940679 prefixEnd_3940679 := by exact prefixLift 3940679
  have htrace : WordTrace (prefixWord ++ tailWord_3940679) baseStart_3940679 baseEnd_3940679 := by
    simpa [prefixWord, tailWord_3940679, baseEnd_3940679] using wordTrace_append hprefix tailTrace_3940679
  have hstable : (prefixWord ++ tailWord_3940679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940679).length < 2 ^ (prefixWord ++ tailWord_3940679).sum := by decide
  have hdescent : baseEnd_3940679 < baseStart_3940679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940706 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3940706 : Nat := 118140960795 + 3940706 * 2 ^ 59
def prefixEnd_3940706 : Nat := 4983230072969 + 3 ^ 40 * 3940706 * 2
def baseEnd_3940706 : Nat := 2023476296056764203352029

theorem tailTrace_3940706 : CollatzResearch.WordTrace tailWord_3940706 prefixEnd_3940706 2023476296056764203352029 := by
  unfold tailWord_3940706
  simp only [CollatzResearch.WordTrace]
  refine ⟨35932338915375663962032493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95819570441001770565419981 35932338915375663962032493)
  ·
    refine ⟨13474627093265873985762185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35932338915375663962032493 13474627093265873985762185)
    ·
      refine ⟨10105970319949405489321639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13474627093265873985762185 10105970319949405489321639)
      ·
        refine ⟨15158955479924108233982459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10105970319949405489321639 15158955479924108233982459)
        ·
          refine ⟨22738433219886162350973689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15158955479924108233982459 22738433219886162350973689)
          ·
            refine ⟨17053824914914621763230267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22738433219886162350973689 17053824914914621763230267)
            ·
              refine ⟨25580737372371932644845401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17053824914914621763230267 25580737372371932644845401)
              ·
                refine ⟨19185553029278949483634051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25580737372371932644845401 19185553029278949483634051)
                ·
                  refine ⟨28778329543918424225451077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19185553029278949483634051 28778329543918424225451077)
                  ·
                    refine ⟨5395936789484704542272077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28778329543918424225451077 5395936789484704542272077)
                    ·
                      refine ⟨2023476296056764203352029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5395936789484704542272077 2023476296056764203352029)
                      ·
                        rfl

theorem cell23_3940706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3940706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940706 prefixEnd_3940706 := by exact prefixLift 3940706
  have htrace : WordTrace (prefixWord ++ tailWord_3940706) baseStart_3940706 baseEnd_3940706 := by
    simpa [prefixWord, tailWord_3940706, baseEnd_3940706] using wordTrace_append hprefix tailTrace_3940706
  have hstable : (prefixWord ++ tailWord_3940706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940706).length < 2 ^ (prefixWord ++ tailWord_3940706).sum := by decide
  have hdescent : baseEnd_3940706 < baseStart_3940706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940876 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_3940876 : Nat := 118140960795 + 3940876 * 2 ^ 59
def prefixEnd_3940876 : Nat := 4983230072969 + 3 ^ 40 * 3940876 * 2
def baseEnd_3940876 : Nat := 674521195922676179408749

theorem tailTrace_3940876 : CollatzResearch.WordTrace tailWord_3940876 prefixEnd_3940876 674521195922676179408749 := by
  unfold tailWord_3940876
  simp only [CollatzResearch.WordTrace]
  refine ⟨71867778035443387440909241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95823704047257849921212321 71867778035443387440909241)
  ·
    refine ⟨53900833526582540580681931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71867778035443387440909241 53900833526582540580681931)
    ·
      refine ⟨80851250289873810871022897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53900833526582540580681931 80851250289873810871022897)
      ·
        refine ⟨60638437717405358153267173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80851250289873810871022897 60638437717405358153267173)
        ·
          refine ⟨11369707072013504653737595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60638437717405358153267173 11369707072013504653737595)
          ·
            refine ⟨17054560608020256980606393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11369707072013504653737595 17054560608020256980606393)
            ·
              refine ⟨12790920456015192735454795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17054560608020256980606393 12790920456015192735454795)
              ·
                refine ⟨19186380684022789103182193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12790920456015192735454795 19186380684022789103182193)
                ·
                  refine ⟨14389785513017091827386645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19186380684022789103182193 14389785513017091827386645)
                  ·
                    refine ⟨674521195922676179408749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14389785513017091827386645 674521195922676179408749)
                    ·
                      rfl

theorem cell23_3940876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_3940876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940876 prefixEnd_3940876 := by exact prefixLift 3940876
  have htrace : WordTrace (prefixWord ++ tailWord_3940876) baseStart_3940876 baseEnd_3940876 := by
    simpa [prefixWord, tailWord_3940876, baseEnd_3940876] using wordTrace_append hprefix tailTrace_3940876
  have hstable : (prefixWord ++ tailWord_3940876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940876).length < 2 ^ (prefixWord ++ tailWord_3940876).sum := by decide
  have hdescent : baseEnd_3940876 < baseStart_3940876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940877 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3940877 : Nat := 118140960795 + 3940877 * 2 ^ 59
def prefixEnd_3940877 : Nat := 4983230072969 + 3 ^ 40 * 3940877 * 2
def baseEnd_3940877 : Nat := 2023564101248683034313743

theorem tailTrace_3940877 : CollatzResearch.WordTrace tailWord_3940877 prefixEnd_3940877 2023564101248683034313743 := by
  unfold tailWord_3940877
  simp only [CollatzResearch.WordTrace]
  refine ⟨143735592543883152052604885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95823728362588768035069923 143735592543883152052604885)
  ·
    refine ⟨3368802950247261376232927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 143735592543883152052604885 3368802950247261376232927)
    ·
      refine ⟨5053204425370892064349391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368802950247261376232927 5053204425370892064349391)
      ·
        refine ⟨7579806638056338096524087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053204425370892064349391 7579806638056338096524087)
        ·
          refine ⟨11369709957084507144786131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7579806638056338096524087 11369709957084507144786131)
          ·
            refine ⟨17054564935626760717179197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11369709957084507144786131 17054564935626760717179197)
            ·
              refine ⟨6395461850860035268942199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17054564935626760717179197 6395461850860035268942199)
              ·
                refine ⟨9593192776290052903413299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395461850860035268942199 9593192776290052903413299)
                ·
                  refine ⟨14389789164435079355119949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9593192776290052903413299 14389789164435079355119949)
                  ·
                    refine ⟨5396170936663154758169981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14389789164435079355119949 5396170936663154758169981)
                    ·
                      refine ⟨2023564101248683034313743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396170936663154758169981 2023564101248683034313743)
                      ·
                        rfl

theorem cell23_3940877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3940877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940877 prefixEnd_3940877 := by exact prefixLift 3940877
  have htrace : WordTrace (prefixWord ++ tailWord_3940877) baseStart_3940877 baseEnd_3940877 := by
    simpa [prefixWord, tailWord_3940877, baseEnd_3940877] using wordTrace_append hprefix tailTrace_3940877
  have hstable : (prefixWord ++ tailWord_3940877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940877).length < 2 ^ (prefixWord ++ tailWord_3940877).sum := by decide
  have hdescent : baseEnd_3940877 < baseStart_3940877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940946 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_3940946 : Nat := 118140960795 + 3940946 * 2 ^ 59
def prefixEnd_3940946 : Nat := 4983230072969 + 3 ^ 40 * 3940946 * 2
def baseEnd_3940946 : Nat := 2023599531413843264350925

theorem tailTrace_3940946 : CollatzResearch.WordTrace tailWord_3940946 prefixEnd_3940946 2023599531413843264350925 := by
  unfold tailWord_3940946
  simp only [CollatzResearch.WordTrace]
  refine ⟨35934527295158294209216673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95825406120422117891244461 35934527295158294209216673)
  ·
    refine ⟨26950895471368720656912505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35934527295158294209216673 26950895471368720656912505)
    ·
      refine ⟨20213171603526540492684379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26950895471368720656912505 20213171603526540492684379)
      ·
        refine ⟨30319757405289810739026569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20213171603526540492684379 30319757405289810739026569)
        ·
          refine ⟨22739818053967358054269927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30319757405289810739026569 22739818053967358054269927)
          ·
            refine ⟨34109727080951037081404891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22739818053967358054269927 34109727080951037081404891)
            ·
              refine ⟨51164590621426555622107337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34109727080951037081404891 51164590621426555622107337)
              ·
                refine ⟨38373442966069916716580503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51164590621426555622107337 38373442966069916716580503)
                ·
                  refine ⟨57560164449104875074870755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38373442966069916716580503 57560164449104875074870755)
                  ·
                    refine ⟨86340246673657312612306133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57560164449104875074870755 86340246673657312612306133)
                    ·
                      refine ⟨2023599531413843264350925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86340246673657312612306133 2023599531413843264350925)
                      ·
                        rfl

theorem cell23_3940946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_3940946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940946 prefixEnd_3940946 := by exact prefixLift 3940946
  have htrace : WordTrace (prefixWord ++ tailWord_3940946) baseStart_3940946 baseEnd_3940946 := by
    simpa [prefixWord, tailWord_3940946, baseEnd_3940946] using wordTrace_append hprefix tailTrace_3940946
  have hstable : (prefixWord ++ tailWord_3940946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940946).length < 2 ^ (prefixWord ++ tailWord_3940946).sum := by decide
  have hdescent : baseEnd_3940946 < baseStart_3940946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940993 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3940993 : Nat := 118140960795 + 3940993 * 2 ^ 59
def prefixEnd_3940993 : Nat := 4983230072969 + 3 ^ 40 * 3940993 * 2
def baseEnd_3940993 : Nat := 2023623665004604580463209

theorem tailTrace_3940993 : CollatzResearch.WordTrace tailWord_3940993 prefixEnd_3940993 2023623665004604580463209 := by
  unfold tailWord_3940993
  simp only [CollatzResearch.WordTrace]
  refine ⟨143739823411462903863827633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95826548940975269242551755 143739823411462903863827633)
  ·
    refine ⟨107804867558597177897870725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143739823411462903863827633 107804867558597177897870725)
    ·
      refine ⟨20213412667236970855850761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107804867558597177897870725 20213412667236970855850761)
      ·
        refine ⟨15160059500427728141888071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20213412667236970855850761 15160059500427728141888071)
        ·
          refine ⟨22740089250641592212832107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15160059500427728141888071 22740089250641592212832107)
          ·
            refine ⟨34110133875962388319248161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22740089250641592212832107 34110133875962388319248161)
            ·
              refine ⟨25582600406971791239436121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34110133875962388319248161 25582600406971791239436121)
              ·
                refine ⟨19186950305228843429577091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25582600406971791239436121 19186950305228843429577091)
                ·
                  refine ⟨28780425457843265144365637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19186950305228843429577091 28780425457843265144365637)
                  ·
                    refine ⟨5396329773345612214568557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28780425457843265144365637 5396329773345612214568557)
                    ·
                      refine ⟨2023623665004604580463209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396329773345612214568557 2023623665004604580463209)
                      ·
                        rfl

theorem cell23_3940993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3940993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3940993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3940993 prefixEnd_3940993 := by exact prefixLift 3940993
  have htrace : WordTrace (prefixWord ++ tailWord_3940993) baseStart_3940993 baseEnd_3940993 := by
    simpa [prefixWord, tailWord_3940993, baseEnd_3940993] using wordTrace_append hprefix tailTrace_3940993
  have hstable : (prefixWord ++ tailWord_3940993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940993).length < 2 ^ (prefixWord ++ tailWord_3940993).sum := by decide
  have hdescent : baseEnd_3940993 < baseStart_3940993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941010 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3941010 : Nat := 118140960795 + 3941010 * 2 ^ 59
def prefixEnd_3941010 : Nat := 4983230072969 + 3 ^ 40 * 3941010 * 2
def baseEnd_3941010 : Nat := 2023632394175731013950631

theorem tailTrace_3941010 : CollatzResearch.WordTrace tailWord_3941010 prefixEnd_3941010 2023632394175731013950631 := by
  unfold tailWord_3941010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35935110863100328941799121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95826962301600877178130989 35935110863100328941799121)
  ·
    refine ⟨26951333147325246706349341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35935110863100328941799121 26951333147325246706349341)
    ·
      refine ⟨10106749930246967514881003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26951333147325246706349341 10106749930246967514881003)
      ·
        refine ⟨15160124895370451272321505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106749930246967514881003 15160124895370451272321505)
        ·
          refine ⟨11370093671527838454241129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15160124895370451272321505 11370093671527838454241129)
          ·
            refine ⟨8527570253645878840680847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11370093671527838454241129 8527570253645878840680847)
            ·
              refine ⟨12791355380468818261021271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8527570253645878840680847 12791355380468818261021271)
              ·
                refine ⟨19187033070703227391531907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12791355380468818261021271 19187033070703227391531907)
                ·
                  refine ⟨28780549606054841087297861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19187033070703227391531907 28780549606054841087297861)
                  ·
                    refine ⟨5396353051135282703868349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28780549606054841087297861 5396353051135282703868349)
                    ·
                      refine ⟨2023632394175731013950631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396353051135282703868349 2023632394175731013950631)
                      ·
                        rfl

theorem cell23_3941010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3941010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941010 prefixEnd_3941010 := by exact prefixLift 3941010
  have htrace : WordTrace (prefixWord ++ tailWord_3941010) baseStart_3941010 baseEnd_3941010 := by
    simpa [prefixWord, tailWord_3941010, baseEnd_3941010] using wordTrace_append hprefix tailTrace_3941010
  have hstable : (prefixWord ++ tailWord_3941010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941010).length < 2 ^ (prefixWord ++ tailWord_3941010).sum := by decide
  have hdescent : baseEnd_3941010 < baseStart_3941010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941033 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 3, 5, 2]
def baseStart_3941033 : Nat := 118140960795 + 3941033 * 2 ^ 59
def prefixEnd_3941033 : Nat := 4983230072969 + 3 ^ 40 * 3941033 * 2
def baseEnd_3941033 : Nat := 2023644204230784423963025

theorem tailTrace_3941033 : CollatzResearch.WordTrace tailWord_3941033 prefixEnd_3941033 2023644204230784423963025 := by
  unfold tailWord_3941033
  simp only [CollatzResearch.WordTrace]
  refine ⟨143741282331317990695283753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95827521554211993796855835 143741282331317990695283753)
  ·
    refine ⟨107805961748488493021462815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143741282331317990695283753 107805961748488493021462815)
    ·
      refine ⟨161708942622732739532194223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107805961748488493021462815 161708942622732739532194223)
      ·
        refine ⟨242563413934099109298291335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161708942622732739532194223 242563413934099109298291335)
        ·
          refine ⟨363845120901148663947437003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242563413934099109298291335 363845120901148663947437003)
          ·
            refine ⟨545767681351722995921155505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363845120901148663947437003 545767681351722995921155505)
            ·
              refine ⟨409325761013792246940866629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545767681351722995921155505 409325761013792246940866629)
              ·
                refine ⟨76748580190086046301412493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409325761013792246940866629 76748580190086046301412493)
                ·
                  refine ⟨28780717571282267363029685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76748580190086046301412493 28780717571282267363029685)
                  ·
                    refine ⟨2698192272307712565284033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28780717571282267363029685 2698192272307712565284033)
                    ·
                      refine ⟨2023644204230784423963025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698192272307712565284033 2023644204230784423963025)
                      ·
                        rfl

theorem cell23_3941033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 5, 2].length) (baseStart_3941033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941033 prefixEnd_3941033 := by exact prefixLift 3941033
  have htrace : WordTrace (prefixWord ++ tailWord_3941033) baseStart_3941033 baseEnd_3941033 := by
    simpa [prefixWord, tailWord_3941033, baseEnd_3941033] using wordTrace_append hprefix tailTrace_3941033
  have hstable : (prefixWord ++ tailWord_3941033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941033).length < 2 ^ (prefixWord ++ tailWord_3941033).sum := by decide
  have hdescent : baseEnd_3941033 < baseStart_3941033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941034 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3941034 : Nat := 118140960795 + 3941034 * 2 ^ 59
def prefixEnd_3941034 : Nat := 4983230072969 + 3 ^ 40 * 3941034 * 2
def baseEnd_3941034 : Nat := 674548239237146306683507

theorem tailTrace_3941034 : CollatzResearch.WordTrace tailWord_3941034 prefixEnd_3941034 674548239237146306683507 := by
  unfold tailWord_3941034
  simp only [CollatzResearch.WordTrace]
  refine ⟨35935329701078591966517539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95827545869542911910713437 35935329701078591966517539)
  ·
    refine ⟨53902994551617887949776309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35935329701078591966517539 53902994551617887949776309)
    ·
      refine ⟨5053405739214176995291529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53902994551617887949776309 5053405739214176995291529)
      ·
        refine ⟨3790054304410632746468647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5053405739214176995291529 3790054304410632746468647)
        ·
          refine ⟨5685081456615949119702971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790054304410632746468647 5685081456615949119702971)
          ·
            refine ⟨8527622184923923679554457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685081456615949119702971 8527622184923923679554457)
            ·
              refine ⟨6395716638692942759665843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8527622184923923679554457 6395716638692942759665843)
              ·
                refine ⟨9593574958039414139498765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395716638692942759665843 9593574958039414139498765)
                ·
                  refine ⟨3597590609264780302312037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9593574958039414139498765 3597590609264780302312037)
                  ·
                    refine ⟨674548239237146306683507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3597590609264780302312037 674548239237146306683507)
                    ·
                      rfl

theorem cell23_3941034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3941034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941034 prefixEnd_3941034 := by exact prefixLift 3941034
  have htrace : WordTrace (prefixWord ++ tailWord_3941034) baseStart_3941034 baseEnd_3941034 := by
    simpa [prefixWord, tailWord_3941034, baseEnd_3941034] using wordTrace_append hprefix tailTrace_3941034
  have hstable : (prefixWord ++ tailWord_3941034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941034).length < 2 ^ (prefixWord ++ tailWord_3941034).sum := by decide
  have hdescent : baseEnd_3941034 < baseStart_3941034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941060 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3941060 : Nat := 118140960795 + 3941060 * 2 ^ 59
def prefixEnd_3941060 : Nat := 4983230072969 + 3 ^ 40 * 3941060 * 2
def baseEnd_3941060 : Nat := 674552689402818606108467

theorem tailTrace_3941060 : CollatzResearch.WordTrace tailWord_3941060 prefixEnd_3941060 674552689402818606108467 := by
  unfold tailWord_3941060
  simp only [CollatzResearch.WordTrace]
  refine ⟨71871133551110087153258317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95828178068146782871011089 71871133551110087153258317)
  ·
    refine ⟨26951675081666282682471869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71871133551110087153258317 26951675081666282682471869)
    ·
      refine ⟨10106878155624856005926951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26951675081666282682471869 10106878155624856005926951)
      ·
        refine ⟨15160317233437284008890427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106878155624856005926951 15160317233437284008890427)
        ·
          refine ⟨22740475850155926013335641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15160317233437284008890427 22740475850155926013335641)
          ·
            refine ⟨17055356887616944510001731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22740475850155926013335641 17055356887616944510001731)
            ·
              refine ⟨25583035331425416765002597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17055356887616944510001731 25583035331425416765002597)
              ·
                refine ⟨4796819124642265643437987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25583035331425416765002597 4796819124642265643437987)
                ·
                  refine ⟨7195228686963398465156981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796819124642265643437987 7195228686963398465156981)
                  ·
                    refine ⟨674552689402818606108467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7195228686963398465156981 674552689402818606108467)
                    ·
                      rfl

theorem cell23_3941060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3941060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941060 prefixEnd_3941060 := by exact prefixLift 3941060
  have htrace : WordTrace (prefixWord ++ tailWord_3941060) baseStart_3941060 baseEnd_3941060 := by
    simpa [prefixWord, tailWord_3941060, baseEnd_3941060] using wordTrace_append hprefix tailTrace_3941060
  have hstable : (prefixWord ++ tailWord_3941060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941060).length < 2 ^ (prefixWord ++ tailWord_3941060).sum := by decide
  have hdescent : baseEnd_3941060 < baseStart_3941060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941073 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 6, 4]
def baseStart_3941073 : Nat := 118140960795 + 3941073 * 2 ^ 59
def prefixEnd_3941073 : Nat := 4983230072969 + 3 ^ 40 * 3941073 * 2
def baseEnd_3941073 : Nat := 674554914485654755820947

theorem tailTrace_3941073 : CollatzResearch.WordTrace tailWord_3941073 prefixEnd_3941073 674554914485654755820947 := by
  unfold tailWord_3941073
  simp only [CollatzResearch.WordTrace]
  refine ⟨143742741251173077526739873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95828494167448718351159915 143742741251173077526739873)
  ·
    refine ⟨107807055938379808145054905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143742741251173077526739873 107807055938379808145054905)
    ·
      refine ⟨80855291953784856108791179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107807055938379808145054905 80855291953784856108791179)
      ·
        refine ⟨121282937930677284163186769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80855291953784856108791179 121282937930677284163186769)
        ·
          refine ⟨90962203448007963122390077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121282937930677284163186769 90962203448007963122390077)
          ·
            refine ⟨34110826293002986170896279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90962203448007963122390077 34110826293002986170896279)
            ·
              refine ⟨51166239439504479256344419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34110826293002986170896279 51166239439504479256344419)
              ·
                refine ⟨76749359159256718884516629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51166239439504479256344419 76749359159256718884516629)
                ·
                  refine ⟨3597626210590158697711717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76749359159256718884516629 3597626210590158697711717)
                  ·
                    refine ⟨674554914485654755820947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3597626210590158697711717 674554914485654755820947)
                    ·
                      rfl

theorem cell23_3941073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_3941073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941073 prefixEnd_3941073 := by exact prefixLift 3941073
  have htrace : WordTrace (prefixWord ++ tailWord_3941073) baseStart_3941073 baseEnd_3941073 := by
    simpa [prefixWord, tailWord_3941073, baseEnd_3941073] using wordTrace_append hprefix tailTrace_3941073
  have hstable : (prefixWord ++ tailWord_3941073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941073).length < 2 ^ (prefixWord ++ tailWord_3941073).sum := by decide
  have hdescent : baseEnd_3941073 < baseStart_3941073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941080 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_3941080 : Nat := 118140960795 + 3941080 * 2 ^ 59
def prefixEnd_3941080 : Nat := 4983230072969 + 3 ^ 40 * 3941080 * 2
def baseEnd_3941080 : Nat := 2023668337821545740075309

theorem tailTrace_3941080 : CollatzResearch.WordTrace tailWord_3941080 prefixEnd_3941080 2023668337821545740075309 := by
  unfold tailWord_3941080
  simp only [CollatzResearch.WordTrace]
  refine ⟨71871498281073858861122347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95828664374765145148163129 71871498281073858861122347)
  ·
    refine ⟨107807247421610788291683521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71871498281073858861122347 107807247421610788291683521)
    ·
      refine ⟨80855435566208091218762641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107807247421610788291683521 80855435566208091218762641)
      ·
        refine ⟨60641576674656068414071981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80855435566208091218762641 60641576674656068414071981)
        ·
          refine ⟨22740591252996025655276993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60641576674656068414071981 22740591252996025655276993)
          ·
            refine ⟨17055443439747019241457745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22740591252996025655276993 17055443439747019241457745)
            ·
              refine ⟨12791582579810264431093309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17055443439747019241457745 12791582579810264431093309)
              ·
                refine ⟨4796843467428849161659991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12791582579810264431093309 4796843467428849161659991)
                ·
                  refine ⟨7195265201143273742489987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796843467428849161659991 7195265201143273742489987)
                  ·
                    refine ⟨10792897801714910613734981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7195265201143273742489987 10792897801714910613734981)
                    ·
                      refine ⟨2023668337821545740075309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10792897801714910613734981 2023668337821545740075309)
                      ·
                        rfl

theorem cell23_3941080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_3941080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941080 prefixEnd_3941080 := by exact prefixLift 3941080
  have htrace : WordTrace (prefixWord ++ tailWord_3941080) baseStart_3941080 baseEnd_3941080 := by
    simpa [prefixWord, tailWord_3941080, baseEnd_3941080] using wordTrace_append hprefix tailTrace_3941080
  have hstable : (prefixWord ++ tailWord_3941080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941080).length < 2 ^ (prefixWord ++ tailWord_3941080).sum := by decide
  have hdescent : baseEnd_3941080 < baseStart_3941080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941084 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3941084 : Nat := 118140960795 + 3941084 * 2 ^ 59
def prefixEnd_3941084 : Nat := 4983230072969 + 3 ^ 40 * 3941084 * 2
def baseEnd_3941084 : Nat := 2023670391744163724425291

theorem tailTrace_3941084 : CollatzResearch.WordTrace tailWord_3941084 prefixEnd_3941084 2023670391744163724425291 := by
  unfold tailWord_3941084
  simp only [CollatzResearch.WordTrace]
  refine ⟨71871571227066613202695153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95828761636088817603593537 71871571227066613202695153)
  ·
    refine ⟨53903678420299959902021365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71871571227066613202695153 53903678420299959902021365)
    ·
      refine ⟨5053469851903121240814503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53903678420299959902021365 5053469851903121240814503)
      ·
        refine ⟨7580204777854681861221755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053469851903121240814503 7580204777854681861221755)
        ·
          refine ⟨11370307166782022791832633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7580204777854681861221755 11370307166782022791832633)
          ·
            refine ⟨8527730375086517093874475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11370307166782022791832633 8527730375086517093874475)
            ·
              refine ⟨12791595562629775640811713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8527730375086517093874475 12791595562629775640811713)
              ·
                refine ⟨9593696671972331730608785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12791595562629775640811713 9593696671972331730608785)
                ·
                  refine ⟨7195272503979248797956589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9593696671972331730608785 7195272503979248797956589)
                  ·
                    refine ⟨2698227188992218299233721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7195272503979248797956589 2698227188992218299233721)
                    ·
                      refine ⟨2023670391744163724425291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698227188992218299233721 2023670391744163724425291)
                      ·
                        rfl

theorem cell23_3941084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3941084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941084 prefixEnd_3941084 := by exact prefixLift 3941084
  have htrace : WordTrace (prefixWord ++ tailWord_3941084) baseStart_3941084 baseEnd_3941084 := by
    simpa [prefixWord, tailWord_3941084, baseEnd_3941084] using wordTrace_append hprefix tailTrace_3941084
  have hstable : (prefixWord ++ tailWord_3941084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941084).length < 2 ^ (prefixWord ++ tailWord_3941084).sum := by decide
  have hdescent : baseEnd_3941084 < baseStart_3941084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941091 : List Nat := [1, 1, 1, 7, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3941091 : Nat := 118140960795 + 3941091 * 2 ^ 59
def prefixEnd_3941091 : Nat := 4983230072969 + 3 ^ 40 * 3941091 * 2
def baseEnd_3941091 : Nat := 2023673986108745197037759

theorem tailTrace_3941091 : CollatzResearch.WordTrace tailWord_3941091 prefixEnd_3941091 2023673986108745197037759 := by
  unfold tailWord_3941091
  simp only [CollatzResearch.WordTrace]
  refine ⟨143743397765107866600895127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95828931843405244400596751 143743397765107866600895127)
  ·
    refine ⟨215615096647661799901342691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143743397765107866600895127 215615096647661799901342691)
    ·
      refine ⟨323422644971492699852014037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215615096647661799901342691 323422644971492699852014037)
      ·
        refine ⟨7580218241519360152781579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 323422644971492699852014037 7580218241519360152781579)
        ·
          refine ⟨11370327362279040229172369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7580218241519360152781579 11370327362279040229172369)
          ·
            refine ⟨8527745521709280171879277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11370327362279040229172369 8527745521709280171879277)
            ·
              refine ⟨3197904570640980064454729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8527745521709280171879277 3197904570640980064454729)
              ·
                refine ⟨2398428427980735048341047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197904570640980064454729 2398428427980735048341047)
                ·
                  refine ⟨3597642641971102572511571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398428427980735048341047 3597642641971102572511571)
                  ·
                    refine ⟨5396463962956653858767357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3597642641971102572511571 5396463962956653858767357)
                    ·
                      refine ⟨2023673986108745197037759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396463962956653858767357 2023673986108745197037759)
                      ·
                        rfl

theorem cell23_3941091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3941091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941091 prefixEnd_3941091 := by exact prefixLift 3941091
  have htrace : WordTrace (prefixWord ++ tailWord_3941091) baseStart_3941091 baseEnd_3941091 := by
    simpa [prefixWord, tailWord_3941091, baseEnd_3941091] using wordTrace_append hprefix tailTrace_3941091
  have hstable : (prefixWord ++ tailWord_3941091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941091).length < 2 ^ (prefixWord ++ tailWord_3941091).sum := by decide
  have hdescent : baseEnd_3941091 < baseStart_3941091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941093 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3941093 : Nat := 118140960795 + 3941093 * 2 ^ 59
def prefixEnd_3941093 : Nat := 4983230072969 + 3 ^ 40 * 3941093 * 2
def baseEnd_3941093 : Nat := 2023675013070054189212749

theorem tailTrace_3941093 : CollatzResearch.WordTrace tailWord_3941093 prefixEnd_3941093 2023675013070054189212749 := by
  unfold tailWord_3941093
  simp only [CollatzResearch.WordTrace]
  refine ⟨143743470711100620942467933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95828980474067080628311955 143743470711100620942467933)
  ·
    refine ⟨53903801516662732853425475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143743470711100620942467933 53903801516662732853425475)
    ·
      refine ⟨80855702274994099280138213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53903801516662732853425475 80855702274994099280138213)
      ·
        refine ⟨15160444176561393615025915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80855702274994099280138213 15160444176561393615025915)
        ·
          refine ⟨22740666264842090422538873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15160444176561393615025915 22740666264842090422538873)
          ·
            refine ⟨17055499698631567816904155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22740666264842090422538873 17055499698631567816904155)
            ·
              refine ⟨25583249547947351725356233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17055499698631567816904155 25583249547947351725356233)
              ·
                refine ⟨19187437160960513794017175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25583249547947351725356233 19187437160960513794017175)
                ·
                  refine ⟨28781155741440770691025763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19187437160960513794017175 28781155741440770691025763)
                  ·
                    refine ⟨43171733612161156036538645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28781155741440770691025763 43171733612161156036538645)
                    ·
                      refine ⟨2023675013070054189212749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43171733612161156036538645 2023675013070054189212749)
                      ·
                        rfl

theorem cell23_3941093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3941093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941093 prefixEnd_3941093 := by exact prefixLift 3941093
  have htrace : WordTrace (prefixWord ++ tailWord_3941093) baseStart_3941093 baseEnd_3941093 := by
    simpa [prefixWord, tailWord_3941093, baseEnd_3941093] using wordTrace_append hprefix tailTrace_3941093
  have hstable : (prefixWord ++ tailWord_3941093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941093).length < 2 ^ (prefixWord ++ tailWord_3941093).sum := by decide
  have hdescent : baseEnd_3941093 < baseStart_3941093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941097 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 3, 2, 2]
def baseStart_3941097 : Nat := 118140960795 + 3941097 * 2 ^ 59
def prefixEnd_3941097 : Nat := 4983230072969 + 3 ^ 40 * 3941097 * 2
def baseEnd_3941097 : Nat := 2023677066992672173562731

theorem tailTrace_3941097 : CollatzResearch.WordTrace tailWord_3941097 prefixEnd_3941097 2023677066992672173562731 := by
  unfold tailWord_3941097
  simp only [CollatzResearch.WordTrace]
  refine ⟨143743616603086129625613545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95829077735390753083742363 143743616603086129625613545)
  ·
    refine ⟨107807712452314597219210159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143743616603086129625613545 107807712452314597219210159)
    ·
      refine ⟨161711568678471895828815239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107807712452314597219210159 161711568678471895828815239)
      ·
        refine ⟨242567353017707843743222859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161711568678471895828815239 242567353017707843743222859)
        ·
          refine ⟨363851029526561765614834289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242567353017707843743222859 363851029526561765614834289)
          ·
            refine ⟨272888272144921324211125717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363851029526561765614834289 272888272144921324211125717)
            ·
              refine ⟨6395818878396593536198259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 272888272144921324211125717 6395818878396593536198259)
              ·
                refine ⟨9593728317594890304297389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6395818878396593536198259 9593728317594890304297389)
                ·
                  refine ⟨3597648119098083864111521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9593728317594890304297389 3597648119098083864111521)
                  ·
                    refine ⟨2698236089323562898083641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3597648119098083864111521 2698236089323562898083641)
                    ·
                      refine ⟨2023677066992672173562731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698236089323562898083641 2023677066992672173562731)
                      ·
                        rfl

theorem cell23_3941097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 2, 2].length) (baseStart_3941097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941097 prefixEnd_3941097 := by exact prefixLift 3941097
  have htrace : WordTrace (prefixWord ++ tailWord_3941097) baseStart_3941097 baseEnd_3941097 := by
    simpa [prefixWord, tailWord_3941097, baseEnd_3941097] using wordTrace_append hprefix tailTrace_3941097
  have hstable : (prefixWord ++ tailWord_3941097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941097).length < 2 ^ (prefixWord ++ tailWord_3941097).sum := by decide
  have hdescent : baseEnd_3941097 < baseStart_3941097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941103 : List Nat := [1, 1, 2, 1, 5, 3, 2, 8]
def baseStart_3941103 : Nat := 118140960795 + 3941103 * 2 ^ 59
def prefixEnd_3941103 : Nat := 4983230072969 + 3 ^ 40 * 3941103 * 2
def baseEnd_3941103 : Nat := 74951116588022190743989

theorem tailTrace_3941103 : CollatzResearch.WordTrace tailWord_3941103 prefixEnd_3941103 74951116588022190743989 := by
  unfold tailWord_3941103
  simp only [CollatzResearch.WordTrace]
  refine ⟨143743835441064392650331963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95829223627376261766887975 143743835441064392650331963)
  ·
    refine ⟨215615753161596588975497945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143743835441064392650331963 215615753161596588975497945)
    ·
      refine ⟨161711814871197441731623459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215615753161596588975497945 161711814871197441731623459)
      ·
        refine ⟨242567722306796162597435189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161711814871197441731623459 242567722306796162597435189)
        ·
          refine ⟨22740723966262140243509549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242567722306796162597435189 22740723966262140243509549)
          ·
            refine ⟨8527771487348302591316081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22740723966262140243509549 8527771487348302591316081)
            ·
              refine ⟨6395828615511226943487061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8527771487348302591316081 6395828615511226943487061)
              ·
                refine ⟨74951116588022190743989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6395828615511226943487061 74951116588022190743989)
                ·
                  rfl

theorem cell23_3941103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 8].length) (baseStart_3941103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941103 prefixEnd_3941103 := by exact prefixLift 3941103
  have htrace : WordTrace (prefixWord ++ tailWord_3941103) baseStart_3941103 baseEnd_3941103 := by
    simpa [prefixWord, tailWord_3941103, baseEnd_3941103] using wordTrace_append hprefix tailTrace_3941103
  have hstable : (prefixWord ++ tailWord_3941103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941103).length < 2 ^ (prefixWord ++ tailWord_3941103).sum := by decide
  have hdescent : baseEnd_3941103 < baseStart_3941103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941110 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3941110 : Nat := 118140960795 + 3941110 * 2 ^ 59
def prefixEnd_3941110 : Nat := 4983230072969 + 3 ^ 40 * 3941110 * 2
def baseEnd_3941110 : Nat := 2023683742241180622700171

theorem tailTrace_3941110 : CollatzResearch.WordTrace tailWord_3941110 prefixEnd_3941110 2023683742241180622700171 := by
  unfold tailWord_3941110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984005672002439552864799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95829393834692688563891189 8984005672002439552864799)
  ·
    refine ⟨13476008508003659329297199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8984005672002439552864799 13476008508003659329297199)
    ·
      refine ⟨20214012762005488993945799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13476008508003659329297199 20214012762005488993945799)
      ·
        refine ⟨30321019143008233490918699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20214012762005488993945799 30321019143008233490918699)
        ·
          refine ⟨45481528714512350236378049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30321019143008233490918699 45481528714512350236378049)
          ·
            refine ⟨34111146535884262677283537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45481528714512350236378049 34111146535884262677283537)
            ·
              refine ⟨25583359901913197007962653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34111146535884262677283537 25583359901913197007962653)
              ·
                refine ⟨9593759963217448877985995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25583359901913197007962653 9593759963217448877985995)
                ·
                  refine ⟨14390639944826173316978993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9593759963217448877985995 14390639944826173316978993)
                  ·
                    refine ⟨10792979958619629987734245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14390639944826173316978993 10792979958619629987734245)
                    ·
                      refine ⟨2023683742241180622700171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10792979958619629987734245 2023683742241180622700171)
                      ·
                        rfl

theorem cell23_3941110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3941110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941110 prefixEnd_3941110 := by exact prefixLift 3941110
  have htrace : WordTrace (prefixWord ++ tailWord_3941110) baseStart_3941110 baseEnd_3941110 := by
    simpa [prefixWord, tailWord_3941110, baseEnd_3941110] using wordTrace_append hprefix tailTrace_3941110
  have hstable : (prefixWord ++ tailWord_3941110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941110).length < 2 ^ (prefixWord ++ tailWord_3941110).sum := by decide
  have hdescent : baseEnd_3941110 < baseStart_3941110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941113 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 3]
def baseStart_3941113 : Nat := 118140960795 + 3941113 * 2 ^ 59
def prefixEnd_3941113 : Nat := 4983230072969 + 3 ^ 40 * 3941113 * 2
def baseEnd_3941113 : Nat := 2023685282683144110962657

theorem tailTrace_3941113 : CollatzResearch.WordTrace tailWord_3941113 prefixEnd_3941113 2023685282683144110962657 := by
  unfold tailWord_3941113
  simp only [CollatzResearch.WordTrace]
  refine ⟨143744200171028164358195993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95829466780685442905463995 143744200171028164358195993)
  ·
    refine ⟨107808150128271123268646995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143744200171028164358195993 107808150128271123268646995)
    ·
      refine ⟨161712225192406684902970493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107808150128271123268646995 161712225192406684902970493)
      ·
        refine ⟨60642084447152506838613935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161712225192406684902970493 60642084447152506838613935)
        ·
          refine ⟨90963126670728760257920903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60642084447152506838613935 90963126670728760257920903)
          ·
            refine ⟨136444690006093140386881355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90963126670728760257920903 136444690006093140386881355)
            ·
              refine ⟨204667035009139710580322033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136444690006093140386881355 204667035009139710580322033)
              ·
                refine ⟨153500276256854782935241525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204667035009139710580322033 153500276256854782935241525)
                ·
                  refine ⟨14390650899080135900178893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153500276256854782935241525 14390650899080135900178893)
                  ·
                    refine ⟨5396494087155050962567085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14390650899080135900178893 5396494087155050962567085)
                    ·
                      refine ⟨2023685282683144110962657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396494087155050962567085 2023685282683144110962657)
                      ·
                        rfl

theorem cell23_3941113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_3941113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941113 prefixEnd_3941113 := by exact prefixLift 3941113
  have htrace : WordTrace (prefixWord ++ tailWord_3941113) baseStart_3941113 baseEnd_3941113 := by
    simpa [prefixWord, tailWord_3941113, baseEnd_3941113] using wordTrace_append hprefix tailTrace_3941113
  have hstable : (prefixWord ++ tailWord_3941113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941113).length < 2 ^ (prefixWord ++ tailWord_3941113).sum := by decide
  have hdescent : baseEnd_3941113 < baseStart_3941113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941130 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3941130 : Nat := 118140960795 + 3941130 * 2 ^ 59
def prefixEnd_3941130 : Nat := 4983230072969 + 3 ^ 40 * 3941130 * 2
def baseEnd_3941130 : Nat := 2023694011854270544450079

theorem tailTrace_3941130 : CollatzResearch.WordTrace tailWord_3941130 prefixEnd_3941130 2023694011854270544450079 := by
  unfold tailWord_3941130
  simp only [CollatzResearch.WordTrace]
  refine ⟨35936205052991644065391211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95829880141311050841043229 35936205052991644065391211)
  ·
    refine ⟨53904307579487466098086817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35936205052991644065391211 53904307579487466098086817)
    ·
      refine ⟨40428230684615599573565113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53904307579487466098086817 40428230684615599573565113)
      ·
        refine ⟨30321173013461699680173835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40428230684615599573565113 30321173013461699680173835)
        ·
          refine ⟨45481759520192549520260753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30321173013461699680173835 45481759520192549520260753)
          ·
            refine ⟨34111319640144412140195565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45481759520192549520260753 34111319640144412140195565)
            ·
              refine ⟨12791744865054154552573337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34111319640144412140195565 12791744865054154552573337)
              ·
                refine ⟨9593808648790615914430003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12791744865054154552573337 9593808648790615914430003)
                ·
                  refine ⟨14390712973185923871645005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9593808648790615914430003 14390712973185923871645005)
                  ·
                    refine ⟨5396517364944721451866877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14390712973185923871645005 5396517364944721451866877)
                    ·
                      refine ⟨2023694011854270544450079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396517364944721451866877 2023694011854270544450079)
                      ·
                        rfl

theorem cell23_3941130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3941130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941130 prefixEnd_3941130 := by exact prefixLift 3941130
  have htrace : WordTrace (prefixWord ++ tailWord_3941130) baseStart_3941130 baseEnd_3941130 := by
    simpa [prefixWord, tailWord_3941130, baseEnd_3941130] using wordTrace_append hprefix tailTrace_3941130
  have hstable : (prefixWord ++ tailWord_3941130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941130).length < 2 ^ (prefixWord ++ tailWord_3941130).sum := by decide
  have hdescent : baseEnd_3941130 < baseStart_3941130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941148 : List Nat := [2, 2, 3, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_3941148 : Nat := 118140960795 + 3941148 * 2 ^ 59
def prefixEnd_3941148 : Nat := 4983230072969 + 3 ^ 40 * 3941148 * 2
def baseEnd_3941148 : Nat := 2023703254506051474024997

theorem tailTrace_3941148 : CollatzResearch.WordTrace tailWord_3941148 prefixEnd_3941148 2023703254506051474024997 := by
  unfold tailWord_3941148
  simp only [CollatzResearch.WordTrace]
  refine ⟨71872738362950682667860049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95830317817267576890480065 71872738362950682667860049)
  ·
    refine ⟨53904553772213012000895037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71872738362950682667860049 53904553772213012000895037)
    ·
      refine ⟨20214207664579879500335639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53904553772213012000895037 20214207664579879500335639)
      ·
        refine ⟨30321311496869819250503459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20214207664579879500335639 30321311496869819250503459)
        ·
          refine ⟨45481967245304728875755189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30321311496869819250503459 45481967245304728875755189)
          ·
            refine ⟨4263934429247318332102049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45481967245304728875755189 4263934429247318332102049)
            ·
              refine ⟨3197950821935488749076537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4263934429247318332102049 3197950821935488749076537)
              ·
                refine ⟨2398463116451616561807403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197950821935488749076537 2398463116451616561807403)
                ·
                  refine ⟨3597694674677424842711105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398463116451616561807403 3597694674677424842711105)
                  ·
                    refine ⟨2698271006008068632033329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3597694674677424842711105 2698271006008068632033329)
                    ·
                      refine ⟨2023703254506051474024997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698271006008068632033329 2023703254506051474024997)
                      ·
                        rfl

theorem cell23_3941148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_3941148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941148 prefixEnd_3941148 := by exact prefixLift 3941148
  have htrace : WordTrace (prefixWord ++ tailWord_3941148) baseStart_3941148 baseEnd_3941148 := by
    simpa [prefixWord, tailWord_3941148, baseEnd_3941148] using wordTrace_append hprefix tailTrace_3941148
  have hstable : (prefixWord ++ tailWord_3941148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941148).length < 2 ^ (prefixWord ++ tailWord_3941148).sum := by decide
  have hdescent : baseEnd_3941148 < baseStart_3941148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941153 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3941153 : Nat := 118140960795 + 3941153 * 2 ^ 59
def prefixEnd_3941153 : Nat := 4983230072969 + 3 ^ 40 * 3941153 * 2
def baseEnd_3941153 : Nat := 2023705821909323954462473

theorem tailTrace_3941153 : CollatzResearch.WordTrace tailWord_3941153 prefixEnd_3941153 2023705821909323954462473 := by
  unfold tailWord_3941153
  simp only [CollatzResearch.WordTrace]
  refine ⟨143745659090883251189652113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95830439393922167459768075 143745659090883251189652113)
  ·
    refine ⟨107809244318162438392239085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143745659090883251189652113 107809244318162438392239085)
    ·
      refine ⟨40428466619310914397089657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107809244318162438392239085 40428466619310914397089657)
      ·
        refine ⟨30321349964483185797817243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40428466619310914397089657 30321349964483185797817243)
        ·
          refine ⟨45482024946724778696725865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30321349964483185797817243 45482024946724778696725865)
          ·
            refine ⟨34111518710043584022544399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45482024946724778696725865 34111518710043584022544399)
            ·
              refine ⟨51167278065065376033816599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34111518710043584022544399 51167278065065376033816599)
              ·
                refine ⟨76750917097598064050724899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51167278065065376033816599 76750917097598064050724899)
                ·
                  refine ⟨115126375646397096076087349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76750917097598064050724899 115126375646397096076087349)
                  ·
                    refine ⟨10793097716849727757133189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115126375646397096076087349 10793097716849727757133189)
                    ·
                      refine ⟨2023705821909323954462473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10793097716849727757133189 2023705821909323954462473)
                      ·
                        rfl

theorem cell23_3941153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3941153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941153 prefixEnd_3941153 := by exact prefixLift 3941153
  have htrace : WordTrace (prefixWord ++ tailWord_3941153) baseStart_3941153 baseEnd_3941153 := by
    simpa [prefixWord, tailWord_3941153, baseEnd_3941153] using wordTrace_append hprefix tailTrace_3941153
  have hstable : (prefixWord ++ tailWord_3941153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941153).length < 2 ^ (prefixWord ++ tailWord_3941153).sum := by decide
  have hdescent : baseEnd_3941153 < baseStart_3941153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941187 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 4, 2, 2]
def baseStart_3941187 : Nat := 118140960795 + 3941187 * 2 ^ 59
def prefixEnd_3941187 : Nat := 4983230072969 + 3 ^ 40 * 3941187 * 2
def baseEnd_3941187 : Nat := 2023723280251576821437317

theorem tailTrace_3941187 : CollatzResearch.WordTrace tailWord_3941187 prefixEnd_3941187 2023723280251576821437317 := by
  unfold tailWord_3941187
  simp only [CollatzResearch.WordTrace]
  refine ⟨143746899172760074996389815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95831266115173383330926543 143746899172760074996389815)
  ·
    refine ⟨215620348759140112494584723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143746899172760074996389815 215620348759140112494584723)
    ·
      refine ⟨323430523138710168741877085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215620348759140112494584723 323430523138710168741877085)
      ·
        refine ⟨121286446177016313278203907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323430523138710168741877085 121286446177016313278203907)
        ·
          refine ⟨181929669265524469917305861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121286446177016313278203907 181929669265524469917305861)
          ·
            refine ⟨34111812987285838109494849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181929669265524469917305861 34111812987285838109494849)
            ·
              refine ⟨25583859740464378582121137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34111812987285838109494849 25583859740464378582121137)
              ·
                refine ⟨19187894805348283936590853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25583859740464378582121137 19187894805348283936590853)
                ·
                  refine ⟨3597730276002803238110785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19187894805348283936590853 3597730276002803238110785)
                  ·
                    refine ⟨2698297707002102428583089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3597730276002803238110785 2698297707002102428583089)
                    ·
                      refine ⟨2023723280251576821437317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698297707002102428583089 2023723280251576821437317)
                      ·
                        rfl

theorem cell23_3941187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_3941187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941187 prefixEnd_3941187 := by exact prefixLift 3941187
  have htrace : WordTrace (prefixWord ++ tailWord_3941187) baseStart_3941187 baseEnd_3941187 := by
    simpa [prefixWord, tailWord_3941187, baseEnd_3941187] using wordTrace_append hprefix tailTrace_3941187
  have hstable : (prefixWord ++ tailWord_3941187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941187).length < 2 ^ (prefixWord ++ tailWord_3941187).sum := by decide
  have hdescent : baseEnd_3941187 < baseStart_3941187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941210 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 7]
def baseStart_3941210 : Nat := 118140960795 + 3941210 * 2 ^ 59
def prefixEnd_3941210 : Nat := 4983230072969 + 3 ^ 40 * 3941210 * 2
def baseEnd_3941210 : Nat := 224859454478514470161079

theorem tailTrace_3941210 : CollatzResearch.WordTrace tailWord_3941210 prefixEnd_3941210 224859454478514470161079 := by
  unfold tailWord_3941210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35936934512919187481119271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95831825367784499949651389 35936934512919187481119271)
  ·
    refine ⟨53905401769378781221678907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35936934512919187481119271 53905401769378781221678907)
    ·
      refine ⟨80858102654068171832518361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53905401769378781221678907 80858102654068171832518361)
      ·
        refine ⟨60643576990551128874388771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80858102654068171832518361 60643576990551128874388771)
        ·
          refine ⟨90965365485826693311583157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60643576990551128874388771 90965365485826693311583157)
          ·
            refine ⟨8528003014296252497960921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90965365485826693311583157 8528003014296252497960921)
            ·
              refine ⟨6396002260722189373470691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8528003014296252497960921 6396002260722189373470691)
              ·
                refine ⟨9594003391083284060206037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6396002260722189373470691 9594003391083284060206037)
                ·
                  refine ⟨224859454478514470161079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9594003391083284060206037 224859454478514470161079)
                  ·
                    rfl

theorem cell23_3941210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_3941210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941210 prefixEnd_3941210 := by exact prefixLift 3941210
  have htrace : WordTrace (prefixWord ++ tailWord_3941210) baseStart_3941210 baseEnd_3941210 := by
    simpa [prefixWord, tailWord_3941210, baseEnd_3941210] using wordTrace_append hprefix tailTrace_3941210
  have hstable : (prefixWord ++ tailWord_3941210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941210).length < 2 ^ (prefixWord ++ tailWord_3941210).sum := by decide
  have hdescent : baseEnd_3941210 < baseStart_3941210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941260 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_3941260 : Nat := 118140960795 + 3941260 * 2 ^ 59
def prefixEnd_3941260 : Nat := 4983230072969 + 3 ^ 40 * 3941260 * 2
def baseEnd_3941260 : Nat := 2023760764339355035824481

theorem tailTrace_3941260 : CollatzResearch.WordTrace tailWord_3941260 prefixEnd_3941260 2023760764339355035824481 := by
  unfold tailWord_3941260
  simp only [CollatzResearch.WordTrace]
  refine ⟨71874780850747804231898617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95833041134330405642531489 71874780850747804231898617)
  ·
    refine ⟨53906085638060853173923963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71874780850747804231898617 53906085638060853173923963)
    ·
      refine ⟨80859128457091279760885945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53906085638060853173923963 80859128457091279760885945)
      ·
        refine ⟨60644346342818459820664459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80859128457091279760885945 60644346342818459820664459)
        ·
          refine ⟨90966519514227689730996689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60644346342818459820664459 90966519514227689730996689)
          ·
            refine ⟨68224889635670767298247517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90966519514227689730996689 68224889635670767298247517)
            ·
              refine ⟨25584333613376537736842819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68224889635670767298247517 25584333613376537736842819)
              ·
                refine ⟨38376500420064806605264229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25584333613376537736842819 38376500420064806605264229)
                ·
                  refine ⟨7195593828762151238487043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38376500420064806605264229 7195593828762151238487043)
                  ·
                    refine ⟨10793390743143226857730565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7195593828762151238487043 10793390743143226857730565)
                    ·
                      refine ⟨2023760764339355035824481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10793390743143226857730565 2023760764339355035824481)
                      ·
                        rfl

theorem cell23_3941260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_3941260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941260 prefixEnd_3941260 := by exact prefixLift 3941260
  have htrace : WordTrace (prefixWord ++ tailWord_3941260) baseStart_3941260 baseEnd_3941260 := by
    simpa [prefixWord, tailWord_3941260, baseEnd_3941260] using wordTrace_append hprefix tailTrace_3941260
  have hstable : (prefixWord ++ tailWord_3941260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941260).length < 2 ^ (prefixWord ++ tailWord_3941260).sum := by decide
  have hdescent : baseEnd_3941260 < baseStart_3941260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941277 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_3941277 : Nat := 118140960795 + 3941277 * 2 ^ 59
def prefixEnd_3941277 : Nat := 4983230072969 + 3 ^ 40 * 3941277 * 2
def baseEnd_3941277 : Nat := 2023769493510481469311903

theorem tailTrace_3941277 : CollatzResearch.WordTrace tailWord_3941277 prefixEnd_3941277 2023769493510481469311903 := by
  unfold tailWord_3941277
  simp only [CollatzResearch.WordTrace]
  refine ⟨143750181742434020367166085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95833454494956013578110723 143750181742434020367166085)
  ·
    refine ⟨26953159076706378818843641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143750181742434020367166085 26953159076706378818843641)
    ·
      refine ⟨20214869307529784114132731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26953159076706378818843641 20214869307529784114132731)
      ·
        refine ⟨30322303961294676171199097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20214869307529784114132731 30322303961294676171199097)
        ·
          refine ⟨22741727970971007128399323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30322303961294676171199097 22741727970971007128399323)
          ·
            refine ⟨34112591956456510692598985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22741727970971007128399323 34112591956456510692598985)
            ·
              refine ⟨25584443967342383019449239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34112591956456510692598985 25584443967342383019449239)
              ·
                refine ⟨38376665951013574529173859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25584443967342383019449239 38376665951013574529173859)
                ·
                  refine ⟨57564998926520361793760789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38376665951013574529173859 57564998926520361793760789)
                  ·
                    refine ⟨2698359324680641959082537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57564998926520361793760789 2698359324680641959082537)
                    ·
                      refine ⟨2023769493510481469311903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698359324680641959082537 2023769493510481469311903)
                      ·
                        rfl

theorem cell23_3941277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_3941277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941277 prefixEnd_3941277 := by exact prefixLift 3941277
  have htrace : WordTrace (prefixWord ++ tailWord_3941277) baseStart_3941277 baseEnd_3941277 := by
    simpa [prefixWord, tailWord_3941277, baseEnd_3941277] using wordTrace_append hprefix tailTrace_3941277
  have hstable : (prefixWord ++ tailWord_3941277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941277).length < 2 ^ (prefixWord ++ tailWord_3941277).sum := by decide
  have hdescent : baseEnd_3941277 < baseStart_3941277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941280 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3]
def baseStart_3941280 : Nat := 118140960795 + 3941280 * 2 ^ 59
def prefixEnd_3941280 : Nat := 4983230072969 + 3 ^ 40 * 3941280 * 2
def baseEnd_3941280 : Nat := 2023771033952444957574389

theorem tailTrace_3941280 : CollatzResearch.WordTrace tailWord_3941280 prefixEnd_3941280 2023771033952444957574389 := by
  unfold tailWord_3941280
  simp only [CollatzResearch.WordTrace]
  refine ⟨71875145580711575939762647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95833527440948767919683529 71875145580711575939762647)
  ·
    refine ⟨107812718371067363909643971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71875145580711575939762647 107812718371067363909643971)
    ·
      refine ⟨161719077556601045864465957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107812718371067363909643971 161719077556601045864465957)
      ·
        refine ⟨30322327041862696099587367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161719077556601045864465957 30322327041862696099587367)
        ·
          refine ⟨45483490562794044149381051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30322327041862696099587367 45483490562794044149381051)
          ·
            refine ⟨68225235844191066224071577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45483490562794044149381051 68225235844191066224071577)
            ·
              refine ⟨51168926883143299668053683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68225235844191066224071577 51168926883143299668053683)
              ·
                refine ⟨76753390324714949502080525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51168926883143299668053683 76753390324714949502080525)
                ·
                  refine ⟨28782521371768106063280197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76753390324714949502080525 28782521371768106063280197)
                  ·
                    refine ⟨5396722757206519886865037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28782521371768106063280197 5396722757206519886865037)
                    ·
                      refine ⟨2023771033952444957574389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396722757206519886865037 2023771033952444957574389)
                      ·
                        rfl

theorem cell23_3941280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_3941280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941280 prefixEnd_3941280 := by exact prefixLift 3941280
  have htrace : WordTrace (prefixWord ++ tailWord_3941280) baseStart_3941280 baseEnd_3941280 := by
    simpa [prefixWord, tailWord_3941280, baseEnd_3941280] using wordTrace_append hprefix tailTrace_3941280
  have hstable : (prefixWord ++ tailWord_3941280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941280).length < 2 ^ (prefixWord ++ tailWord_3941280).sum := by decide
  have hdescent : baseEnd_3941280 < baseStart_3941280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941334 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3941334 : Nat := 118140960795 + 3941334 * 2 ^ 59
def prefixEnd_3941334 : Nat := 4983230072969 + 3 ^ 40 * 3941334 * 2
def baseEnd_3941334 : Nat := 224866529100865305144349

theorem tailTrace_3941334 : CollatzResearch.WordTrace tailWord_3941334 prefixEnd_3941334 224866529100865305144349 := by
  unfold tailWord_3941334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984516293951719943874441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95834840468818346067994037 8984516293951719943874441)
  ·
    refine ⟨6738387220463789957905831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8984516293951719943874441 6738387220463789957905831)
    ·
      refine ⟨10107580830695684936858747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738387220463789957905831 10107580830695684936858747)
      ·
        refine ⟨15161371246043527405288121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10107580830695684936858747 15161371246043527405288121)
        ·
          refine ⟨11371028434532645553966091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15161371246043527405288121 11371028434532645553966091)
          ·
            refine ⟨17056542651798968330949137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11371028434532645553966091 17056542651798968330949137)
            ·
              refine ⟨12792406988849226248211853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17056542651798968330949137 12792406988849226248211853)
              ·
                refine ⟨4797152620818459843079445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12792406988849226248211853 4797152620818459843079445)
                ·
                  refine ⟨224866529100865305144349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4797152620818459843079445 224866529100865305144349)
                  ·
                    rfl

theorem cell23_3941334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3941334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941334 prefixEnd_3941334 := by exact prefixLift 3941334
  have htrace : WordTrace (prefixWord ++ tailWord_3941334) baseStart_3941334 baseEnd_3941334 := by
    simpa [prefixWord, tailWord_3941334, baseEnd_3941334] using wordTrace_append hprefix tailTrace_3941334
  have hstable : (prefixWord ++ tailWord_3941334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941334).length < 2 ^ (prefixWord ++ tailWord_3941334).sum := by decide
  have hdescent : baseEnd_3941334 < baseStart_3941334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941347 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 1, 5]
def baseStart_3941347 : Nat := 118140960795 + 3941347 * 2 ^ 59
def prefixEnd_3941347 : Nat := 4983230072969 + 3 ^ 40 * 3941347 * 2
def baseEnd_3941347 : Nat := 674601812385432065145527

theorem tailTrace_3941347 : CollatzResearch.WordTrace tailWord_3941347 prefixEnd_3941347 674601812385432065145527 := by
  unfold tailWord_3941347
  simp only [CollatzResearch.WordTrace]
  refine ⟨143752734852180422322214295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95835156568120281548142863 143752734852180422322214295)
  ·
    refine ⟨215629102278270633483321443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143752734852180422322214295 215629102278270633483321443)
    ·
      refine ⟨323443653417405950224982165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215629102278270633483321443 323443653417405950224982165)
      ·
        refine ⟨15161421253940903916796039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323443653417405950224982165 15161421253940903916796039)
        ·
          refine ⟨22742131880911355875194059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15161421253940903916796039 22742131880911355875194059)
          ·
            refine ⟨34113197821367033812791089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22742131880911355875194059 34113197821367033812791089)
            ·
              refine ⟨25584898366025275359593317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34113197821367033812791089 25584898366025275359593317)
              ·
                refine ⟨4797168443629739129923747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25584898366025275359593317 4797168443629739129923747)
                ·
                  refine ⟨7195752665444608694885621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797168443629739129923747 7195752665444608694885621)
                  ·
                    refine ⟨674601812385432065145527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7195752665444608694885621 674601812385432065145527)
                    ·
                      rfl

theorem cell23_3941347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 5].length) (baseStart_3941347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941347 prefixEnd_3941347 := by exact prefixLift 3941347
  have htrace : WordTrace (prefixWord ++ tailWord_3941347) baseStart_3941347 baseEnd_3941347 := by
    simpa [prefixWord, tailWord_3941347, baseEnd_3941347] using wordTrace_append hprefix tailTrace_3941347
  have hstable : (prefixWord ++ tailWord_3941347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941347).length < 2 ^ (prefixWord ++ tailWord_3941347).sum := by decide
  have hdescent : baseEnd_3941347 < baseStart_3941347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941354 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_3941354 : Nat := 118140960795 + 3941354 * 2 ^ 59
def prefixEnd_3941354 : Nat := 4983230072969 + 3 ^ 40 * 3941354 * 2
def baseEnd_3941354 : Nat := 2023809031520877668049049

theorem tailTrace_3941354 : CollatzResearch.WordTrace tailWord_3941354 prefixEnd_3941354 2023809031520877668049049 := by
  unfold tailWord_3941354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35938247540788765629429779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95835326775436708345146077 35938247540788765629429779)
  ·
    refine ⟨53907371311183148444144669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35938247540788765629429779 53907371311183148444144669)
    ·
      refine ⟨20215264241693680666554251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53907371311183148444144669 20215264241693680666554251)
      ·
        refine ⟨30322896362540520999831377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20215264241693680666554251 30322896362540520999831377)
        ·
          refine ⟨22742172271905390749873533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30322896362540520999831377 22742172271905390749873533)
          ·
            refine ⟨8528314601964521531202575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22742172271905390749873533 8528314601964521531202575)
            ·
              refine ⟨12792471902946782296803863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8528314601964521531202575 12792471902946782296803863)
              ·
                refine ⟨19188707854420173445205795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12792471902946782296803863 19188707854420173445205795)
                ·
                  refine ⟨28783061781630260167808693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19188707854420173445205795 28783061781630260167808693)
                  ·
                    refine ⟨2698412042027836890732065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28783061781630260167808693 2698412042027836890732065)
                    ·
                      refine ⟨2023809031520877668049049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698412042027836890732065 2023809031520877668049049)
                      ·
                        rfl

theorem cell23_3941354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_3941354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941354 prefixEnd_3941354 := by exact prefixLift 3941354
  have htrace : WordTrace (prefixWord ++ tailWord_3941354) baseStart_3941354 baseEnd_3941354 := by
    simpa [prefixWord, tailWord_3941354, baseEnd_3941354] using wordTrace_append hprefix tailTrace_3941354
  have hstable : (prefixWord ++ tailWord_3941354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941354).length < 2 ^ (prefixWord ++ tailWord_3941354).sum := by decide
  have hdescent : baseEnd_3941354 < baseStart_3941354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941361 : List Nat := [1, 2, 2, 2, 4, 1, 1, 5, 1, 1, 3]
def baseStart_3941361 : Nat := 118140960795 + 3941361 * 2 ^ 59
def prefixEnd_3941361 : Nat := 4983230072969 + 3 ^ 40 * 3941361 * 2
def baseEnd_3941361 : Nat := 2023812625885459140661517

theorem tailTrace_3941361 : CollatzResearch.WordTrace tailWord_3941361 prefixEnd_3941361 2023812625885459140661517 := by
  unfold tailWord_3941361
  simp only [CollatzResearch.WordTrace]
  refine ⟨143753245474129702713223937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95835496982753135142149291 143753245474129702713223937)
  ·
    refine ⟨107814934105597277034917953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143753245474129702713223937 107814934105597277034917953)
    ·
      refine ⟨80861200579197957776188465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107814934105597277034917953 80861200579197957776188465)
      ·
        refine ⟨60645900434398468332141349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80861200579197957776188465 60645900434398468332141349)
        ·
          refine ⟨11371106331449712812276503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60645900434398468332141349 11371106331449712812276503)
          ·
            refine ⟨17056659497174569218414755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11371106331449712812276503 17056659497174569218414755)
            ·
              refine ⟨25584989245761853827622133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17056659497174569218414755 25584989245761853827622133)
              ·
                refine ⟨2398592741790173796339575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25584989245761853827622133 2398592741790173796339575)
                ·
                  refine ⟨3597889112685260694509363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398592741790173796339575 3597889112685260694509363)
                  ·
                    refine ⟨5396833669027891041764045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3597889112685260694509363 5396833669027891041764045)
                    ·
                      refine ⟨2023812625885459140661517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396833669027891041764045 2023812625885459140661517)
                      ·
                        rfl

theorem cell23_3941361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_3941361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941361 prefixEnd_3941361 := by exact prefixLift 3941361
  have htrace : WordTrace (prefixWord ++ tailWord_3941361) baseStart_3941361 baseEnd_3941361 := by
    simpa [prefixWord, tailWord_3941361, baseEnd_3941361] using wordTrace_append hprefix tailTrace_3941361
  have hstable : (prefixWord ++ tailWord_3941361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941361).length < 2 ^ (prefixWord ++ tailWord_3941361).sum := by decide
  have hdescent : baseEnd_3941361 < baseStart_3941361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941370 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_3941370 : Nat := 118140960795 + 3941370 * 2 ^ 59
def prefixEnd_3941370 : Nat := 4983230072969 + 3 ^ 40 * 3941370 * 2
def baseEnd_3941370 : Nat := 2023817247211349605448975

theorem tailTrace_3941370 : CollatzResearch.WordTrace tailWord_3941370 prefixEnd_3941370 2023817247211349605448975 := by
  unfold tailWord_3941370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35938393432774274312575391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95835715820731398166867709 35938393432774274312575391)
  ·
    refine ⟨53907590149161411468863087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35938393432774274312575391 53907590149161411468863087)
    ·
      refine ⟨80861385223742117203294631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53907590149161411468863087 80861385223742117203294631)
      ·
        refine ⟨121292077835613175804941947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80861385223742117203294631 121292077835613175804941947)
        ·
          refine ⟨181938116753419763707412921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121292077835613175804941947 181938116753419763707412921)
          ·
            refine ⟨136453587565064822780559691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181938116753419763707412921 136453587565064822780559691)
            ·
              refine ⟨204680381347597234170839537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136453587565064822780559691 204680381347597234170839537)
              ·
                refine ⟨153510286010697925628129653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204680381347597234170839537 153510286010697925628129653)
                ·
                  refine ⟨14391589313502930527637155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153510286010697925628129653 14391589313502930527637155)
                  ·
                    refine ⟨21587383970254395791455733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14391589313502930527637155 21587383970254395791455733)
                    ·
                      refine ⟨2023817247211349605448975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21587383970254395791455733 2023817247211349605448975)
                      ·
                        rfl

theorem cell23_3941370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_3941370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941370 prefixEnd_3941370 := by exact prefixLift 3941370
  have htrace : WordTrace (prefixWord ++ tailWord_3941370) baseStart_3941370 baseEnd_3941370 := by
    simpa [prefixWord, tailWord_3941370, baseEnd_3941370] using wordTrace_append hprefix tailTrace_3941370
  have hstable : (prefixWord ++ tailWord_3941370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941370).length < 2 ^ (prefixWord ++ tailWord_3941370).sum := by decide
  have hdescent : baseEnd_3941370 < baseStart_3941370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941387 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5]
def baseStart_3941387 : Nat := 118140960795 + 3941387 * 2 ^ 59
def prefixEnd_3941387 : Nat := 4983230072969 + 3 ^ 40 * 3941387 * 2
def baseEnd_3941387 : Nat := 2023825976382476038936397

theorem tailTrace_3941387 : CollatzResearch.WordTrace tailWord_3941387 prefixEnd_3941387 2023825976382476038936397 := by
  unfold tailWord_3941387
  simp only [CollatzResearch.WordTrace]
  refine ⟨143754193772035509153670415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95836129181357006102446943 143754193772035509153670415)
  ·
    refine ⟨215631290658053263730505623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143754193772035509153670415 215631290658053263730505623)
    ·
      refine ⟨323446935987079895595758435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215631290658053263730505623 323446935987079895595758435)
      ·
        refine ⟨485170403980619843393637653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323446935987079895595758435 485170403980619843393637653)
        ·
          refine ⟨22742362686591555159076765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 485170403980619843393637653 22742362686591555159076765)
          ·
            refine ⟨8528386007471833184653787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22742362686591555159076765 8528386007471833184653787)
            ·
              refine ⟨12792579011207749776980681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8528386007471833184653787 12792579011207749776980681)
              ·
                refine ⟨9594434258405812332735511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12792579011207749776980681 9594434258405812332735511)
                ·
                  refine ⟨14391651387608718499103267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9594434258405812332735511 14391651387608718499103267)
                  ·
                    refine ⟨21587477081413077748654901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14391651387608718499103267 21587477081413077748654901)
                    ·
                      refine ⟨2023825976382476038936397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21587477081413077748654901 2023825976382476038936397)
                      ·
                        rfl

theorem cell23_3941387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5].length) (baseStart_3941387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941387 prefixEnd_3941387 := by exact prefixLift 3941387
  have htrace : WordTrace (prefixWord ++ tailWord_3941387) baseStart_3941387 baseEnd_3941387 := by
    simpa [prefixWord, tailWord_3941387, baseEnd_3941387] using wordTrace_append hprefix tailTrace_3941387
  have hstable : (prefixWord ++ tailWord_3941387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941387).length < 2 ^ (prefixWord ++ tailWord_3941387).sum := by decide
  have hdescent : baseEnd_3941387 < baseStart_3941387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941397 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3941397 : Nat := 118140960795 + 3941397 * 2 ^ 59
def prefixEnd_3941397 : Nat := 4983230072969 + 3 ^ 40 * 3941397 * 2
def baseEnd_3941397 : Nat := 2023831111189020999811351

theorem tailTrace_3941397 : CollatzResearch.WordTrace tailWord_3941397 prefixEnd_3941397 2023831111189020999811351 := by
  unfold tailWord_3941397
  simp only [CollatzResearch.WordTrace]
  refine ⟨143754558501999280861534445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95836372334666187241022963 143754558501999280861534445)
  ·
    refine ⟨53907959438249730323075417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143754558501999280861534445 53907959438249730323075417)
    ·
      refine ⟨40430969578687297742306563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53907959438249730323075417 40430969578687297742306563)
      ·
        refine ⟨60646454368030946613459845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40430969578687297742306563 60646454368030946613459845)
        ·
          refine ⟨11371210194005802490023721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60646454368030946613459845 11371210194005802490023721)
          ·
            refine ⟨8528407645504351867517791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11371210194005802490023721 8528407645504351867517791)
            ·
              refine ⟨12792611468256527801276687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8528407645504351867517791 12792611468256527801276687)
              ·
                refine ⟨19188917202384791701915031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12792611468256527801276687 19188917202384791701915031)
                ·
                  refine ⟨28783375803577187552872547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19188917202384791701915031 28783375803577187552872547)
                  ·
                    refine ⟨43175063705365781329308821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28783375803577187552872547 43175063705365781329308821)
                    ·
                      refine ⟨2023831111189020999811351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43175063705365781329308821 2023831111189020999811351)
                      ·
                        rfl

theorem cell23_3941397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3941397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941397 prefixEnd_3941397 := by exact prefixLift 3941397
  have htrace : WordTrace (prefixWord ++ tailWord_3941397) baseStart_3941397 baseEnd_3941397 := by
    simpa [prefixWord, tailWord_3941397, baseEnd_3941397] using wordTrace_append hprefix tailTrace_3941397
  have hstable : (prefixWord ++ tailWord_3941397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941397).length < 2 ^ (prefixWord ++ tailWord_3941397).sum := by decide
  have hdescent : baseEnd_3941397 < baseStart_3941397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941407 : List Nat := [1, 1, 2, 4, 1, 3, 4, 7]
def baseStart_3941407 : Nat := 118140960795 + 3941407 * 2 ^ 59
def prefixEnd_3941407 : Nat := 4983230072969 + 3 ^ 40 * 3941407 * 2
def baseEnd_3941407 : Nat := 74956897999835776321715

theorem tailTrace_3941407 : CollatzResearch.WordTrace tailWord_3941407 prefixEnd_3941407 74956897999835776321715 := by
  unfold tailWord_3941407
  simp only [CollatzResearch.WordTrace]
  refine ⟨143754923231963052569398475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95836615487975368379598983 143754923231963052569398475)
  ·
    refine ⟨215632384847944578854097713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143754923231963052569398475 215632384847944578854097713)
    ·
      refine ⟨161724288635958434140573285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215632384847944578854097713 161724288635958434140573285)
      ·
        refine ⟨30323304119242206401357491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161724288635958434140573285 30323304119242206401357491)
        ·
          refine ⟨45484956178863309602036237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30323304119242206401357491 45484956178863309602036237)
          ·
            refine ⟨17056858567073741100763589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45484956178863309602036237 17056858567073741100763589)
            ·
              refine ⟨3198160981326326456393173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17056858567073741100763589 3198160981326326456393173)
              ·
                refine ⟨74956897999835776321715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3198160981326326456393173 74956897999835776321715)
                ·
                  rfl

theorem cell23_3941407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 7].length) (baseStart_3941407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941407 prefixEnd_3941407 := by exact prefixLift 3941407
  have htrace : WordTrace (prefixWord ++ tailWord_3941407) baseStart_3941407 baseEnd_3941407 := by
    simpa [prefixWord, tailWord_3941407, baseEnd_3941407] using wordTrace_append hprefix tailTrace_3941407
  have hstable : (prefixWord ++ tailWord_3941407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941407).length < 2 ^ (prefixWord ++ tailWord_3941407).sum := by decide
  have hdescent : baseEnd_3941407 < baseStart_3941407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941434 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_3941434 : Nat := 118140960795 + 3941434 * 2 ^ 59
def prefixEnd_3941434 : Nat := 4983230072969 + 3 ^ 40 * 3941434 * 2
def baseEnd_3941434 : Nat := 2023850109973237355048681

theorem tailTrace_3941434 : CollatzResearch.WordTrace tailWord_3941434 prefixEnd_3941434 2023850109973237355048681 := by
  unfold tailWord_3941434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35938977000716309045157839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95837272001910157453754237 35938977000716309045157839)
  ·
    refine ⟨53908465501074463567736759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35938977000716309045157839 53908465501074463567736759)
    ·
      refine ⟨80862698251611695351605139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53908465501074463567736759 80862698251611695351605139)
      ·
        refine ⟨121294047377417543027407709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80862698251611695351605139 121294047377417543027407709)
        ·
          refine ⟨45485267766531578635277891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121294047377417543027407709 45485267766531578635277891)
          ·
            refine ⟨68227901649797367952916837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45485267766531578635277891 68227901649797367952916837)
            ·
              refine ⟨12792731559337006491171907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68227901649797367952916837 12792731559337006491171907)
              ·
                refine ⟨19189097339005509736757861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12792731559337006491171907 19189097339005509736757861)
                ·
                  refine ⟨3597955751063533075642099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19189097339005509736757861 3597955751063533075642099)
                  ·
                    refine ⟨5396933626595299613463149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3597955751063533075642099 5396933626595299613463149)
                    ·
                      refine ⟨2023850109973237355048681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5396933626595299613463149 2023850109973237355048681)
                      ·
                        rfl

theorem cell23_3941434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_3941434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941434 prefixEnd_3941434 := by exact prefixLift 3941434
  have htrace : WordTrace (prefixWord ++ tailWord_3941434) baseStart_3941434 baseEnd_3941434 := by
    simpa [prefixWord, tailWord_3941434, baseEnd_3941434] using wordTrace_append hprefix tailTrace_3941434
  have hstable : (prefixWord ++ tailWord_3941434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941434).length < 2 ^ (prefixWord ++ tailWord_3941434).sum := by decide
  have hdescent : baseEnd_3941434 < baseStart_3941434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941477 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3941477 : Nat := 118140960795 + 3941477 * 2 ^ 59
def prefixEnd_3941477 : Nat := 4983230072969 + 3 ^ 40 * 3941477 * 2
def baseEnd_3941477 : Nat := 2023872189641380686810983

theorem tailTrace_3941477 : CollatzResearch.WordTrace tailWord_3941477 prefixEnd_3941477 2023872189641380686810983 := by
  unfold tailWord_3941477
  simp only [CollatzResearch.WordTrace]
  refine ⟨143757476341709454524446685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95838317561139636349631123 143757476341709454524446685)
  ·
    refine ⟨53909053628141045446667507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143757476341709454524446685 53909053628141045446667507)
    ·
      refine ⟨80863580442211568170001261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53909053628141045446667507 80863580442211568170001261)
      ·
        refine ⟨30323842665829338063750473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80863580442211568170001261 30323842665829338063750473)
        ·
          refine ⟨22742881999372003547812855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30323842665829338063750473 22742881999372003547812855)
          ·
            refine ⟨34114322999058005321719283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22742881999372003547812855 34114322999058005321719283)
            ·
              refine ⟨51171484498587007982578925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34114322999058005321719283 51171484498587007982578925)
              ·
                refine ⟨19189306686970127993467097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51171484498587007982578925 19189306686970127993467097)
                ·
                  refine ⟨14391980015227595995100323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19189306686970127993467097 14391980015227595995100323)
                  ·
                    refine ⟨21587970022841393992650485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14391980015227595995100323 21587970022841393992650485)
                    ·
                      refine ⟨2023872189641380686810983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21587970022841393992650485 2023872189641380686810983)
                      ·
                        rfl

theorem cell23_3941477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3941477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941477 prefixEnd_3941477 := by exact prefixLift 3941477
  have htrace : WordTrace (prefixWord ++ tailWord_3941477) baseStart_3941477 baseEnd_3941477 := by
    simpa [prefixWord, tailWord_3941477, baseEnd_3941477] using wordTrace_append hprefix tailTrace_3941477
  have hstable : (prefixWord ++ tailWord_3941477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941477).length < 2 ^ (prefixWord ++ tailWord_3941477).sum := by decide
  have hdescent : baseEnd_3941477 < baseStart_3941477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941487 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_3941487 : Nat := 118140960795 + 3941487 * 2 ^ 59
def prefixEnd_3941487 : Nat := 4983230072969 + 3 ^ 40 * 3941487 * 2
def baseEnd_3941487 : Nat := 2023877324447925647685937

theorem tailTrace_3941487 : CollatzResearch.WordTrace tailWord_3941487 prefixEnd_3941487 2023877324447925647685937 := by
  unfold tailWord_3941487
  simp only [CollatzResearch.WordTrace]
  refine ⟨143757841071673226232310715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95838560714448817488207143 143757841071673226232310715)
  ·
    refine ⟨215636761607509839348466073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143757841071673226232310715 215636761607509839348466073)
    ·
      refine ⟨161727571205632379511349555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215636761607509839348466073 161727571205632379511349555)
      ·
        refine ⟨242591356808448569267024333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161727571205632379511349555 242591356808448569267024333)
        ·
          refine ⟨90971758803168213475134125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242591356808448569267024333 90971758803168213475134125)
          ·
            refine ⟨34114409551188080053175297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90971758803168213475134125 34114409551188080053175297)
            ·
              refine ⟨25585807163391060039881473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34114409551188080053175297 25585807163391060039881473)
              ·
                refine ⟨19189355372543295029911105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25585807163391060039881473 19189355372543295029911105)
                ·
                  refine ⟨14392016529407471272433329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19189355372543295029911105 14392016529407471272433329)
                  ·
                    refine ⟨10794012397055603454324997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14392016529407471272433329 10794012397055603454324997)
                    ·
                      refine ⟨2023877324447925647685937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10794012397055603454324997 2023877324447925647685937)
                      ·
                        rfl

theorem cell23_3941487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_3941487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941487 prefixEnd_3941487 := by exact prefixLift 3941487
  have htrace : WordTrace (prefixWord ++ tailWord_3941487) baseStart_3941487 baseEnd_3941487 := by
    simpa [prefixWord, tailWord_3941487, baseEnd_3941487] using wordTrace_append hprefix tailTrace_3941487
  have hstable : (prefixWord ++ tailWord_3941487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941487).length < 2 ^ (prefixWord ++ tailWord_3941487).sum := by decide
  have hdescent : baseEnd_3941487 < baseStart_3941487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941494 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3941494 : Nat := 118140960795 + 3941494 * 2 ^ 59
def prefixEnd_3941494 : Nat := 4983230072969 + 3 ^ 40 * 3941494 * 2
def baseEnd_3941494 : Nat := 2023880918812507120298405

theorem tailTrace_3941494 : CollatzResearch.WordTrace tailWord_3941494 prefixEnd_3941494 2023880918812507120298405 := by
  unfold tailWord_3941494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984881023915491651738471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95838730921765244285210357 8984881023915491651738471)
  ·
    refine ⟨13477321535873237477607707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8984881023915491651738471 13477321535873237477607707)
    ·
      refine ⟨20215982303809856216411561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13477321535873237477607707 20215982303809856216411561)
      ·
        refine ⟨15161986727857392162308671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20215982303809856216411561 15161986727857392162308671)
        ·
          refine ⟨22742980091786088243463007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15161986727857392162308671 22742980091786088243463007)
          ·
            refine ⟨34114470137679132365194511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22742980091786088243463007 34114470137679132365194511)
            ·
              refine ⟨51171705206518698547791767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34114470137679132365194511 51171705206518698547791767)
              ·
                refine ⟨76757557809778047821687651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51171705206518698547791767 76757557809778047821687651)
                ·
                  refine ⟨115136336714667071732531477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76757557809778047821687651 115136336714667071732531477)
                  ·
                    refine ⟨5397015783500018987462413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115136336714667071732531477 5397015783500018987462413)
                    ·
                      refine ⟨2023880918812507120298405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5397015783500018987462413 2023880918812507120298405)
                      ·
                        rfl

theorem cell23_3941494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3941494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941494 prefixEnd_3941494 := by exact prefixLift 3941494
  have htrace : WordTrace (prefixWord ++ tailWord_3941494) baseStart_3941494 baseEnd_3941494 := by
    simpa [prefixWord, tailWord_3941494, baseEnd_3941494] using wordTrace_append hprefix tailTrace_3941494
  have hstable : (prefixWord ++ tailWord_3941494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941494).length < 2 ^ (prefixWord ++ tailWord_3941494).sum := by decide
  have hdescent : baseEnd_3941494 < baseStart_3941494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941508 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_3941508 : Nat := 118140960795 + 3941508 * 2 ^ 59
def prefixEnd_3941508 : Nat := 4983230072969 + 3 ^ 40 * 3941508 * 2
def baseEnd_3941508 : Nat := 2023888107541670065523341

theorem tailTrace_3941508 : CollatzResearch.WordTrace tailWord_3941508 prefixEnd_3941508 2023888107541670065523341 := by
  unfold tailWord_3941508
  simp only [CollatzResearch.WordTrace]
  refine ⟨71879303502298573409412589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95839071336398097879216785 71879303502298573409412589)
  ·
    refine ⟨26954738813361965028529721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71879303502298573409412589 26954738813361965028529721)
    ·
      refine ⟨20216054110021473771397291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26954738813361965028529721 20216054110021473771397291)
      ·
        refine ⟨30324081165032210657095937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20216054110021473771397291 30324081165032210657095937)
        ·
          refine ⟨22743060873774157992821953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30324081165032210657095937 22743060873774157992821953)
          ·
            refine ⟨17057295655330618494616465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22743060873774157992821953 17057295655330618494616465)
            ·
              refine ⟨12792971741497963870962349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17057295655330618494616465 12792971741497963870962349)
              ·
                refine ⟨4797364403061736451610881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12792971741497963870962349 4797364403061736451610881)
                ·
                  refine ⟨3598023302296302338708161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4797364403061736451610881 3598023302296302338708161)
                  ·
                    refine ⟨2698517476722226754031121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3598023302296302338708161 2698517476722226754031121)
                    ·
                      refine ⟨2023888107541670065523341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698517476722226754031121 2023888107541670065523341)
                      ·
                        rfl

theorem cell23_3941508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_3941508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941508 prefixEnd_3941508 := by exact prefixLift 3941508
  have htrace : WordTrace (prefixWord ++ tailWord_3941508) baseStart_3941508 baseEnd_3941508 := by
    simpa [prefixWord, tailWord_3941508, baseEnd_3941508] using wordTrace_append hprefix tailTrace_3941508
  have hstable : (prefixWord ++ tailWord_3941508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941508).length < 2 ^ (prefixWord ++ tailWord_3941508).sum := by decide
  have hdescent : baseEnd_3941508 < baseStart_3941508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941564 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3941564 : Nat := 118140960795 + 3941564 * 2 ^ 59
def prefixEnd_3941564 : Nat := 4983230072969 + 3 ^ 40 * 3941564 * 2
def baseEnd_3941564 : Nat := 2023916862458321846423083

theorem tailTrace_3941564 : CollatzResearch.WordTrace tailWord_3941564 prefixEnd_3941564 2023916862458321846423083 := by
  unfold tailWord_3941564
  simp only [CollatzResearch.WordTrace]
  refine ⟨71880324746197134191431873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95840432994929512255242497 71880324746197134191431873)
  ·
    refine ⟨53910243559647850643573905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71880324746197134191431873 53910243559647850643573905)
    ·
      refine ⟨40432682669735887982680429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53910243559647850643573905 40432682669735887982680429)
      ·
        refine ⟨15162256001150957993505161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40432682669735887982680429 15162256001150957993505161)
        ·
          refine ⟨11371692000863218495128871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15162256001150957993505161 11371692000863218495128871)
          ·
            refine ⟨17057538001294827742693307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11371692000863218495128871 17057538001294827742693307)
            ·
              refine ⟨25586307001942241614039961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17057538001294827742693307 25586307001942241614039961)
              ·
                refine ⟨19189730251456681210529971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25586307001942241614039961 19189730251456681210529971)
                ·
                  refine ⟨28784595377185021815794957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19189730251456681210529971 28784595377185021815794957)
                  ·
                    refine ⟨10794223266444383180923109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28784595377185021815794957 10794223266444383180923109)
                    ·
                      refine ⟨2023916862458321846423083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10794223266444383180923109 2023916862458321846423083)
                      ·
                        rfl

theorem cell23_3941564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3941564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941564 prefixEnd_3941564 := by exact prefixLift 3941564
  have htrace : WordTrace (prefixWord ++ tailWord_3941564) baseStart_3941564 baseEnd_3941564 := by
    simpa [prefixWord, tailWord_3941564, baseEnd_3941564] using wordTrace_append hprefix tailTrace_3941564
  have hstable : (prefixWord ++ tailWord_3941564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941564).length < 2 ^ (prefixWord ++ tailWord_3941564).sum := by decide
  have hdescent : baseEnd_3941564 < baseStart_3941564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941601 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3941601 : Nat := 118140960795 + 3941601 * 2 ^ 59
def prefixEnd_3941601 : Nat := 4983230072969 + 3 ^ 40 * 3941601 * 2
def baseEnd_3941601 : Nat := 2023935861242538201660413

theorem tailTrace_3941601 : CollatzResearch.WordTrace tailWord_3941601 prefixEnd_3941601 2023935861242538201660413 := by
  unfold tailWord_3941601
  simp only [CollatzResearch.WordTrace]
  refine ⟨143761998993260223701960657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95841332662173482467973771 143761998993260223701960657)
  ·
    refine ⟨107821499244945167776470493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143761998993260223701960657 107821499244945167776470493)
    ·
      refine ⟨40433062216854437916176435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107821499244945167776470493 40433062216854437916176435)
      ·
        refine ⟨60649593325281656874264653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40433062216854437916176435 60649593325281656874264653)
        ·
          refine ⟨22743597496980621327849245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60649593325281656874264653 22743597496980621327849245)
          ·
            refine ⟨8528849061367732997943467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22743597496980621327849245 8528849061367732997943467)
            ·
              refine ⟨12793273592051599496915201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8528849061367732997943467 12793273592051599496915201)
              ·
                refine ⟨9594955194038699622686401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12793273592051599496915201 9594955194038699622686401)
                ·
                  refine ⟨7196216395529024717014801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9594955194038699622686401 7196216395529024717014801)
                  ·
                    refine ⟨5397162296646768537761101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7196216395529024717014801 5397162296646768537761101)
                    ·
                      refine ⟨2023935861242538201660413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5397162296646768537761101 2023935861242538201660413)
                      ·
                        rfl

theorem cell23_3941601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3941601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941601 prefixEnd_3941601 := by exact prefixLift 3941601
  have htrace : WordTrace (prefixWord ++ tailWord_3941601) baseStart_3941601 baseEnd_3941601 := by
    simpa [prefixWord, tailWord_3941601, baseEnd_3941601] using wordTrace_append hprefix tailTrace_3941601
  have hstable : (prefixWord ++ tailWord_3941601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941601).length < 2 ^ (prefixWord ++ tailWord_3941601).sum := by decide
  have hdescent : baseEnd_3941601 < baseStart_3941601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941617 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 9]
def baseStart_3941617 : Nat := 118140960795 + 3941617 * 2 ^ 59
def prefixEnd_3941617 : Nat := 4983230072969 + 3 ^ 40 * 3941617 * 2
def baseEnd_3941617 : Nat := 674648025644336713020113

theorem tailTrace_3941617 : CollatzResearch.WordTrace tailWord_3941617 prefixEnd_3941617 674648025644336713020113 := by
  unfold tailWord_3941617
  simp only [CollatzResearch.WordTrace]
  refine ⟨143762582561202258434543105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95841721707468172289695403 143762582561202258434543105)
  ·
    refine ⟨107821936920901693825907329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143762582561202258434543105 107821936920901693825907329)
    ·
      refine ⟨80866452690676270369430497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107821936920901693825907329 80866452690676270369430497)
      ·
        refine ⟨60649839518007202777072873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80866452690676270369430497 60649839518007202777072873)
        ·
          refine ⟨45487379638505402082804655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60649839518007202777072873 45487379638505402082804655)
          ·
            refine ⟨68231069457758103124206983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45487379638505402082804655 68231069457758103124206983)
            ·
              refine ⟨102346604186637154686310475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68231069457758103124206983 102346604186637154686310475)
              ·
                refine ⟨153519906279955732029465713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102346604186637154686310475 153519906279955732029465713)
                ·
                  refine ⟨115139929709966799022099285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153519906279955732029465713 115139929709966799022099285)
                  ·
                    refine ⟨674648025644336713020113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115139929709966799022099285 674648025644336713020113)
                    ·
                      rfl

theorem cell23_3941617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_3941617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941617 prefixEnd_3941617 := by exact prefixLift 3941617
  have htrace : WordTrace (prefixWord ++ tailWord_3941617) baseStart_3941617 baseEnd_3941617 := by
    simpa [prefixWord, tailWord_3941617, baseEnd_3941617] using wordTrace_append hprefix tailTrace_3941617
  have hstable : (prefixWord ++ tailWord_3941617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941617).length < 2 ^ (prefixWord ++ tailWord_3941617).sum := by decide
  have hdescent : baseEnd_3941617 < baseStart_3941617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941658 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2]
def baseStart_3941658 : Nat := 118140960795 + 3941658 * 2 ^ 59
def prefixEnd_3941658 : Nat := 4983230072969 + 3 ^ 40 * 3941658 * 2
def baseEnd_3941658 : Nat := 2023965129639844478647651

theorem tailTrace_3941658 : CollatzResearch.WordTrace tailWord_3941658 prefixEnd_3941658 2023965129639844478647651 := by
  unfold tailWord_3941658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35941019488513430609196407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95842718636035814957857085 35941019488513430609196407)
  ·
    refine ⟨53911529232770145913794611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35941019488513430609196407 53911529232770145913794611)
    ·
      refine ⟨80867293849155218870691917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53911529232770145913794611 80867293849155218870691917)
      ·
        refine ⟨30325235193433207076509469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80867293849155218870691917 30325235193433207076509469)
        ·
          refine ⟨11371963197537452653691051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30325235193433207076509469 11371963197537452653691051)
          ·
            refine ⟨17057944796306178980536577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11371963197537452653691051 17057944796306178980536577)
            ·
              refine ⟨12793458597229634235402433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17057944796306178980536577 12793458597229634235402433)
              ·
                refine ⟨9595093947922225676551825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12793458597229634235402433 9595093947922225676551825)
                ·
                  refine ⟨7196320460941669257413869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9595093947922225676551825 7196320460941669257413869)
                  ·
                    refine ⟨2698620172853125971530201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7196320460941669257413869 2698620172853125971530201)
                    ·
                      refine ⟨2023965129639844478647651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698620172853125971530201 2023965129639844478647651)
                      ·
                        rfl

theorem cell23_3941658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_3941658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941658 prefixEnd_3941658 := by exact prefixLift 3941658
  have htrace : WordTrace (prefixWord ++ tailWord_3941658) baseStart_3941658 baseEnd_3941658 := by
    simpa [prefixWord, tailWord_3941658, baseEnd_3941658] using wordTrace_append hprefix tailTrace_3941658
  have hstable : (prefixWord ++ tailWord_3941658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941658).length < 2 ^ (prefixWord ++ tailWord_3941658).sum := by decide
  have hdescent : baseEnd_3941658 < baseStart_3941658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941681 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 1, 6]
def baseStart_3941681 : Nat := 118140960795 + 3941681 * 2 ^ 59
def prefixEnd_3941681 : Nat := 4983230072969 + 3 ^ 40 * 3941681 * 2
def baseEnd_3941681 : Nat := 674658979898299296220015

theorem tailTrace_3941681 : CollatzResearch.WordTrace tailWord_3941681 prefixEnd_3941681 674658979898299296220015 := by
  unfold tailWord_3941681
  simp only [CollatzResearch.WordTrace]
  refine ⟨143764916832970397364872897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95843277888646931576581931 143764916832970397364872897)
  ·
    refine ⟨107823687624727798023654673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143764916832970397364872897 107823687624727798023654673)
    ·
      refine ⟨80867765718545848517741005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107823687624727798023654673 80867765718545848517741005)
      ·
        refine ⟨30325412144454693194152877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80867765718545848517741005 30325412144454693194152877)
        ·
          refine ⟨11372029554170509947807329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30325412144454693194152877 11372029554170509947807329)
          ·
            refine ⟨8529022165627882460855497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11372029554170509947807329 8529022165627882460855497)
            ·
              refine ⟨6396766624220911845641623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8529022165627882460855497 6396766624220911845641623)
              ·
                refine ⟨9595149936331367768462435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6396766624220911845641623 9595149936331367768462435)
                ·
                  refine ⟨14392724904497051652693653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9595149936331367768462435 14392724904497051652693653)
                  ·
                    refine ⟨674658979898299296220015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14392724904497051652693653 674658979898299296220015)
                    ·
                      rfl

theorem cell23_3941681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_3941681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941681 prefixEnd_3941681 := by exact prefixLift 3941681
  have htrace : WordTrace (prefixWord ++ tailWord_3941681) baseStart_3941681 baseEnd_3941681 := by
    simpa [prefixWord, tailWord_3941681, baseEnd_3941681] using wordTrace_append hprefix tailTrace_3941681
  have hstable : (prefixWord ++ tailWord_3941681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941681).length < 2 ^ (prefixWord ++ tailWord_3941681).sum := by decide
  have hdescent : baseEnd_3941681 < baseStart_3941681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941702 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3941702 : Nat := 118140960795 + 3941702 * 2 ^ 59
def prefixEnd_3941702 : Nat := 4983230072969 + 3 ^ 40 * 3941702 * 2
def baseEnd_3941702 : Nat := 674662574262880768832483

theorem tailTrace_3941702 : CollatzResearch.WordTrace tailWord_3941702 prefixEnd_3941702 674662574262880768832483 := by
  unfold tailWord_3941702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492677586434197435980855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95843788510596211967591573 4492677586434197435980855)
  ·
    refine ⟨6739016379651296153971283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492677586434197435980855 6739016379651296153971283)
    ·
      refine ⟨10108524569476944230956925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739016379651296153971283 10108524569476944230956925)
      ·
        refine ⟨3790696713553854086608847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10108524569476944230956925 3790696713553854086608847)
        ·
          refine ⟨5686045070330781129913271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790696713553854086608847 5686045070330781129913271)
          ·
            refine ⟨8529067605496171694869907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686045070330781129913271 8529067605496171694869907)
            ·
              refine ⟨12793601408244257542304861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529067605496171694869907 12793601408244257542304861)
              ·
                refine ⟨4797600528091596578364323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12793601408244257542304861 4797600528091596578364323)
                ·
                  refine ⟨7196400792137394867546485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797600528091596578364323 7196400792137394867546485)
                  ·
                    refine ⟨674662574262880768832483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7196400792137394867546485 674662574262880768832483)
                    ·
                      rfl

theorem cell23_3941702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3941702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941702 prefixEnd_3941702 := by exact prefixLift 3941702
  have htrace : WordTrace (prefixWord ++ tailWord_3941702) baseStart_3941702 baseEnd_3941702 := by
    simpa [prefixWord, tailWord_3941702, baseEnd_3941702] using wordTrace_append hprefix tailTrace_3941702
  have hstable : (prefixWord ++ tailWord_3941702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941702).length < 2 ^ (prefixWord ++ tailWord_3941702).sum := by decide
  have hdescent : baseEnd_3941702 < baseStart_3941702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941705 : List Nat := [1, 2, 1, 1, 2, 3, 3, 5, 1, 2, 2]
def baseStart_3941705 : Nat := 118140960795 + 3941705 * 2 ^ 59
def prefixEnd_3941705 : Nat := 4983230072969 + 3 ^ 40 * 3941705 * 2
def baseEnd_3941705 : Nat := 2023989263230605794759935

theorem tailTrace_3941705 : CollatzResearch.WordTrace tailWord_3941705 prefixEnd_3941705 2023989263230605794759935 := by
  unfold tailWord_3941705
  simp only [CollatzResearch.WordTrace]
  refine ⟨143765792184883449463746569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95843861456588966309164379 143765792184883449463746569)
  ·
    refine ⟨107824344138662587097809927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143765792184883449463746569 107824344138662587097809927)
    ·
      refine ⟨161736516207993880646714891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107824344138662587097809927 161736516207993880646714891)
      ·
        refine ⟨242604774311990820970072337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161736516207993880646714891 242604774311990820970072337)
        ·
          refine ⟨181953580733993115727554253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242604774311990820970072337 181953580733993115727554253)
          ·
            refine ⟨68232592775247418397832845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181953580733993115727554253 68232592775247418397832845)
            ·
              refine ⟨25587222290717781899187317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68232592775247418397832845 25587222290717781899187317)
              ·
                refine ⟨2398802089754792053048811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25587222290717781899187317 2398802089754792053048811)
                ·
                  refine ⟨3598203134632188079573217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398802089754792053048811 3598203134632188079573217)
                  ·
                    refine ⟨2698652350974141059679913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3598203134632188079573217 2698652350974141059679913)
                    ·
                      refine ⟨2023989263230605794759935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698652350974141059679913 2023989263230605794759935)
                      ·
                        rfl

theorem cell23_3941705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 2, 2].length) (baseStart_3941705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941705 prefixEnd_3941705 := by exact prefixLift 3941705
  have htrace : WordTrace (prefixWord ++ tailWord_3941705) baseStart_3941705 baseEnd_3941705 := by
    simpa [prefixWord, tailWord_3941705, baseEnd_3941705] using wordTrace_append hprefix tailTrace_3941705
  have hstable : (prefixWord ++ tailWord_3941705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941705).length < 2 ^ (prefixWord ++ tailWord_3941705).sum := by decide
  have hdescent : baseEnd_3941705 < baseStart_3941705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941708 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_3941708 : Nat := 118140960795 + 3941708 * 2 ^ 59
def prefixEnd_3941708 : Nat := 4983230072969 + 3 ^ 40 * 3941708 * 2
def baseEnd_3941708 : Nat := 2023990803672569283022421

theorem tailTrace_3941708 : CollatzResearch.WordTrace tailWord_3941708 prefixEnd_3941708 2023990803672569283022421 := by
  unfold tailWord_3941708
  simp only [CollatzResearch.WordTrace]
  refine ⟨71882950801936290488052889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95843934402581720650737185 71882950801936290488052889)
  ·
    refine ⟨53912213101452217866039667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71882950801936290488052889 53912213101452217866039667)
    ·
      refine ⟨80868319652178326799059501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53912213101452217866039667 80868319652178326799059501)
      ·
        refine ⟨30325619869566872549647313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80868319652178326799059501 30325619869566872549647313)
        ·
          refine ⟨22744214902175154412235485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30325619869566872549647313 22744214902175154412235485)
          ·
            refine ⟨8529080588315682904588307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22744214902175154412235485 8529080588315682904588307)
            ·
              refine ⟨12793620882473524356882461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529080588315682904588307 12793620882473524356882461)
              ·
                refine ⟨4797607830927571633830923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12793620882473524356882461 4797607830927571633830923)
                ·
                  refine ⟨7196411746391357450746385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797607830927571633830923 7196411746391357450746385)
                  ·
                    refine ⟨5397308809793518088059789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7196411746391357450746385 5397308809793518088059789)
                    ·
                      refine ⟨2023990803672569283022421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5397308809793518088059789 2023990803672569283022421)
                      ·
                        rfl

theorem cell23_3941708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_3941708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941708 prefixEnd_3941708 := by exact prefixLift 3941708
  have htrace : WordTrace (prefixWord ++ tailWord_3941708) baseStart_3941708 baseEnd_3941708 := by
    simpa [prefixWord, tailWord_3941708, baseEnd_3941708] using wordTrace_append hprefix tailTrace_3941708
  have hstable : (prefixWord ++ tailWord_3941708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941708).length < 2 ^ (prefixWord ++ tailWord_3941708).sum := by decide
  have hdescent : baseEnd_3941708 < baseStart_3941708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941714 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_3941714 : Nat := 118140960795 + 3941714 * 2 ^ 59
def prefixEnd_3941714 : Nat := 4983230072969 + 3 ^ 40 * 3941714 * 2
def baseEnd_3941714 : Nat := 2023993884556496259547393

theorem tailTrace_3941714 : CollatzResearch.WordTrace tailWord_3941714 prefixEnd_3941714 2023993884556496259547393 := by
  unfold tailWord_3941714
  simp only [CollatzResearch.WordTrace]
  refine ⟨35941530110462711000206049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95844080294567229333882797 35941530110462711000206049)
  ·
    refine ⟨26956147582847033250154537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35941530110462711000206049 26956147582847033250154537)
    ·
      refine ⟨20217110687135274937615903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26956147582847033250154537 20217110687135274937615903)
      ·
        refine ⟨30325666030702912406423855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20217110687135274937615903 30325666030702912406423855)
        ·
          refine ⟨45488499046054368609635783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30325666030702912406423855 45488499046054368609635783)
          ·
            refine ⟨68232748569081552914453675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45488499046054368609635783 68232748569081552914453675)
            ·
              refine ⟨102349122853622329371680513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68232748569081552914453675 102349122853622329371680513)
              ·
                refine ⟨76761842140216747028760385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102349122853622329371680513 76761842140216747028760385)
                ·
                  refine ⟨57571381605162560271570289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76761842140216747028760385 57571381605162560271570289)
                  ·
                    refine ⟨43178536203871920203677717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57571381605162560271570289 43178536203871920203677717)
                    ·
                      refine ⟨2023993884556496259547393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43178536203871920203677717 2023993884556496259547393)
                      ·
                        rfl

theorem cell23_3941714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_3941714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941714 prefixEnd_3941714 := by exact prefixLift 3941714
  have htrace : WordTrace (prefixWord ++ tailWord_3941714) baseStart_3941714 baseEnd_3941714 := by
    simpa [prefixWord, tailWord_3941714, baseEnd_3941714] using wordTrace_append hprefix tailTrace_3941714
  have hstable : (prefixWord ++ tailWord_3941714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941714).length < 2 ^ (prefixWord ++ tailWord_3941714).sum := by decide
  have hdescent : baseEnd_3941714 < baseStart_3941714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941735 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_3941735 : Nat := 118140960795 + 3941735 * 2 ^ 59
def prefixEnd_3941735 : Nat := 4983230072969 + 3 ^ 40 * 3941735 * 2
def baseEnd_3941735 : Nat := 2024004667650240677384797

theorem tailTrace_3941735 : CollatzResearch.WordTrace tailWord_3941735 prefixEnd_3941735 2024004667650240677384797 := by
  unfold tailWord_3941735
  simp only [CollatzResearch.WordTrace]
  refine ⟨143766886374774764587338659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95844590916516509724892439 143766886374774764587338659)
  ·
    refine ⟨215650329562162146881007989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143766886374774764587338659 215650329562162146881007989)
    ·
      refine ⟨20217218396452701270094499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215650329562162146881007989 20217218396452701270094499)
      ·
        refine ⟨30325827594679051905141749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20217218396452701270094499 30325827594679051905141749)
        ·
          refine ⟨2843046337001161116107039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30325827594679051905141749 2843046337001161116107039)
          ·
            refine ⟨4264569505501741674160559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843046337001161116107039 4264569505501741674160559)
            ·
              refine ⟨6396854258252612511240839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264569505501741674160559 6396854258252612511240839)
              ·
                refine ⟨9595281387378918766861259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6396854258252612511240839 9595281387378918766861259)
                ·
                  refine ⟨14392922081068378150291889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9595281387378918766861259 14392922081068378150291889)
                  ·
                    refine ⟨10794691560801283612718917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14392922081068378150291889 10794691560801283612718917)
                    ·
                      refine ⟨2024004667650240677384797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10794691560801283612718917 2024004667650240677384797)
                      ·
                        rfl

theorem cell23_3941735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_3941735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941735 prefixEnd_3941735 := by exact prefixLift 3941735
  have htrace : WordTrace (prefixWord ++ tailWord_3941735) baseStart_3941735 baseEnd_3941735 := by
    simpa [prefixWord, tailWord_3941735, baseEnd_3941735] using wordTrace_append hprefix tailTrace_3941735
  have hstable : (prefixWord ++ tailWord_3941735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941735).length < 2 ^ (prefixWord ++ tailWord_3941735).sum := by decide
  have hdescent : baseEnd_3941735 < baseStart_3941735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941742 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3941742 : Nat := 118140960795 + 3941742 * 2 ^ 59
def prefixEnd_3941742 : Nat := 4983230072969 + 3 ^ 40 * 3941742 * 2
def baseEnd_3941742 : Nat := 2024008262014822149997265

theorem tailTrace_3941742 : CollatzResearch.WordTrace tailWord_3941742 prefixEnd_3941742 2024008262014822149997265 := by
  unfold tailWord_3941742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17970892710718675597855435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95844761123832936521895653 17970892710718675597855435)
  ·
    refine ⟨26956339066078013396783153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17970892710718675597855435 26956339066078013396783153)
    ·
      refine ⟨20217254299558510047587365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26956339066078013396783153 20217254299558510047587365)
      ·
        refine ⟨3790735181167220633922631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20217254299558510047587365 3790735181167220633922631)
        ·
          refine ⟨5686102771750830950883947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790735181167220633922631 5686102771750830950883947)
          ·
            refine ⟨8529154157626246426325921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686102771750830950883947 8529154157626246426325921)
            ·
              refine ⟨6396865618219684819744441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8529154157626246426325921 6396865618219684819744441)
              ·
                refine ⟨4797649213664763614808331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6396865618219684819744441 4797649213664763614808331)
                ·
                  refine ⟨7196473820497145422212497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797649213664763614808331 7196473820497145422212497)
                  ·
                    refine ⟨5397355365372859066659373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7196473820497145422212497 5397355365372859066659373)
                    ·
                      refine ⟨2024008262014822149997265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5397355365372859066659373 2024008262014822149997265)
                      ·
                        rfl

theorem cell23_3941742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3941742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941742 prefixEnd_3941742 := by exact prefixLift 3941742
  have htrace : WordTrace (prefixWord ++ tailWord_3941742) baseStart_3941742 baseEnd_3941742 := by
    simpa [prefixWord, tailWord_3941742, baseEnd_3941742] using wordTrace_append hprefix tailTrace_3941742
  have hstable : (prefixWord ++ tailWord_3941742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941742).length < 2 ^ (prefixWord ++ tailWord_3941742).sum := by decide
  have hdescent : baseEnd_3941742 < baseStart_3941742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941795 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 2, 2, 2]
def baseStart_3941795 : Nat := 118140960795 + 3941795 * 2 ^ 59
def prefixEnd_3941795 : Nat := 4983230072969 + 3 ^ 40 * 3941795 * 2
def baseEnd_3941795 : Nat := 2024035476489510442634521

theorem tailTrace_3941795 : CollatzResearch.WordTrace tailWord_3941795 prefixEnd_3941795 2024035476489510442634521 := by
  unfold tailWord_3941795
  simp only [CollatzResearch.WordTrace]
  refine ⟨143769074754557394834522839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95846049836371596556348559 143769074754557394834522839)
  ·
    refine ⟨215653612131836092251784259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143769074754557394834522839 215653612131836092251784259)
    ·
      refine ⟨323480418197754138377676389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215653612131836092251784259 323480418197754138377676389)
      ·
        refine ⟨60652578412078900945814323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323480418197754138377676389 60652578412078900945814323)
        ·
          refine ⟨90978867618118351418721485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60652578412078900945814323 90978867618118351418721485)
          ·
            refine ⟨34117075356794381782020557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90978867618118351418721485 34117075356794381782020557)
            ·
              refine ⟨12793903258797893168257709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34117075356794381782020557 12793903258797893168257709)
              ·
                refine ⟨4797713722049209938096641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12793903258797893168257709 4797713722049209938096641)
                ·
                  refine ⟨3598285291536907453572481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4797713722049209938096641 3598285291536907453572481)
                  ·
                    refine ⟨2698713968652680590179361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3598285291536907453572481 2698713968652680590179361)
                    ·
                      refine ⟨2024035476489510442634521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698713968652680590179361 2024035476489510442634521)
                      ·
                        rfl

theorem cell23_3941795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_3941795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941795 prefixEnd_3941795 := by exact prefixLift 3941795
  have htrace : WordTrace (prefixWord ++ tailWord_3941795) baseStart_3941795 baseEnd_3941795 := by
    simpa [prefixWord, tailWord_3941795, baseEnd_3941795] using wordTrace_append hprefix tailTrace_3941795
  have hstable : (prefixWord ++ tailWord_3941795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941795).length < 2 ^ (prefixWord ++ tailWord_3941795).sum := by decide
  have hdescent : baseEnd_3941795 < baseStart_3941795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941831 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 2, 5]
def baseStart_3941831 : Nat := 118140960795 + 3941831 * 2 ^ 59
def prefixEnd_3941831 : Nat := 4983230072969 + 3 ^ 40 * 3941831 * 2
def baseEnd_3941831 : Nat := 674684653931024100594785

theorem tailTrace_3941831 : CollatzResearch.WordTrace tailWord_3941831 prefixEnd_3941831 674684653931024100594785 := by
  unfold tailWord_3941831
  simp only [CollatzResearch.WordTrace]
  refine ⟨143770387782426972982833347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95846925188284648655222231 143770387782426972982833347)
  ·
    refine ⟨215655581673640459474250021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143770387782426972982833347 215655581673640459474250021)
    ·
      refine ⟨40435421563807586151421879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215655581673640459474250021 40435421563807586151421879)
      ·
        refine ⟨60653132345711379227132819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40435421563807586151421879 60653132345711379227132819)
        ·
          refine ⟨90979698518567068840699229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60653132345711379227132819 90979698518567068840699229)
          ·
            refine ⟨34117386944462650815262211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90979698518567068840699229 34117386944462650815262211)
            ·
              refine ⟨51176080416693976222893317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34117386944462650815262211 51176080416693976222893317)
              ·
                refine ⟨9595515078130120541792497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51176080416693976222893317 9595515078130120541792497)
                ·
                  refine ⟨7196636308597590406344373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9595515078130120541792497 7196636308597590406344373)
                  ·
                    refine ⟨674684653931024100594785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7196636308597590406344373 674684653931024100594785)
                    ·
                      rfl

theorem cell23_3941831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_3941831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941831 prefixEnd_3941831 := by exact prefixLift 3941831
  have htrace : WordTrace (prefixWord ++ tailWord_3941831) baseStart_3941831 baseEnd_3941831 := by
    simpa [prefixWord, tailWord_3941831, baseEnd_3941831] using wordTrace_append hprefix tailTrace_3941831
  have hstable : (prefixWord ++ tailWord_3941831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941831).length < 2 ^ (prefixWord ++ tailWord_3941831).sum := by decide
  have hdescent : baseEnd_3941831 < baseStart_3941831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941838 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_3941838 : Nat := 118140960795 + 3941838 * 2 ^ 59
def prefixEnd_3941838 : Nat := 4983230072969 + 3 ^ 40 * 3941838 * 2
def baseEnd_3941838 : Nat := 2024057556157653774396823

theorem tailTrace_3941838 : CollatzResearch.WordTrace tailWord_3941838 prefixEnd_3941838 2024057556157653774396823 := by
  unfold tailWord_3941838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17971330386675201647292271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95847095395601075452225445 17971330386675201647292271)
  ·
    refine ⟨26956995580012802470938407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17971330386675201647292271 26956995580012802470938407)
    ·
      refine ⟨40435493370019203706407611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26956995580012802470938407 40435493370019203706407611)
      ·
        refine ⟨60653240055028805559611417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40435493370019203706407611 60653240055028805559611417)
        ·
          refine ⟨45489930041271604169708563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60653240055028805559611417 45489930041271604169708563)
          ·
            refine ⟨68234895061907406254562845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45489930041271604169708563 68234895061907406254562845)
            ·
              refine ⟨25588085648215277345461067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68234895061907406254562845 25588085648215277345461067)
              ·
                refine ⟨38382128472322916018191601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25588085648215277345461067 38382128472322916018191601)
                ·
                  refine ⟨28786596354242187013643701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38382128472322916018191601 28786596354242187013643701)
                  ·
                    refine ⟨2698743408210205032529097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28786596354242187013643701 2698743408210205032529097)
                    ·
                      refine ⟨2024057556157653774396823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698743408210205032529097 2024057556157653774396823)
                      ·
                        rfl

theorem cell23_3941838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_3941838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941838 prefixEnd_3941838 := by exact prefixLift 3941838
  have htrace : WordTrace (prefixWord ++ tailWord_3941838) baseStart_3941838 baseEnd_3941838 := by
    simpa [prefixWord, tailWord_3941838, baseEnd_3941838] using wordTrace_append hprefix tailTrace_3941838
  have hstable : (prefixWord ++ tailWord_3941838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941838).length < 2 ^ (prefixWord ++ tailWord_3941838).sum := by decide
  have hdescent : baseEnd_3941838 < baseStart_3941838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941891 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 6]
def baseStart_3941891 : Nat := 118140960795 + 3941891 * 2 ^ 59
def prefixEnd_3941891 : Nat := 4983230072969 + 3 ^ 40 * 3941891 * 2
def baseEnd_3941891 : Nat := 224898307848038007448231

theorem tailTrace_3941891 : CollatzResearch.WordTrace tailWord_3941891 prefixEnd_3941891 224898307848038007448231 := by
  unfold tailWord_3941891
  simp only [CollatzResearch.WordTrace]
  refine ⟨143772576162209603230017527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95848384108139735486678351 143772576162209603230017527)
  ·
    refine ⟨215658864243314404845026291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143772576162209603230017527 215658864243314404845026291)
    ·
      refine ⟨323488296364971607267539437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215658864243314404845026291 323488296364971607267539437)
      ·
        refine ⟨121308111136864352725327289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323488296364971607267539437 121308111136864352725327289)
        ·
          refine ⟨90981083352648264543995467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121308111136864352725327289 90981083352648264543995467)
          ·
            refine ⟨136471625028972396815993201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90981083352648264543995467 136471625028972396815993201)
            ·
              refine ⟨102353718771729297611994901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136471625028972396815993201 102353718771729297611994901)
              ·
                refine ⟨4797830567424810825562261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102353718771729297611994901 4797830567424810825562261)
                ·
                  refine ⟨224898307848038007448231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4797830567424810825562261 224898307848038007448231)
                  ·
                    rfl

theorem cell23_3941891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 6].length) (baseStart_3941891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941891 prefixEnd_3941891 := by exact prefixLift 3941891
  have htrace : WordTrace (prefixWord ++ tailWord_3941891) baseStart_3941891 baseEnd_3941891 := by
    simpa [prefixWord, tailWord_3941891, baseEnd_3941891] using wordTrace_append hprefix tailTrace_3941891
  have hstable : (prefixWord ++ tailWord_3941891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941891).length < 2 ^ (prefixWord ++ tailWord_3941891).sum := by decide
  have hdescent : baseEnd_3941891 < baseStart_3941891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941895 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 3, 4]
def baseStart_3941895 : Nat := 118140960795 + 3941895 * 2 ^ 59
def prefixEnd_3941895 : Nat := 4983230072969 + 3 ^ 40 * 3941895 * 2
def baseEnd_3941895 : Nat := 674695608184986683794687

theorem tailTrace_3941895 : CollatzResearch.WordTrace tailWord_3941895 prefixEnd_3941895 674695608184986683794687 := by
  unfold tailWord_3941895
  simp only [CollatzResearch.WordTrace]
  refine ⟨143772722054195111913163139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95848481369463407942108759 143772722054195111913163139)
  ·
    refine ⟨215659083081292667869744709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143772722054195111913163139 215659083081292667869744709)
    ·
      refine ⟨40436078077742375225577133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215659083081292667869744709 40436078077742375225577133)
      ·
        refine ⟨15163529279153390709591425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40436078077742375225577133 15163529279153390709591425)
        ·
          refine ⟨11372646959365043032193569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15163529279153390709591425 11372646959365043032193569)
          ·
            refine ⟨8529485219523782274145177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11372646959365043032193569 8529485219523782274145177)
            ·
              refine ⟨6397113914642836705608883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8529485219523782274145177 6397113914642836705608883)
              ·
                refine ⟨9595670871964255058413325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6397113914642836705608883 9595670871964255058413325)
                ·
                  refine ⟨3598376576986595646904997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9595670871964255058413325 3598376576986595646904997)
                  ·
                    refine ⟨674695608184986683794687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3598376576986595646904997 674695608184986683794687)
                    ·
                      rfl

theorem cell23_3941895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_3941895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941895 prefixEnd_3941895 := by exact prefixLift 3941895
  have htrace : WordTrace (prefixWord ++ tailWord_3941895) baseStart_3941895 baseEnd_3941895 := by
    simpa [prefixWord, tailWord_3941895, baseEnd_3941895] using wordTrace_append hprefix tailTrace_3941895
  have hstable : (prefixWord ++ tailWord_3941895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941895).length < 2 ^ (prefixWord ++ tailWord_3941895).sum := by decide
  have hdescent : baseEnd_3941895 < baseStart_3941895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941945 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 4, 3, 2]
def baseStart_3941945 : Nat := 118140960795 + 3941945 * 2 ^ 59
def prefixEnd_3941945 : Nat := 4983230072969 + 3 ^ 40 * 3941945 * 2
def baseEnd_3941945 : Nat := 2024112498587684855758831

theorem tailTrace_3941945 : CollatzResearch.WordTrace tailWord_3941945 prefixEnd_3941945 2024112498587684855758831 := by
  unfold tailWord_3941945
  simp only [CollatzResearch.WordTrace]
  refine ⟨143774545704013970452483289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95849697136009313634988859 143774545704013970452483289)
  ·
    refine ⟨107830909278010477839362467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143774545704013970452483289 107830909278010477839362467)
    ·
      refine ⟨161746363917015716759043701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107830909278010477839362467 161746363917015716759043701)
      ·
        refine ⟨15163721617220223446160347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161746363917015716759043701 15163721617220223446160347)
        ·
          refine ⟨22745582425830335169240521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15163721617220223446160347 22745582425830335169240521)
          ·
            refine ⟨17059186819372751376930391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22745582425830335169240521 17059186819372751376930391)
            ·
              refine ⟨25588780229059127065395587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17059186819372751376930391 25588780229059127065395587)
              ·
                refine ⟨38383170343588690598093381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25588780229059127065395587 38383170343588690598093381)
                ·
                  refine ⟨7196844439422879487142509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38383170343588690598093381 7196844439422879487142509)
                  ·
                    refine ⟨2698816664783579807678441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7196844439422879487142509 2698816664783579807678441)
                    ·
                      refine ⟨2024112498587684855758831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698816664783579807678441 2024112498587684855758831)
                      ·
                        rfl

theorem cell23_3941945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_3941945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941945 prefixEnd_3941945 := by exact prefixLift 3941945
  have htrace : WordTrace (prefixWord ++ tailWord_3941945) baseStart_3941945 baseEnd_3941945 := by
    simpa [prefixWord, tailWord_3941945, baseEnd_3941945] using wordTrace_append hprefix tailTrace_3941945
  have hstable : (prefixWord ++ tailWord_3941945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941945).length < 2 ^ (prefixWord ++ tailWord_3941945).sum := by decide
  have hdescent : baseEnd_3941945 < baseStart_3941945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941975 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_3941975 : Nat := 118140960795 + 3941975 * 2 ^ 59
def prefixEnd_3941975 : Nat := 4983230072969 + 3 ^ 40 * 3941975 * 2
def baseEnd_3941975 : Nat := 2024127903007319738383693

theorem tailTrace_3941975 : CollatzResearch.WordTrace tailWord_3941975 prefixEnd_3941975 2024127903007319738383693 := by
  unfold tailWord_3941975
  simp only [CollatzResearch.WordTrace]
  refine ⟨143775639893905285576075379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95850426595936857050716919 143775639893905285576075379)
  ·
    refine ⟨215663459840857928364113069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143775639893905285576075379 215663459840857928364113069)
    ·
      refine ⟨80873797440321723136542401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215663459840857928364113069 80873797440321723136542401)
      ·
        refine ⟨60655348080241292352406801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80873797440321723136542401 60655348080241292352406801)
        ·
          refine ⟨45491511060180969264305101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60655348080241292352406801 45491511060180969264305101)
          ·
            refine ⟨17059316647567863474114413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45491511060180969264305101 17059316647567863474114413)
            ·
              refine ⟨6397243742837948802792905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17059316647567863474114413 6397243742837948802792905)
              ·
                refine ⟨4797932807128461602094679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6397243742837948802792905 4797932807128461602094679)
                ·
                  refine ⟨7196899210692692403142019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797932807128461602094679 7196899210692692403142019)
                  ·
                    refine ⟨10795348816039038604713029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7196899210692692403142019 10795348816039038604713029)
                    ·
                      refine ⟨2024127903007319738383693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10795348816039038604713029 2024127903007319738383693)
                      ·
                        rfl

theorem cell23_3941975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_3941975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941975 prefixEnd_3941975 := by exact prefixLift 3941975
  have htrace : WordTrace (prefixWord ++ tailWord_3941975) baseStart_3941975 baseEnd_3941975 := by
    simpa [prefixWord, tailWord_3941975, baseEnd_3941975] using wordTrace_append hprefix tailTrace_3941975
  have hstable : (prefixWord ++ tailWord_3941975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941975).length < 2 ^ (prefixWord ++ tailWord_3941975).sum := by decide
  have hdescent : baseEnd_3941975 < baseStart_3941975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941988 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3941988 : Nat := 118140960795 + 3941988 * 2 ^ 59
def prefixEnd_3941988 : Nat := 4983230072969 + 3 ^ 40 * 3941988 * 2
def baseEnd_3941988 : Nat := 2024134578255828187521133

theorem tailTrace_3941988 : CollatzResearch.WordTrace tailWord_3941988 prefixEnd_3941988 2024134578255828187521133 := by
  unfold tailWord_3941988
  simp only [CollatzResearch.WordTrace]
  refine ⟨71888057021429094398149309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95850742695238792530865745 71888057021429094398149309)
  ·
    refine ⟨26958021383035910399305991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71888057021429094398149309 26958021383035910399305991)
    ·
      refine ⟨40437032074553865598958987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26958021383035910399305991 40437032074553865598958987)
      ·
        refine ⟨60655548111830798398438481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40437032074553865598958987 60655548111830798398438481)
        ·
          refine ⟨45491661083873098798828861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60655548111830798398438481 45491661083873098798828861)
          ·
            refine ⟨17059372906452412049560823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45491661083873098798828861 17059372906452412049560823)
            ·
              refine ⟨25589059359678618074341235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17059372906452412049560823 25589059359678618074341235)
              ·
                refine ⟨38383589039517927111511853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25589059359678618074341235 38383589039517927111511853)
                ·
                  refine ⟨14393845889819222666816945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38383589039517927111511853 14393845889819222666816945)
                  ·
                    refine ⟨10795384417364417000112709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14393845889819222666816945 10795384417364417000112709)
                    ·
                      refine ⟨2024134578255828187521133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10795384417364417000112709 2024134578255828187521133)
                      ·
                        rfl

theorem cell23_3941988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3941988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941988 prefixEnd_3941988 := by exact prefixLift 3941988
  have htrace : WordTrace (prefixWord ++ tailWord_3941988) baseStart_3941988 baseEnd_3941988 := by
    simpa [prefixWord, tailWord_3941988, baseEnd_3941988] using wordTrace_append hprefix tailTrace_3941988
  have hstable : (prefixWord ++ tailWord_3941988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941988).length < 2 ^ (prefixWord ++ tailWord_3941988).sum := by decide
  have hdescent : baseEnd_3941988 < baseStart_3941988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3941998 : List Nat := [4, 1, 2, 2, 3, 11]
def baseStart_3941998 : Nat := 118140960795 + 3941998 * 2 ^ 59
def prefixEnd_3941998 : Nat := 4983230072969 + 3 ^ 40 * 3941998 * 2
def baseEnd_3941998 : Nat := 8329793057869848347309

theorem tailTrace_3941998 : CollatzResearch.WordTrace tailWord_3941998 prefixEnd_3941998 8329793057869848347309 := by
  unfold tailWord_3941998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972059846602745063020331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95850985848547973669441765 17972059846602745063020331)
  ·
    refine ⟨26958089769904117594530497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17972059846602745063020331 26958089769904117594530497)
    ·
      refine ⟨20218567327428088195897873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26958089769904117594530497 20218567327428088195897873)
      ·
        refine ⟨15163925495571066146923405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20218567327428088195897873 15163925495571066146923405)
        ·
          refine ⟨5686472060839149805096277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15163925495571066146923405 5686472060839149805096277)
          ·
            refine ⟨8329793057869848347309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5686472060839149805096277 8329793057869848347309)
            ·
              rfl

theorem cell23_3941998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 11].length) (baseStart_3941998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3941998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3941998 prefixEnd_3941998 := by exact prefixLift 3941998
  have htrace : WordTrace (prefixWord ++ tailWord_3941998) baseStart_3941998 baseEnd_3941998 := by
    simpa [prefixWord, tailWord_3941998, baseEnd_3941998] using wordTrace_append hprefix tailTrace_3941998
  have hstable : (prefixWord ++ tailWord_3941998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3941998).length < 2 ^ (prefixWord ++ tailWord_3941998).sum := by decide
  have hdescent : baseEnd_3941998 < baseStart_3941998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3941998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942002 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_3942002 : Nat := 118140960795 + 3942002 * 2 ^ 59
def prefixEnd_3942002 : Nat := 4983230072969 + 3 ^ 40 * 3942002 * 2
def baseEnd_3942002 : Nat := 674713922328330377582023

theorem tailTrace_3942002 : CollatzResearch.WordTrace tailWord_3942002 prefixEnd_3942002 674713922328330377582023 := by
  unfold tailWord_3942002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35944156166201867296827065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95851083109871646124872173 35944156166201867296827065)
  ·
    refine ⟨26958117124651400472620299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35944156166201867296827065 26958117124651400472620299)
    ·
      refine ⟨40437175686977100708930449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26958117124651400472620299 40437175686977100708930449)
      ·
        refine ⟨30327881765232825531697837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40437175686977100708930449 30327881765232825531697837)
        ·
          refine ⟨11372955661962309574386689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30327881765232825531697837 11372955661962309574386689)
          ·
            refine ⟨8529716746471732180790017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11372955661962309574386689 8529716746471732180790017)
            ·
              refine ⟨6397287559853799135592513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8529716746471732180790017 6397287559853799135592513)
              ·
                refine ⟨4797965669890349351694385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6397287559853799135592513 4797965669890349351694385)
                ·
                  refine ⟨3598474252417762013770789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4797965669890349351694385 3598474252417762013770789)
                  ·
                    refine ⟨674713922328330377582023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3598474252417762013770789 674713922328330377582023)
                    ·
                      rfl

theorem cell23_3942002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_3942002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942002 prefixEnd_3942002 := by exact prefixLift 3942002
  have htrace : WordTrace (prefixWord ++ tailWord_3942002) baseStart_3942002 baseEnd_3942002 := by
    simpa [prefixWord, tailWord_3942002, baseEnd_3942002] using wordTrace_append hprefix tailTrace_3942002
  have hstable : (prefixWord ++ tailWord_3942002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942002).length < 2 ^ (prefixWord ++ tailWord_3942002).sum := by decide
  have hdescent : baseEnd_3942002 < baseStart_3942002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942009 : List Nat := [1, 2, 1, 3, 3, 1, 3, 4, 1, 2, 2]
def baseStart_3942009 : Nat := 118140960795 + 3942009 * 2 ^ 59
def prefixEnd_3942009 : Nat := 4983230072969 + 3 ^ 40 * 3942009 * 2
def baseEnd_3942009 : Nat := 2024145361349572605358537

theorem tailTrace_3942009 : CollatzResearch.WordTrace tailWord_3942009 prefixEnd_3942009 2024145361349572605358537 := by
  unfold tailWord_3942009
  simp only [CollatzResearch.WordTrace]
  refine ⟨143776879975782109382813081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95851253317188072921875387 143776879975782109382813081)
  ·
    refine ⟨107832659981836582037109811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143776879975782109382813081 107832659981836582037109811)
    ·
      refine ⟨161748989972754873055664717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107832659981836582037109811 161748989972754873055664717)
      ·
        refine ⟨60655871239783077395874269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161748989972754873055664717 60655871239783077395874269)
        ·
          refine ⟨22745951714918654023452851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60655871239783077395874269 22745951714918654023452851)
          ·
            refine ⟨34118927572377981035179277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22745951714918654023452851 34118927572377981035179277)
            ·
              refine ⟨12794597839641742888192229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34118927572377981035179277 12794597839641742888192229)
              ·
                refine ⟨2398987094932826791536043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12794597839641742888192229 2398987094932826791536043)
                ·
                  refine ⟨3598480642399240187304065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398987094932826791536043 3598480642399240187304065)
                  ·
                    refine ⟨2698860481799430140478049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3598480642399240187304065 2698860481799430140478049)
                    ·
                      refine ⟨2024145361349572605358537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698860481799430140478049 2024145361349572605358537)
                      ·
                        rfl

theorem cell23_3942009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_3942009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942009 prefixEnd_3942009 := by exact prefixLift 3942009
  have htrace : WordTrace (prefixWord ++ tailWord_3942009) baseStart_3942009 baseEnd_3942009 := by
    simpa [prefixWord, tailWord_3942009, baseEnd_3942009] using wordTrace_append hprefix tailTrace_3942009
  have hstable : (prefixWord ++ tailWord_3942009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942009).length < 2 ^ (prefixWord ++ tailWord_3942009).sum := by decide
  have hdescent : baseEnd_3942009 < baseStart_3942009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942011 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 9]
def baseStart_3942011 : Nat := 118140960795 + 3942011 * 2 ^ 59
def prefixEnd_3942011 : Nat := 4983230072969 + 3 ^ 40 * 3942011 * 2
def baseEnd_3942011 : Nat := 674715462770293865844509

theorem tailTrace_3942011 : CollatzResearch.WordTrace tailWord_3942011 prefixEnd_3942011 674715462770293865844509 := by
  unfold tailWord_3942011
  simp only [CollatzResearch.WordTrace]
  refine ⟨143776952921774863724385887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95851301947849909149590591 143776952921774863724385887)
  ·
    refine ⟨215665429382662295586578831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143776952921774863724385887 215665429382662295586578831)
    ·
      refine ⟨323498144073993443379868247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215665429382662295586578831 323498144073993443379868247)
      ·
        refine ⟨485247216110990165069802371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323498144073993443379868247 485247216110990165069802371)
        ·
          refine ⟨727870824166485247604703557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485247216110990165069802371 727870824166485247604703557)
          ·
            refine ⟨136475779531215983925881917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 727870824166485247604703557 136475779531215983925881917)
            ·
              refine ⟨51178417324205993972205719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136475779531215983925881917 51178417324205993972205719)
              ·
                refine ⟨76767625986308990958308579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51178417324205993972205719 76767625986308990958308579)
                ·
                  refine ⟨115151438979463486437462869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76767625986308990958308579 115151438979463486437462869)
                  ·
                    refine ⟨674715462770293865844509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115151438979463486437462869 674715462770293865844509)
                    ·
                      rfl

theorem cell23_3942011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_3942011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942011 prefixEnd_3942011 := by exact prefixLift 3942011
  have htrace : WordTrace (prefixWord ++ tailWord_3942011) baseStart_3942011 baseEnd_3942011 := by
    simpa [prefixWord, tailWord_3942011, baseEnd_3942011] using wordTrace_append hprefix tailTrace_3942011
  have hstable : (prefixWord ++ tailWord_3942011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942011).length < 2 ^ (prefixWord ++ tailWord_3942011).sum := by decide
  have hdescent : baseEnd_3942011 < baseStart_3942011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942031 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_3942031 : Nat := 118140960795 + 3942031 * 2 ^ 59
def prefixEnd_3942031 : Nat := 4983230072969 + 3 ^ 40 * 3942031 * 2
def baseEnd_3942031 : Nat := 2024156657923971519283435

theorem tailTrace_3942031 : CollatzResearch.WordTrace tailWord_3942031 prefixEnd_3942031 2024156657923971519283435 := by
  unfold tailWord_3942031
  simp only [CollatzResearch.WordTrace]
  refine ⟨143777682381702407140113947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95851788254468271426742631 143777682381702407140113947)
  ·
    refine ⟨215666523572553610710170921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143777682381702407140113947 215666523572553610710170921)
    ·
      refine ⟨161749892679415208032628191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215666523572553610710170921 161749892679415208032628191)
      ·
        refine ⟨242624839019122812048942287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161749892679415208032628191 242624839019122812048942287)
        ·
          refine ⟨363937258528684218073413431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242624839019122812048942287 363937258528684218073413431)
          ·
            refine ⟨545905887793026327110120147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363937258528684218073413431 545905887793026327110120147)
            ·
              refine ⟨818858831689539490665180221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545905887793026327110120147 818858831689539490665180221)
              ·
                refine ⟨307072061883577308999442583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 818858831689539490665180221 307072061883577308999442583)
                ·
                  refine ⟨460608092825365963499163875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307072061883577308999442583 460608092825365963499163875)
                  ·
                    refine ⟨690912139238048945248745813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460608092825365963499163875 690912139238048945248745813)
                    ·
                      refine ⟨2024156657923971519283435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 690912139238048945248745813 2024156657923971519283435)
                      ·
                        rfl

theorem cell23_3942031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_3942031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942031 prefixEnd_3942031 := by exact prefixLift 3942031
  have htrace : WordTrace (prefixWord ++ tailWord_3942031) baseStart_3942031 baseEnd_3942031 := by
    simpa [prefixWord, tailWord_3942031, baseEnd_3942031] using wordTrace_append hprefix tailTrace_3942031
  have hstable : (prefixWord ++ tailWord_3942031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942031).length < 2 ^ (prefixWord ++ tailWord_3942031).sum := by decide
  have hdescent : baseEnd_3942031 < baseStart_3942031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942046 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_3942046 : Nat := 118140960795 + 3942046 * 2 ^ 59
def prefixEnd_3942046 : Nat := 4983230072969 + 3 ^ 40 * 3942046 * 2
def baseEnd_3942046 : Nat := 2024164360133788960595867

theorem tailTrace_3942046 : CollatzResearch.WordTrace tailWord_3942046 prefixEnd_3942046 2024164360133788960595867 := by
  unfold tailWord_3942046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972278684581008087738749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95852152984432043134606661 17972278684581008087738749)
  ·
    refine ⟨6739604506717878032902031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17972278684581008087738749 6739604506717878032902031)
    ·
      refine ⟨10109406760076817049353047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739604506717878032902031 10109406760076817049353047)
      ·
        refine ⟨15164110140115225574029571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10109406760076817049353047 15164110140115225574029571)
        ·
          refine ⟨22746165210172838361044357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15164110140115225574029571 22746165210172838361044357)
          ·
            refine ⟨4264905976907407192695817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22746165210172838361044357 4264905976907407192695817)
            ·
              refine ⟨3198679482680555394521863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264905976907407192695817 3198679482680555394521863)
              ·
                refine ⟨4798019224020833091782795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198679482680555394521863 4798019224020833091782795)
                ·
                  refine ⟨7197028836031249637674193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798019224020833091782795 7197028836031249637674193)
                  ·
                    refine ⟨5397771627023437228255645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7197028836031249637674193 5397771627023437228255645)
                    ·
                      refine ⟨2024164360133788960595867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5397771627023437228255645 2024164360133788960595867)
                      ·
                        rfl

theorem cell23_3942046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_3942046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942046 prefixEnd_3942046 := by exact prefixLift 3942046
  have htrace : WordTrace (prefixWord ++ tailWord_3942046) baseStart_3942046 baseEnd_3942046 := by
    simpa [prefixWord, tailWord_3942046, baseEnd_3942046] using wordTrace_append hprefix tailTrace_3942046
  have hstable : (prefixWord ++ tailWord_3942046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942046).length < 2 ^ (prefixWord ++ tailWord_3942046).sum := by decide
  have hdescent : baseEnd_3942046 < baseStart_3942046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942088 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 7]
def baseStart_3942088 : Nat := 118140960795 + 3942088 * 2 ^ 59
def prefixEnd_3942088 : Nat := 4983230072969 + 3 ^ 40 * 3942088 * 2
def baseEnd_3942088 : Nat := 224909547369030866252297

theorem tailTrace_3942088 : CollatzResearch.WordTrace tailWord_3942088 prefixEnd_3942088 224909547369030866252297 := by
  unfold tailWord_3942088
  simp only [CollatzResearch.WordTrace]
  refine ⟨71889880671247952937469459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95853174228330603916625945 71889880671247952937469459)
  ·
    refine ⟨107834821006871929406204189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71889880671247952937469459 107834821006871929406204189)
    ·
      refine ⟨40438057877576973527326571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107834821006871929406204189 40438057877576973527326571)
      ·
        refine ⟨60657086816365460290989857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40438057877576973527326571 60657086816365460290989857)
        ·
          refine ⟨45492815112274095218242393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60657086816365460290989857 45492815112274095218242393)
          ·
            refine ⟨34119611334205571413681795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45492815112274095218242393 34119611334205571413681795)
            ·
              refine ⟨51179417001308357120522693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34119611334205571413681795 51179417001308357120522693)
              ·
                refine ⟨9596140687745316960098005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51179417001308357120522693 9596140687745316960098005)
                ·
                  refine ⟨224909547369030866252297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9596140687745316960098005 224909547369030866252297)
                  ·
                    rfl

theorem cell23_3942088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 7].length) (baseStart_3942088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942088 prefixEnd_3942088 := by exact prefixLift 3942088
  have htrace : WordTrace (prefixWord ++ tailWord_3942088) baseStart_3942088 baseEnd_3942088 := by
    simpa [prefixWord, tailWord_3942088, baseEnd_3942088] using wordTrace_append hprefix tailTrace_3942088
  have hstable : (prefixWord ++ tailWord_3942088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942088).length < 2 ^ (prefixWord ++ tailWord_3942088).sum := by decide
  have hdescent : baseEnd_3942088 < baseStart_3942088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942155 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 4]
def baseStart_3942155 : Nat := 118140960795 + 3942155 * 2 ^ 59
def prefixEnd_3942155 : Nat := 4983230072969 + 3 ^ 40 * 3942155 * 2
def baseEnd_3942155 : Nat := 2024220329525129034132865

theorem tailTrace_3942155 : CollatzResearch.WordTrace tailWord_3942155 prefixEnd_3942155 2024220329525129034132865 := by
  unfold tailWord_3942155
  simp only [CollatzResearch.WordTrace]
  refine ⟨143782205033253176317627919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95854803355502117545085279 143782205033253176317627919)
  ·
    refine ⟨215673307549879764476441879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143782205033253176317627919 215673307549879764476441879)
    ·
      refine ⟨323509961324819646714662819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215673307549879764476441879 323509961324819646714662819)
      ·
        refine ⟨485264941987229470071994229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323509961324819646714662819 485264941987229470071994229)
        ·
          refine ⟨45493588311302762819249459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 485264941987229470071994229 45493588311302762819249459)
          ·
            refine ⟨68240382466954144228874189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45493588311302762819249459 68240382466954144228874189)
            ·
              refine ⟨25590143425107804085827821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68240382466954144228874189 25590143425107804085827821)
              ·
                refine ⟨9596303784415426532185433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25590143425107804085827821 9596303784415426532185433)
                ·
                  refine ⟨7197227838311569899139075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9596303784415426532185433 7197227838311569899139075)
                  ·
                    refine ⟨10795841757467354848708613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7197227838311569899139075 10795841757467354848708613)
                    ·
                      refine ⟨2024220329525129034132865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10795841757467354848708613 2024220329525129034132865)
                      ·
                        rfl

theorem cell23_3942155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 4].length) (baseStart_3942155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942155 prefixEnd_3942155 := by exact prefixLift 3942155
  have htrace : WordTrace (prefixWord ++ tailWord_3942155) baseStart_3942155 baseEnd_3942155 := by
    simpa [prefixWord, tailWord_3942155, baseEnd_3942155] using wordTrace_append hprefix tailTrace_3942155
  have hstable : (prefixWord ++ tailWord_3942155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942155).length < 2 ^ (prefixWord ++ tailWord_3942155).sum := by decide
  have hdescent : baseEnd_3942155 < baseStart_3942155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942162 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3942162 : Nat := 118140960795 + 3942162 * 2 ^ 59
def prefixEnd_3942162 : Nat := 4983230072969 + 3 ^ 40 * 3942162 * 2
def baseEnd_3942162 : Nat := 2024223923889710506745333

theorem tailTrace_3942162 : CollatzResearch.WordTrace tailWord_3942162 prefixEnd_3942162 2024223923889710506745333 := by
  unfold tailWord_3942162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35945615086056954128283185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95854973562818544342088493 35945615086056954128283185)
  ·
    refine ⟨26959211314542715596212389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35945615086056954128283185 26959211314542715596212389)
    ·
      refine ⟨5054852121476759174289823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26959211314542715596212389 5054852121476759174289823)
      ·
        refine ⟨7582278182215138761434735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054852121476759174289823 7582278182215138761434735)
        ·
          refine ⟨11373417273322708142152103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582278182215138761434735 11373417273322708142152103)
          ·
            refine ⟨17060125909984062213228155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11373417273322708142152103 17060125909984062213228155)
            ·
              refine ⟨25590188864976093319842233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17060125909984062213228155 25590188864976093319842233)
              ·
                refine ⟨19192641648732069989881675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25590188864976093319842233 19192641648732069989881675)
                ·
                  refine ⟨28788962473098104984822513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19192641648732069989881675 28788962473098104984822513)
                  ·
                    refine ⟨21591721854823578738616885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28788962473098104984822513 21591721854823578738616885)
                    ·
                      refine ⟨2024223923889710506745333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21591721854823578738616885 2024223923889710506745333)
                      ·
                        rfl

theorem cell23_3942162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3942162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942162 prefixEnd_3942162 := by exact prefixLift 3942162
  have htrace : WordTrace (prefixWord ++ tailWord_3942162) baseStart_3942162 baseEnd_3942162 := by
    simpa [prefixWord, tailWord_3942162, baseEnd_3942162] using wordTrace_append hprefix tailTrace_3942162
  have hstable : (prefixWord ++ tailWord_3942162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942162).length < 2 ^ (prefixWord ++ tailWord_3942162).sum := by decide
  have hdescent : baseEnd_3942162 < baseStart_3942162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942172 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_3942172 : Nat := 118140960795 + 3942172 * 2 ^ 59
def prefixEnd_3942172 : Nat := 4983230072969 + 3 ^ 40 * 3942172 * 2
def baseEnd_3942172 : Nat := 2024229058696255467620287

theorem tailTrace_3942172 : CollatzResearch.WordTrace tailWord_3942172 prefixEnd_3942172 2024229058696255467620287 := by
  unfold tailWord_3942172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71891412537095794110498385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95855216716127725480664513 71891412537095794110498385)
  ·
    refine ⟨53918559402821845582873789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71891412537095794110498385 53918559402821845582873789)
    ·
      refine ⟨20219459776058192093577671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53918559402821845582873789 20219459776058192093577671)
      ·
        refine ⟨30329189664087288140366507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20219459776058192093577671 30329189664087288140366507)
        ·
          refine ⟨45493784496130932210549761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30329189664087288140366507 45493784496130932210549761)
          ·
            refine ⟨34120338372098199157912321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45493784496130932210549761 34120338372098199157912321)
            ·
              refine ⟨25590253779073649368434241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34120338372098199157912321 25590253779073649368434241)
              ·
                refine ⟨19192690334305237026325681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25590253779073649368434241 19192690334305237026325681)
                ·
                  refine ⟨14394517750728927769744261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19192690334305237026325681 14394517750728927769744261)
                  ·
                    refine ⟨2698972078261673956827049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14394517750728927769744261 2698972078261673956827049)
                    ·
                      refine ⟨2024229058696255467620287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2698972078261673956827049 2024229058696255467620287)
                      ·
                        rfl

theorem cell23_3942172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_3942172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942172 prefixEnd_3942172 := by exact prefixLift 3942172
  have htrace : WordTrace (prefixWord ++ tailWord_3942172) baseStart_3942172 baseEnd_3942172 := by
    simpa [prefixWord, tailWord_3942172, baseEnd_3942172] using wordTrace_append hprefix tailTrace_3942172
  have hstable : (prefixWord ++ tailWord_3942172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942172).length < 2 ^ (prefixWord ++ tailWord_3942172).sum := by decide
  have hdescent : baseEnd_3942172 < baseStart_3942172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942239 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 3]
def baseStart_3942239 : Nat := 118140960795 + 3942239 * 2 ^ 59
def prefixEnd_3942239 : Nat := 4983230072969 + 3 ^ 40 * 3942239 * 2
def baseEnd_3942239 : Nat := 2024263461900106705482479

theorem tailTrace_3942239 : CollatzResearch.WordTrace tailWord_3942239 prefixEnd_3942239 2024263461900106705482479 := by
  unfold tailWord_3942239
  simp only [CollatzResearch.WordTrace]
  refine ⟨143785268764948858663685771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95856845843299239109123847 143785268764948858663685771)
  ·
    refine ⟨215677903147423287995528657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143785268764948858663685771 215677903147423287995528657)
    ·
      refine ⟨161758427360567465996646493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215677903147423287995528657 161758427360567465996646493)
      ·
        refine ⟨60659410260212799748742435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161758427360567465996646493 60659410260212799748742435)
        ·
          refine ⟨90989115390319199623113653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60659410260212799748742435 90989115390319199623113653)
          ·
            refine ⟨8530229567842424964666905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90989115390319199623113653 8530229567842424964666905)
            ·
              refine ⟨6397672175881818723500179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530229567842424964666905 6397672175881818723500179)
              ·
                refine ⟨9596508263822728085250269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6397672175881818723500179 9596508263822728085250269)
                ·
                  refine ⟨3598690598933523031968851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9596508263822728085250269 3598690598933523031968851)
                  ·
                    refine ⟨5398035898400284547953277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3598690598933523031968851 5398035898400284547953277)
                    ·
                      refine ⟨2024263461900106705482479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5398035898400284547953277 2024263461900106705482479)
                      ·
                        rfl

theorem cell23_3942239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_3942239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942239 prefixEnd_3942239 := by exact prefixLift 3942239
  have htrace : WordTrace (prefixWord ++ tailWord_3942239) baseStart_3942239 baseEnd_3942239 := by
    simpa [prefixWord, tailWord_3942239, baseEnd_3942239] using wordTrace_append hprefix tailTrace_3942239
  have hstable : (prefixWord ++ tailWord_3942239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942239).length < 2 ^ (prefixWord ++ tailWord_3942239).sum := by decide
  have hdescent : baseEnd_3942239 < baseStart_3942239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942265 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_3942265 : Nat := 118140960795 + 3942265 * 2 ^ 59
def prefixEnd_3942265 : Nat := 4983230072969 + 3 ^ 40 * 3942265 * 2
def baseEnd_3942265 : Nat := 2024276812397123603757359

theorem tailTrace_3942265 : CollatzResearch.WordTrace tailWord_3942265 prefixEnd_3942265 2024276812397123603757359 := by
  unfold tailWord_3942265
  simp only [CollatzResearch.WordTrace]
  refine ⟨143786217062854665104132249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95857478041903110069421499 143786217062854665104132249)
  ·
    refine ⟨107839662797140998828099187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143786217062854665104132249 107839662797140998828099187)
    ·
      refine ⟨161759494195711498242148781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107839662797140998828099187 161759494195711498242148781)
      ·
        refine ⟨60659810323391811840805793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161759494195711498242148781 60659810323391811840805793)
        ·
          refine ⟨45494857742543858880604345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60659810323391811840805793 45494857742543858880604345)
          ·
            refine ⟨34121143306907894160453259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45494857742543858880604345 34121143306907894160453259)
            ·
              refine ⟨51181714960361841240679889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34121143306907894160453259 51181714960361841240679889)
              ·
                refine ⟨38386286220271380930509917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51181714960361841240679889 38386286220271380930509917)
                ·
                  refine ⟨14394857332601767848941219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38386286220271380930509917 14394857332601767848941219)
                  ·
                    refine ⟨21592285998902651773411829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14394857332601767848941219 21592285998902651773411829)
                    ·
                      refine ⟨2024276812397123603757359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21592285998902651773411829 2024276812397123603757359)
                      ·
                        rfl

theorem cell23_3942265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_3942265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942265 prefixEnd_3942265 := by exact prefixLift 3942265
  have htrace : WordTrace (prefixWord ++ tailWord_3942265) baseStart_3942265 baseEnd_3942265 := by
    simpa [prefixWord, tailWord_3942265, baseEnd_3942265] using wordTrace_append hprefix tailTrace_3942265
  have hstable : (prefixWord ++ tailWord_3942265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942265).length < 2 ^ (prefixWord ++ tailWord_3942265).sum := by decide
  have hdescent : baseEnd_3942265 < baseStart_3942265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942290 : List Nat := [3, 2, 3, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3942290 : Nat := 118140960795 + 3942290 * 2 ^ 59
def prefixEnd_3942290 : Nat := 4983230072969 + 3 ^ 40 * 3942290 * 2
def baseEnd_3942290 : Nat := 2024289649413486005944745

theorem tailTrace_3942290 : CollatzResearch.WordTrace tailWord_3942290 prefixEnd_3942290 2024289649413486005944745 := by
  unfold tailWord_3942290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35946782221941023593448081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95858085925176062915861549 35946782221941023593448081)
  ·
    refine ⟨26960086666455767695086061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35946782221941023593448081 26960086666455767695086061)
    ·
      refine ⟨10110032499920912885657273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26960086666455767695086061 10110032499920912885657273)
      ·
        refine ⟨7582524374940684664242955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10110032499920912885657273 7582524374940684664242955)
        ·
          refine ⟨11373786562411026996364433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582524374940684664242955 11373786562411026996364433)
          ·
            refine ⟨8530339921808270247273325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11373786562411026996364433 8530339921808270247273325)
            ·
              refine ⟨3198877470678101342727497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8530339921808270247273325 3198877470678101342727497)
              ·
                refine ⟨2399158103008576007045623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198877470678101342727497 2399158103008576007045623)
                ·
                  refine ⟨3598737154512864010568435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399158103008576007045623 3598737154512864010568435)
                  ·
                    refine ⟨5398105731769296015852653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3598737154512864010568435 5398105731769296015852653)
                    ·
                      refine ⟨2024289649413486005944745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5398105731769296015852653 2024289649413486005944745)
                      ·
                        rfl

theorem cell23_3942290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3942290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942290 prefixEnd_3942290 := by exact prefixLift 3942290
  have htrace : WordTrace (prefixWord ++ tailWord_3942290) baseStart_3942290 baseEnd_3942290 := by
    simpa [prefixWord, tailWord_3942290, baseEnd_3942290] using wordTrace_append hprefix tailTrace_3942290
  have hstable : (prefixWord ++ tailWord_3942290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942290).length < 2 ^ (prefixWord ++ tailWord_3942290).sum := by decide
  have hdescent : baseEnd_3942290 < baseStart_3942290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942292 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3942292 : Nat := 118140960795 + 3942292 * 2 ^ 59
def prefixEnd_3942292 : Nat := 4983230072969 + 3 ^ 40 * 3942292 * 2
def baseEnd_3942292 : Nat := 2024290676374794998119735

theorem tailTrace_3942292 : CollatzResearch.WordTrace tailWord_3942292 prefixEnd_3942292 2024290676374794998119735 := by
  unfold tailWord_3942292
  simp only [CollatzResearch.WordTrace]
  refine ⟨71893600916878424357682565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95858134555837899143576753 71893600916878424357682565)
  ·
    refine ⟨13480050171914704567065481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71893600916878424357682565 13480050171914704567065481)
    ·
      refine ⟨10110037628936028425299111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13480050171914704567065481 10110037628936028425299111)
      ·
        refine ⟨15165056443404042637948667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110037628936028425299111 15165056443404042637948667)
        ·
          refine ⟨22747584665106063956923001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15165056443404042637948667 22747584665106063956923001)
          ·
            refine ⟨17060688498829547967692251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22747584665106063956923001 17060688498829547967692251)
            ·
              refine ⟨25591032748244321951538377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17060688498829547967692251 25591032748244321951538377)
              ·
                refine ⟨19193274561183241463653783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25591032748244321951538377 19193274561183241463653783)
                ·
                  refine ⟨28789911841774862195480675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19193274561183241463653783 28789911841774862195480675)
                  ·
                    refine ⟨43184867762662293293221013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28789911841774862195480675 43184867762662293293221013)
                    ·
                      refine ⟨2024290676374794998119735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43184867762662293293221013 2024290676374794998119735)
                      ·
                        rfl

theorem cell23_3942292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3942292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942292 prefixEnd_3942292 := by exact prefixLift 3942292
  have htrace : WordTrace (prefixWord ++ tailWord_3942292) baseStart_3942292 baseEnd_3942292 := by
    simpa [prefixWord, tailWord_3942292, baseEnd_3942292] using wordTrace_append hprefix tailTrace_3942292
  have hstable : (prefixWord ++ tailWord_3942292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942292).length < 2 ^ (prefixWord ++ tailWord_3942292).sum := by decide
  have hdescent : baseEnd_3942292 < baseStart_3942292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942306 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3942306 : Nat := 118140960795 + 3942306 * 2 ^ 59
def prefixEnd_3942306 : Nat := 4983230072969 + 3 ^ 40 * 3942306 * 2
def baseEnd_3942306 : Nat := 674765955034652647781557

theorem tailTrace_3942306 : CollatzResearch.WordTrace tailWord_3942306 prefixEnd_3942306 674765955034652647781557 := by
  unfold tailWord_3942306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35946928113926532276593693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95858474970470752737583181 35946928113926532276593693)
  ·
    refine ⟨13480098042722449603722635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35946928113926532276593693 13480098042722449603722635)
    ·
      refine ⟨20220147064083674405583953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13480098042722449603722635 20220147064083674405583953)
      ·
        refine ⟨15165110298062755804187965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20220147064083674405583953 15165110298062755804187965)
        ·
          refine ⟨5686916361773533426570487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15165110298062755804187965 5686916361773533426570487)
          ·
            refine ⟨8530374542660300139855731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686916361773533426570487 8530374542660300139855731)
            ·
              refine ⟨12795561813990450209783597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530374542660300139855731 12795561813990450209783597)
              ·
                refine ⟨4798335680246418828668849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12795561813990450209783597 4798335680246418828668849)
                ·
                  refine ⟨3598751760184814121501637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4798335680246418828668849 3598751760184814121501637)
                  ·
                    refine ⟨674765955034652647781557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3598751760184814121501637 674765955034652647781557)
                    ·
                      rfl

theorem cell23_3942306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3942306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942306 prefixEnd_3942306 := by exact prefixLift 3942306
  have htrace : WordTrace (prefixWord ++ tailWord_3942306) baseStart_3942306 baseEnd_3942306 := by
    simpa [prefixWord, tailWord_3942306, baseEnd_3942306] using wordTrace_append hprefix tailTrace_3942306
  have hstable : (prefixWord ++ tailWord_3942306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942306).length < 2 ^ (prefixWord ++ tailWord_3942306).sum := by decide
  have hdescent : baseEnd_3942306 < baseStart_3942306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942345 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 4, 6]
def baseStart_3942345 : Nat := 118140960795 + 3942345 * 2 ^ 59
def prefixEnd_3942345 : Nat := 4983230072969 + 3 ^ 40 * 3942345 * 2
def baseEnd_3942345 : Nat := 674772630283161096918997

theorem tailTrace_3942345 : CollatzResearch.WordTrace tailWord_3942345 prefixEnd_3942345 674772630283161096918997 := by
  unfold tailWord_3942345
  simp only [CollatzResearch.WordTrace]
  refine ⟨143789134902564838767044489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95859423268376559178029659 143789134902564838767044489)
  ·
    refine ⟨107841851176923629075283367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143789134902564838767044489 107841851176923629075283367)
    ·
      refine ⟨161762776765385443612925051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107841851176923629075283367 161762776765385443612925051)
      ·
        refine ⟨242644165148078165419387577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161762776765385443612925051 242644165148078165419387577)
        ·
          refine ⟨181983123861058624064540683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242644165148078165419387577 181983123861058624064540683)
          ·
            refine ⟨272974685791587936096811025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181983123861058624064540683 272974685791587936096811025)
            ·
              refine ⟨204731014343690952072608269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272974685791587936096811025 204731014343690952072608269)
              ·
                refine ⟨76774130378884107027228101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204731014343690952072608269 76774130378884107027228101)
                ·
                  refine ⟨14395149446040770067605269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76774130378884107027228101 14395149446040770067605269)
                  ·
                    refine ⟨674772630283161096918997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14395149446040770067605269 674772630283161096918997)
                    ·
                      rfl

theorem cell23_3942345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_3942345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942345 prefixEnd_3942345 := by exact prefixLift 3942345
  have htrace : WordTrace (prefixWord ++ tailWord_3942345) baseStart_3942345 baseEnd_3942345 := by
    simpa [prefixWord, tailWord_3942345, baseEnd_3942345] using wordTrace_append hprefix tailTrace_3942345
  have hstable : (prefixWord ++ tailWord_3942345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942345).length < 2 ^ (prefixWord ++ tailWord_3942345).sum := by decide
  have hdescent : baseEnd_3942345 < baseStart_3942345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942369 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_3942369 : Nat := 118140960795 + 3942369 * 2 ^ 59
def prefixEnd_3942369 : Nat := 4983230072969 + 3 ^ 40 * 3942369 * 2
def baseEnd_3942369 : Nat := 2024330214385191196856881

theorem tailTrace_3942369 : CollatzResearch.WordTrace tailWord_3942369 prefixEnd_3942369 2024330214385191196856881 := by
  unfold tailWord_3942369
  simp only [CollatzResearch.WordTrace]
  refine ⟨143790010254477890865918161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95860006836318593910612107 143790010254477890865918161)
  ·
    refine ⟨107842507690858418149438621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143790010254477890865918161 107842507690858418149438621)
    ·
      refine ⟨40440940384071906806039483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107842507690858418149438621 40440940384071906806039483)
      ·
        refine ⟨60661410576107860209059225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40440940384071906806039483 60661410576107860209059225)
        ·
          refine ⟨45496057932080895156794419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60661410576107860209059225 45496057932080895156794419)
          ·
            refine ⟨68244086898121342735191629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45496057932080895156794419 68244086898121342735191629)
            ·
              refine ⟨25591532586795503525696861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68244086898121342735191629 25591532586795503525696861)
              ·
                refine ⟨9596824720048313822136323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25591532586795503525696861 9596824720048313822136323)
                ·
                  refine ⟨14395237080072470733204485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9596824720048313822136323 14395237080072470733204485)
                  ·
                    refine ⟨2699106952513588262475841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14395237080072470733204485 2699106952513588262475841)
                    ·
                      refine ⟨2024330214385191196856881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699106952513588262475841 2024330214385191196856881)
                      ·
                        rfl

theorem cell23_3942369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_3942369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942369 prefixEnd_3942369 := by exact prefixLift 3942369
  have htrace : WordTrace (prefixWord ++ tailWord_3942369) baseStart_3942369 baseEnd_3942369 := by
    simpa [prefixWord, tailWord_3942369, baseEnd_3942369] using wordTrace_append hprefix tailTrace_3942369
  have hstable : (prefixWord ++ tailWord_3942369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942369).length < 2 ^ (prefixWord ++ tailWord_3942369).sum := by decide
  have hdescent : baseEnd_3942369 < baseStart_3942369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942372 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_3942372 : Nat := 118140960795 + 3942372 * 2 ^ 59
def prefixEnd_3942372 : Nat := 4983230072969 + 3 ^ 40 * 3942372 * 2
def baseEnd_3942372 : Nat := 2024331754827154685119367

theorem tailTrace_3942372 : CollatzResearch.WordTrace tailWord_3942372 prefixEnd_3942372 2024331754827154685119367 := by
  unfold tailWord_3942372
  simp only [CollatzResearch.WordTrace]
  refine ⟨71895059836733511189138685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95860079782311348252184913 71895059836733511189138685)
  ·
    refine ⟨26960647438775066695927007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71895059836733511189138685 26960647438775066695927007)
    ·
      refine ⟨40440971158162600043890511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26960647438775066695927007 40440971158162600043890511)
      ·
        refine ⟨60661456737243900065835767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40440971158162600043890511 60661456737243900065835767)
        ·
          refine ⟨90992185105865850098753651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60661456737243900065835767 90992185105865850098753651)
          ·
            refine ⟨136488277658798775148130477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90992185105865850098753651 136488277658798775148130477)
            ·
              refine ⟨51183104122049540680548929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136488277658798775148130477 51183104122049540680548929)
              ·
                refine ⟨38387328091537155510411697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51183104122049540680548929 38387328091537155510411697)
                ·
                  refine ⟨28790496068652866632808773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38387328091537155510411697 28790496068652866632808773)
                  ·
                    refine ⟨5398218012872412493651645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28790496068652866632808773 5398218012872412493651645)
                    ·
                      refine ⟨2024331754827154685119367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5398218012872412493651645 2024331754827154685119367)
                      ·
                        rfl

theorem cell23_3942372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_3942372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942372 prefixEnd_3942372 := by exact prefixLift 3942372
  have htrace : WordTrace (prefixWord ++ tailWord_3942372) baseStart_3942372 baseEnd_3942372 := by
    simpa [prefixWord, tailWord_3942372, baseEnd_3942372] using wordTrace_append hprefix tailTrace_3942372
  have hstable : (prefixWord ++ tailWord_3942372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942372).length < 2 ^ (prefixWord ++ tailWord_3942372).sum := by decide
  have hdescent : baseEnd_3942372 < baseStart_3942372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942472 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_3942472 : Nat := 118140960795 + 3942472 * 2 ^ 59
def prefixEnd_3942472 : Nat := 4983230072969 + 3 ^ 40 * 3942472 * 2
def baseEnd_3942472 : Nat := 2024383102892604293868907

theorem tailTrace_3942472 : CollatzResearch.WordTrace tailWord_3942472 prefixEnd_3942472 2024383102892604293868907 := by
  unfold tailWord_3942472
  simp only [CollatzResearch.WordTrace]
  refine ⟨71896883486552369728458835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95862511315403159637945113 71896883486552369728458835)
  ·
    refine ⟨107845325229828554592688253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71896883486552369728458835 107845325229828554592688253)
    ·
      refine ⟨40441996961185707972258095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107845325229828554592688253 40441996961185707972258095)
      ·
        refine ⟨60662995441778561958387143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40441996961185707972258095 60662995441778561958387143)
        ·
          refine ⟨90994493162667842937580715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60662995441778561958387143 90994493162667842937580715)
          ·
            refine ⟨136491739744001764406371073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90994493162667842937580715 136491739744001764406371073)
            ·
              refine ⟨102368804808001323304778305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136491739744001764406371073 102368804808001323304778305)
              ·
                refine ⟨76776603606000992478583729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102368804808001323304778305 76776603606000992478583729)
                ·
                  refine ⟨57582452704500744358937797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76776603606000992478583729 57582452704500744358937797)
                  ·
                    refine ⟨10796709882093889567300837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57582452704500744358937797 10796709882093889567300837)
                    ·
                      refine ⟨2024383102892604293868907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10796709882093889567300837 2024383102892604293868907)
                      ·
                        rfl

theorem cell23_3942472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_3942472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942472 prefixEnd_3942472 := by exact prefixLift 3942472
  have htrace : WordTrace (prefixWord ++ tailWord_3942472) baseStart_3942472 baseEnd_3942472 := by
    simpa [prefixWord, tailWord_3942472, baseEnd_3942472] using wordTrace_append hprefix tailTrace_3942472
  have hstable : (prefixWord ++ tailWord_3942472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942472).length < 2 ^ (prefixWord ++ tailWord_3942472).sum := by decide
  have hdescent : baseEnd_3942472 < baseStart_3942472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942493 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3942493 : Nat := 118140960795 + 3942493 * 2 ^ 59
def prefixEnd_3942493 : Nat := 4983230072969 + 3 ^ 40 * 3942493 * 2
def baseEnd_3942493 : Nat := 2024393885986348711706311

theorem tailTrace_3942493 : CollatzResearch.WordTrace tailWord_3942493 prefixEnd_3942493 2024393885986348711706311 := by
  unfold tailWord_3942493
  simp only [CollatzResearch.WordTrace]
  refine ⟨143794532906028660043432133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95863021937352440028954755 143794532906028660043432133)
  ·
    refine ⟨26961474919880373758143525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143794532906028660043432133 26961474919880373758143525)
    ·
      refine ⟨5055276547477570079651911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26961474919880373758143525 5055276547477570079651911)
      ·
        refine ⟨7582914821216355119477867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5055276547477570079651911 7582914821216355119477867)
        ·
          refine ⟨11374372231824532679216801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582914821216355119477867 11374372231824532679216801)
          ·
            refine ⟨8530779173868399509412601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11374372231824532679216801 8530779173868399509412601)
            ·
              refine ⟨6398084380401299632059451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530779173868399509412601 6398084380401299632059451)
              ·
                refine ⟨9597126570601949448089177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398084380401299632059451 9597126570601949448089177)
                ·
                  refine ⟨7197844927951462086066883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597126570601949448089177 7197844927951462086066883)
                  ·
                    refine ⟨10796767391927193129100325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7197844927951462086066883 10796767391927193129100325)
                    ·
                      refine ⟨2024393885986348711706311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10796767391927193129100325 2024393885986348711706311)
                      ·
                        rfl

theorem cell23_3942493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3942493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942493 prefixEnd_3942493 := by exact prefixLift 3942493
  have htrace : WordTrace (prefixWord ++ tailWord_3942493) baseStart_3942493 baseEnd_3942493 := by
    simpa [prefixWord, tailWord_3942493, baseEnd_3942493] using wordTrace_append hprefix tailTrace_3942493
  have hstable : (prefixWord ++ tailWord_3942493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942493).length < 2 ^ (prefixWord ++ tailWord_3942493).sum := by decide
  have hdescent : baseEnd_3942493 < baseStart_3942493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942496 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3]
def baseStart_3942496 : Nat := 118140960795 + 3942496 * 2 ^ 59
def prefixEnd_3942496 : Nat := 4983230072969 + 3 ^ 40 * 3942496 * 2
def baseEnd_3942496 : Nat := 2024395426428312199968797

theorem tailTrace_3942496 : CollatzResearch.WordTrace tailWord_3942496 prefixEnd_3942496 2024395426428312199968797 := by
  unfold tailWord_3942496
  simp only [CollatzResearch.WordTrace]
  refine ⟨71897321162508895777895671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95863094883345194370527561 71897321162508895777895671)
  ·
    refine ⟨107845981743763343666843507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71897321162508895777895671 107845981743763343666843507)
    ·
      refine ⟨161768972615645015500265261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107845981743763343666843507 161768972615645015500265261)
      ·
        refine ⟨60663364730866880812599473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161768972615645015500265261 60663364730866880812599473)
        ·
          refine ⟨45497523548150160609449605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60663364730866880812599473 45497523548150160609449605)
          ·
            refine ⟨8530785665278155114271801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45497523548150160609449605 8530785665278155114271801)
            ·
              refine ⟨6398089248958616335703851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530785665278155114271801 6398089248958616335703851)
              ·
                refine ⟨9597133873437924503555777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398089248958616335703851 9597133873437924503555777)
                ·
                  refine ⟨7197850405078443377666833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597133873437924503555777 7197850405078443377666833)
                  ·
                    refine ⟨5398387803808832533250125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7197850405078443377666833 5398387803808832533250125)
                    ·
                      refine ⟨2024395426428312199968797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5398387803808832533250125 2024395426428312199968797)
                      ·
                        rfl

theorem cell23_3942496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_3942496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942496 prefixEnd_3942496 := by exact prefixLift 3942496
  have htrace : WordTrace (prefixWord ++ tailWord_3942496) baseStart_3942496 baseEnd_3942496 := by
    simpa [prefixWord, tailWord_3942496, baseEnd_3942496] using wordTrace_append hprefix tailTrace_3942496
  have hstable : (prefixWord ++ tailWord_3942496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942496).length < 2 ^ (prefixWord ++ tailWord_3942496).sum := by decide
  have hdescent : baseEnd_3942496 < baseStart_3942496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942522 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_3942522 : Nat := 118140960795 + 3942522 * 2 ^ 59
def prefixEnd_3942522 : Nat := 4983230072969 + 3 ^ 40 * 3942522 * 2
def baseEnd_3942522 : Nat := 2024408776925329098243677

theorem tailTrace_3942522 : CollatzResearch.WordTrace tailWord_3942522 prefixEnd_3942522 2024408776925329098243677 := by
  unfold tailWord_3942522
  simp only [CollatzResearch.WordTrace]
  refine ⟨35948897655730899499059455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95863727081949065330825213 35948897655730899499059455)
  ·
    refine ⟨53923346483596349248589183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35948897655730899499059455 53923346483596349248589183)
    ·
      refine ⟨80885019725394523872883775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53923346483596349248589183 80885019725394523872883775)
      ·
        refine ⟨121327529588091785809325663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80885019725394523872883775 121327529588091785809325663)
        ·
          refine ⟨181991294382137678713988495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121327529588091785809325663 181991294382137678713988495)
          ·
            refine ⟨272986941573206518070982743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181991294382137678713988495 272986941573206518070982743)
            ·
              refine ⟨409480412359809777106474115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272986941573206518070982743 409480412359809777106474115)
              ·
                refine ⟨614220618539714665659711173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409480412359809777106474115 614220618539714665659711173)
                ·
                  refine ⟨115166365976196499811195845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 614220618539714665659711173 115166365976196499811195845)
                  ·
                    refine ⟨21593693620536843714599221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115166365976196499811195845 21593693620536843714599221)
                    ·
                      refine ⟨2024408776925329098243677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21593693620536843714599221 2024408776925329098243677)
                      ·
                        rfl

theorem cell23_3942522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_3942522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942522 prefixEnd_3942522 := by exact prefixLift 3942522
  have htrace : WordTrace (prefixWord ++ tailWord_3942522) baseStart_3942522 baseEnd_3942522 := by
    simpa [prefixWord, tailWord_3942522, baseEnd_3942522] using wordTrace_append hprefix tailTrace_3942522
  have hstable : (prefixWord ++ tailWord_3942522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942522).length < 2 ^ (prefixWord ++ tailWord_3942522).sum := by decide
  have hdescent : baseEnd_3942522 < baseStart_3942522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942546 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3942546 : Nat := 118140960795 + 3942546 * 2 ^ 59
def prefixEnd_3942546 : Nat := 4983230072969 + 3 ^ 40 * 3942546 * 2
def baseEnd_3942546 : Nat := 674807033487012334781189

theorem tailTrace_3942546 : CollatzResearch.WordTrace tailWord_3942546 prefixEnd_3942546 674807033487012334781189 := by
  unfold tailWord_3942546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35949116493709162523777873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95864310649891100063407661 35949116493709162523777873)
  ·
    refine ⟨26961837370281871892833405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35949116493709162523777873 26961837370281871892833405)
    ·
      refine ⟨10110689013855701959812527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26961837370281871892833405 10110689013855701959812527)
      ·
        refine ⟨15166033520783552939718791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110689013855701959812527 15166033520783552939718791)
        ·
          refine ⟨22749050281175329409578187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15166033520783552939718791 22749050281175329409578187)
          ·
            refine ⟨34123575421762994114367281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22749050281175329409578187 34123575421762994114367281)
            ·
              refine ⟨25592681566322245585775461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34123575421762994114367281 25592681566322245585775461)
              ·
                refine ⟨4798627793685421047332899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25592681566322245585775461 4798627793685421047332899)
                ·
                  refine ⟨7197941690528131570999349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798627793685421047332899 7197941690528131570999349)
                  ·
                    refine ⟨674807033487012334781189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7197941690528131570999349 674807033487012334781189)
                    ·
                      rfl

theorem cell23_3942546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3942546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942546 prefixEnd_3942546 := by exact prefixLift 3942546
  have htrace : WordTrace (prefixWord ++ tailWord_3942546) baseStart_3942546 baseEnd_3942546 := by
    simpa [prefixWord, tailWord_3942546, baseEnd_3942546] using wordTrace_append hprefix tailTrace_3942546
  have hstable : (prefixWord ++ tailWord_3942546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942546).length < 2 ^ (prefixWord ++ tailWord_3942546).sum := by decide
  have hdescent : baseEnd_3942546 < baseStart_3942546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942549 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3942549 : Nat := 118140960795 + 3942549 * 2 ^ 59
def prefixEnd_3942549 : Nat := 4983230072969 + 3 ^ 40 * 3942549 * 2
def baseEnd_3942549 : Nat := 2024422640903000492606053

theorem tailTrace_3942549 : CollatzResearch.WordTrace tailWord_3942549 prefixEnd_3942549 2024422640903000492606053 := by
  unfold tailWord_3942549
  simp only [CollatzResearch.WordTrace]
  refine ⟨143796575393825781607470701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95864383595883854404980467 143796575393825781607470701)
  ·
    refine ⟨53923715772684668102801513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143796575393825781607470701 53923715772684668102801513)
    ·
      refine ⟨40442786829513501077101135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53923715772684668102801513 40442786829513501077101135)
      ·
        refine ⟨60664180244270251615651703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40442786829513501077101135 60664180244270251615651703)
        ·
          refine ⟨90996270366405377423477555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60664180244270251615651703 90996270366405377423477555)
          ·
            refine ⟨136494405549608066135216333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90996270366405377423477555 136494405549608066135216333)
            ·
              refine ⟨51185402081103024800706125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136494405549608066135216333 51185402081103024800706125)
              ·
                refine ⟨19194525780413634300264797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51185402081103024800706125 19194525780413634300264797)
                ·
                  refine ⟨7197947167655112862599299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19194525780413634300264797 7197947167655112862599299)
                  ·
                    refine ⟨10796920751482669293898949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7197947167655112862599299 10796920751482669293898949)
                    ·
                      refine ⟨2024422640903000492606053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10796920751482669293898949 2024422640903000492606053)
                      ·
                        rfl

theorem cell23_3942549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3942549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942549 prefixEnd_3942549 := by exact prefixLift 3942549
  have htrace : WordTrace (prefixWord ++ tailWord_3942549) baseStart_3942549 baseEnd_3942549 := by
    simpa [prefixWord, tailWord_3942549, baseEnd_3942549] using wordTrace_append hprefix tailTrace_3942549
  have hstable : (prefixWord ++ tailWord_3942549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942549).length < 2 ^ (prefixWord ++ tailWord_3942549).sum := by decide
  have hdescent : baseEnd_3942549 < baseStart_3942549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942560 : List Nat := [2, 1, 1, 4, 2, 3, 2, 3, 1, 1, 3]
def baseStart_3942560 : Nat := 118140960795 + 3942560 * 2 ^ 59
def prefixEnd_3942560 : Nat := 4983230072969 + 3 ^ 40 * 3942560 * 2
def baseEnd_3942560 : Nat := 2024428289190199949568503

theorem tailTrace_3942560 : CollatzResearch.WordTrace tailWord_3942560 prefixEnd_3942560 2024428289190199949568503 := by
  unfold tailWord_3942560
  simp only [CollatzResearch.WordTrace]
  refine ⟨71898488298392965243060567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95864651064523953657414089 71898488298392965243060567)
  ·
    refine ⟨107847732447589447864590851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71898488298392965243060567 107847732447589447864590851)
    ·
      refine ⟨161771598671384171796886277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107847732447589447864590851 161771598671384171796886277)
      ·
        refine ⟨30332174750884532211916177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161771598671384171796886277 30332174750884532211916177)
        ·
          refine ⟨22749131063163399158937133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30332174750884532211916177 22749131063163399158937133)
          ·
            refine ⟨8530924148686274684601425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22749131063163399158937133 8530924148686274684601425)
            ·
              refine ⟨6398193111514706013451069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530924148686274684601425 6398193111514706013451069)
              ·
                refine ⟨2399322416818014755044151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6398193111514706013451069 2399322416818014755044151)
                ·
                  refine ⟨3598983625227022132566227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399322416818014755044151 3598983625227022132566227)
                  ·
                    refine ⟨5398475437840533198849341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3598983625227022132566227 5398475437840533198849341)
                    ·
                      refine ⟨2024428289190199949568503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5398475437840533198849341 2024428289190199949568503)
                      ·
                        rfl

theorem cell23_3942560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_3942560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942560 prefixEnd_3942560 := by exact prefixLift 3942560
  have htrace : WordTrace (prefixWord ++ tailWord_3942560) baseStart_3942560 baseEnd_3942560 := by
    simpa [prefixWord, tailWord_3942560, baseEnd_3942560] using wordTrace_append hprefix tailTrace_3942560
  have hstable : (prefixWord ++ tailWord_3942560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942560).length < 2 ^ (prefixWord ++ tailWord_3942560).sum := by decide
  have hdescent : baseEnd_3942560 < baseStart_3942560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942583 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 3, 2, 2]
def baseStart_3942583 : Nat := 118140960795 + 3942583 * 2 ^ 59
def prefixEnd_3942583 : Nat := 4983230072969 + 3 ^ 40 * 3942583 * 2
def baseEnd_3942583 : Nat := 2024440099245253359580897

theorem tailTrace_3942583 : CollatzResearch.WordTrace tailWord_3942583 prefixEnd_3942583 2024440099245253359580897 := by
  unfold tailWord_3942583
  simp only [CollatzResearch.WordTrace]
  refine ⟨143797815475702605414208403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95865210317135070276138935 143797815475702605414208403)
  ·
    refine ⟨215696723213553908121312605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143797815475702605414208403 215696723213553908121312605)
    ·
      refine ⟨80886271205082715545492227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215696723213553908121312605 80886271205082715545492227)
      ·
        refine ⟨121329406807624073318238341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80886271205082715545492227 121329406807624073318238341)
        ·
          refine ⟨22749263776429513747169689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121329406807624073318238341 22749263776429513747169689)
          ·
            refine ⟨17061947832322135310377267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22749263776429513747169689 17061947832322135310377267)
            ·
              refine ⟨25592921748483202965565901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17061947832322135310377267 25592921748483202965565901)
              ·
                refine ⟨9597345655681201112087213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25592921748483202965565901 9597345655681201112087213)
                ·
                  refine ⟨3599004620880450417032705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9597345655681201112087213 3599004620880450417032705)
                  ·
                    refine ⟨2699253465660337812774529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599004620880450417032705 2699253465660337812774529)
                    ·
                      refine ⟨2024440099245253359580897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699253465660337812774529 2024440099245253359580897)
                      ·
                        rfl

theorem cell23_3942583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_3942583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942583 prefixEnd_3942583 := by exact prefixLift 3942583
  have htrace : WordTrace (prefixWord ++ tailWord_3942583) baseStart_3942583 baseEnd_3942583 := by
    simpa [prefixWord, tailWord_3942583, baseEnd_3942583] using wordTrace_append hprefix tailTrace_3942583
  have hstable : (prefixWord ++ tailWord_3942583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942583).length < 2 ^ (prefixWord ++ tailWord_3942583).sum := by decide
  have hdescent : baseEnd_3942583 < baseStart_3942583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942596 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3942596 : Nat := 118140960795 + 3942596 * 2 ^ 59
def prefixEnd_3942596 : Nat := 4983230072969 + 3 ^ 40 * 3942596 * 2
def baseEnd_3942596 : Nat := 2024446774493761808718337

theorem tailTrace_3942596 : CollatzResearch.WordTrace tailWord_3942596 prefixEnd_3942596 2024446774493761808718337 := by
  unfold tailWord_3942596
  simp only [CollatzResearch.WordTrace]
  refine ⟨71899144812327754317215821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95865526416437005756287761 71899144812327754317215821)
  ·
    refine ⟨26962179304622907868955933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71899144812327754317215821 26962179304622907868955933)
    ·
      refine ⟨10110817239233590450858475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26962179304622907868955933 10110817239233590450858475)
      ·
        refine ⟨15166225858850385676287713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110817239233590450858475 15166225858850385676287713)
        ·
          refine ⟨11374669394137789257215785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15166225858850385676287713 11374669394137789257215785)
          ·
            refine ⟨8531002045603341942911839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11374669394137789257215785 8531002045603341942911839)
            ·
              refine ⟨12796503068405012914367759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8531002045603341942911839 12796503068405012914367759)
              ·
                refine ⟨19194754602607519371551639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12796503068405012914367759 19194754602607519371551639)
                ·
                  refine ⟨28792131903911279057327459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19194754602607519371551639 28792131903911279057327459)
                  ·
                    refine ⟨43188197855866918585991189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28792131903911279057327459 43188197855866918585991189)
                    ·
                      refine ⟨2024446774493761808718337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43188197855866918585991189 2024446774493761808718337)
                      ·
                        rfl

theorem cell23_3942596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3942596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942596 prefixEnd_3942596 := by exact prefixLift 3942596
  have htrace : WordTrace (prefixWord ++ tailWord_3942596) baseStart_3942596 baseEnd_3942596 := by
    simpa [prefixWord, tailWord_3942596, baseEnd_3942596] using wordTrace_append hprefix tailTrace_3942596
  have hstable : (prefixWord ++ tailWord_3942596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942596).length < 2 ^ (prefixWord ++ tailWord_3942596).sum := by decide
  have hdescent : baseEnd_3942596 < baseStart_3942596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942606 : List Nat := [4, 1, 1, 1, 4, 1, 4, 7]
def baseStart_3942606 : Nat := 118140960795 + 3942606 * 2 ^ 59
def prefixEnd_3942606 : Nat := 4983230072969 + 3 ^ 40 * 3942606 * 2
def baseEnd_3942606 : Nat := 74979700344455806281233

theorem tailTrace_3942606 : CollatzResearch.WordTrace tailWord_3942606 prefixEnd_3942606 74979700344455806281233 := by
  unfold tailWord_3942606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17974831794327410042786959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95865769569746186894863781 17974831794327410042786959)
  ·
    refine ⟨26962247691491115064180439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17974831794327410042786959 26962247691491115064180439)
    ·
      refine ⟨40443371537236672596270659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26962247691491115064180439 40443371537236672596270659)
      ·
        refine ⟨60665057305855008894405989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40443371537236672596270659 60665057305855008894405989)
        ·
          refine ⟨11374698244847814167701123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60665057305855008894405989 11374698244847814167701123)
          ·
            refine ⟨17062047367271721251551685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11374698244847814167701123 17062047367271721251551685)
            ·
              refine ⟨3199133881363447734665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17062047367271721251551685 3199133881363447734665941)
              ·
                refine ⟨74979700344455806281233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3199133881363447734665941 74979700344455806281233)
                ·
                  rfl

theorem cell23_3942606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_3942606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942606 prefixEnd_3942606 := by exact prefixLift 3942606
  have htrace : WordTrace (prefixWord ++ tailWord_3942606) baseStart_3942606 baseEnd_3942606 := by
    simpa [prefixWord, tailWord_3942606, baseEnd_3942606] using wordTrace_append hprefix tailTrace_3942606
  have hstable : (prefixWord ++ tailWord_3942606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942606).length < 2 ^ (prefixWord ++ tailWord_3942606).sum := by decide
  have hdescent : baseEnd_3942606 < baseStart_3942606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942620 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3942620 : Nat := 118140960795 + 3942620 * 2 ^ 59
def prefixEnd_3942620 : Nat := 4983230072969 + 3 ^ 40 * 3942620 * 2
def baseEnd_3942620 : Nat := 2024459098029469714818227

theorem tailTrace_3942620 : CollatzResearch.WordTrace tailWord_3942620 prefixEnd_3942620 2024459098029469714818227 := by
  unfold tailWord_3942620
  simp only [CollatzResearch.WordTrace]
  refine ⟨71899582488284280366652657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95866109984379040488870209 71899582488284280366652657)
  ·
    refine ⟨53924686866213210274989493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71899582488284280366652657 53924686866213210274989493)
    ·
      refine ⟨5055439393707488463280265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53924686866213210274989493 5055439393707488463280265)
      ·
        refine ⟨3791579545280616347460199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5055439393707488463280265 3791579545280616347460199)
        ·
          refine ⟨5687369317920924521190299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791579545280616347460199 5687369317920924521190299)
          ·
            refine ⟨8531053976881386781785449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5687369317920924521190299 8531053976881386781785449)
            ·
              refine ⟨6398290482661040086339087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8531053976881386781785449 6398290482661040086339087)
              ·
                refine ⟨9597435723991560129508631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398290482661040086339087 9597435723991560129508631)
                ·
                  refine ⟨14396153585987340194262947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9597435723991560129508631 14396153585987340194262947)
                  ·
                    refine ⟨21594230378981010291394421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14396153585987340194262947 21594230378981010291394421)
                    ·
                      refine ⟨2024459098029469714818227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21594230378981010291394421 2024459098029469714818227)
                      ·
                        rfl

theorem cell23_3942620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3942620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942620 prefixEnd_3942620 := by exact prefixLift 3942620
  have htrace : WordTrace (prefixWord ++ tailWord_3942620) baseStart_3942620 baseEnd_3942620 := by
    simpa [prefixWord, tailWord_3942620, baseEnd_3942620] using wordTrace_append hprefix tailTrace_3942620
  have hstable : (prefixWord ++ tailWord_3942620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942620).length < 2 ^ (prefixWord ++ tailWord_3942620).sum := by decide
  have hdescent : baseEnd_3942620 < baseStart_3942620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942650 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3]
def baseStart_3942650 : Nat := 118140960795 + 3942650 * 2 ^ 59
def prefixEnd_3942650 : Nat := 4983230072969 + 3 ^ 40 * 3942650 * 2
def baseEnd_3942650 : Nat := 2024474502449104597443089

theorem tailTrace_3942650 : CollatzResearch.WordTrace tailWord_3942650 prefixEnd_3942650 2024474502449104597443089 := by
  unfold tailWord_3942650
  simp only [CollatzResearch.WordTrace]
  refine ⟨35950064791614968964224351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95866839444306583904598269 35950064791614968964224351)
  ·
    refine ⟨53925097187422453446336527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35950064791614968964224351 53925097187422453446336527)
    ·
      refine ⟨80887645781133680169504791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53925097187422453446336527 80887645781133680169504791)
      ·
        refine ⟨121331468671700520254257187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80887645781133680169504791 121331468671700520254257187)
        ·
          refine ⟨181997203007550780381385781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121331468671700520254257187 181997203007550780381385781)
          ·
            refine ⟨17062237781957885660754917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181997203007550780381385781 17062237781957885660754917)
            ·
              refine ⟨3199169584117103561391547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17062237781957885660754917 3199169584117103561391547)
              ·
                refine ⟨4798754376175655342087321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199169584117103561391547 4798754376175655342087321)
                ·
                  refine ⟨3599065782131741506565491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4798754376175655342087321 3599065782131741506565491)
                  ·
                    refine ⟨5398598673197612259848237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3599065782131741506565491 5398598673197612259848237)
                    ·
                      refine ⟨2024474502449104597443089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5398598673197612259848237 2024474502449104597443089)
                      ·
                        rfl

theorem cell23_3942650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_3942650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942650 prefixEnd_3942650 := by exact prefixLift 3942650
  have htrace : WordTrace (prefixWord ++ tailWord_3942650) baseStart_3942650 baseEnd_3942650 := by
    simpa [prefixWord, tailWord_3942650, baseEnd_3942650] using wordTrace_append hprefix tailTrace_3942650
  have hstable : (prefixWord ++ tailWord_3942650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942650).length < 2 ^ (prefixWord ++ tailWord_3942650).sum := by decide
  have hdescent : baseEnd_3942650 < baseStart_3942650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942659 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5]
def baseStart_3942659 : Nat := 118140960795 + 3942659 * 2 ^ 59
def prefixEnd_3942659 : Nat := 4983230072969 + 3 ^ 40 * 3942659 * 2
def baseEnd_3942659 : Nat := 2024479123774995062230547

theorem tailTrace_3942659 : CollatzResearch.WordTrace tailWord_3942659 prefixEnd_3942659 2024479123774995062230547 := by
  unfold tailWord_3942659
  simp only [CollatzResearch.WordTrace]
  refine ⟨143800587423427270393975031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95867058282284846929316687 143800587423427270393975031)
  ·
    refine ⟨215700881135140905590962547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143800587423427270393975031 215700881135140905590962547)
    ·
      refine ⟨323551321702711358386443821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215700881135140905590962547 323551321702711358386443821)
      ·
        refine ⟨121331745638516759394916433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323551321702711358386443821 121331745638516759394916433)
        ·
          refine ⟨90998809228887569546187325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121331745638516759394916433 90998809228887569546187325)
          ·
            refine ⟨34124553460832838579820247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90998809228887569546187325 34124553460832838579820247)
            ·
              refine ⟨51186830191249257869730371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34124553460832838579820247 51186830191249257869730371)
              ·
                refine ⟨76780245286873886804595557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51186830191249257869730371 76780245286873886804595557)
                ·
                  refine ⟨14396295991288853775861667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76780245286873886804595557 14396295991288853775861667)
                  ·
                    refine ⟨21594443986933280663792501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14396295991288853775861667 21594443986933280663792501)
                    ·
                      refine ⟨2024479123774995062230547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21594443986933280663792501 2024479123774995062230547)
                      ·
                        rfl

theorem cell23_3942659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_3942659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942659 prefixEnd_3942659 := by exact prefixLift 3942659
  have htrace : WordTrace (prefixWord ++ tailWord_3942659) baseStart_3942659 baseEnd_3942659 := by
    simpa [prefixWord, tailWord_3942659, baseEnd_3942659] using wordTrace_append hprefix tailTrace_3942659
  have hstable : (prefixWord ++ tailWord_3942659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942659).length < 2 ^ (prefixWord ++ tailWord_3942659).sum := by decide
  have hdescent : baseEnd_3942659 < baseStart_3942659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942660 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_3942660 : Nat := 118140960795 + 3942660 * 2 ^ 59
def prefixEnd_3942660 : Nat := 4983230072969 + 3 ^ 40 * 3942660 * 2
def baseEnd_3942660 : Nat := 2024479637255649558318043

theorem tailTrace_3942660 : CollatzResearch.WordTrace tailWord_3942660 prefixEnd_3942660 2024479637255649558318043 := by
  unfold tailWord_3942660
  simp only [CollatzResearch.WordTrace]
  refine ⟨71900311948211823782380717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95867082597615765043174289 71900311948211823782380717)
  ·
    refine ⟨26962616980579433918392769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71900311948211823782380717 26962616980579433918392769)
    ·
      refine ⟨20221962735434575438794577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26962616980579433918392769 20221962735434575438794577)
      ·
        refine ⟨15166472051575931579095933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20221962735434575438794577 15166472051575931579095933)
        ·
          refine ⟨5687427019340974342160975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15166472051575931579095933 5687427019340974342160975)
          ·
            refine ⟨8531140529011461513241463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5687427019340974342160975 8531140529011461513241463)
            ·
              refine ⟨12796710793517192269862195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8531140529011461513241463 12796710793517192269862195)
              ·
                refine ⟨19195066190275788404793293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12796710793517192269862195 19195066190275788404793293)
                ·
                  refine ⟨7198149821353420651797485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19195066190275788404793293 7198149821353420651797485)
                  ·
                    refine ⟨2699306183007532744424057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7198149821353420651797485 2699306183007532744424057)
                    ·
                      refine ⟨2024479637255649558318043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699306183007532744424057 2024479637255649558318043)
                      ·
                        rfl

theorem cell23_3942660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_3942660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942660 prefixEnd_3942660 := by exact prefixLift 3942660
  have htrace : WordTrace (prefixWord ++ tailWord_3942660) baseStart_3942660 baseEnd_3942660 := by
    simpa [prefixWord, tailWord_3942660, baseEnd_3942660] using wordTrace_append hprefix tailTrace_3942660
  have hstable : (prefixWord ++ tailWord_3942660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942660).length < 2 ^ (prefixWord ++ tailWord_3942660).sum := by decide
  have hdescent : baseEnd_3942660 < baseStart_3942660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942673 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 1, 4, 2]
def baseStart_3942673 : Nat := 118140960795 + 3942673 * 2 ^ 59
def prefixEnd_3942673 : Nat := 4983230072969 + 3 ^ 40 * 3942673 * 2
def baseEnd_3942673 : Nat := 2024486312504158007455483

theorem tailTrace_3942673 : CollatzResearch.WordTrace tailWord_3942673 prefixEnd_3942673 2024486312504158007455483 := by
  unfold tailWord_3942673
  simp only [CollatzResearch.WordTrace]
  refine ⟨143801098045376550784984673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95867398696917700523323115 143801098045376550784984673)
  ·
    refine ⟨107850823534032413088738505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143801098045376550784984673 107850823534032413088738505)
    ·
      refine ⟨80888117650524309816553879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107850823534032413088738505 80888117650524309816553879)
      ·
        refine ⟨121332176475786464724830819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80888117650524309816553879 121332176475786464724830819)
        ·
          refine ⟨181998264713679697087246229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121332176475786464724830819 181998264713679697087246229)
          ·
            refine ⟨8531168658453735800964667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181998264713679697087246229 8531168658453735800964667)
            ·
              refine ⟨12796752987680603701447001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8531168658453735800964667 12796752987680603701447001)
              ·
                refine ⟨9597564740760452776085251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12796752987680603701447001 9597564740760452776085251)
                ·
                  refine ⟨14396347111140679164127877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9597564740760452776085251 14396347111140679164127877)
                  ·
                    refine ⟨2699315083338877343273977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14396347111140679164127877 2699315083338877343273977)
                    ·
                      refine ⟨2024486312504158007455483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699315083338877343273977 2024486312504158007455483)
                      ·
                        rfl

theorem cell23_3942673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_3942673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942673 prefixEnd_3942673 := by exact prefixLift 3942673
  have htrace : WordTrace (prefixWord ++ tailWord_3942673) baseStart_3942673 baseEnd_3942673 := by
    simpa [prefixWord, tailWord_3942673, baseEnd_3942673] using wordTrace_append hprefix tailTrace_3942673
  have hstable : (prefixWord ++ tailWord_3942673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942673).length < 2 ^ (prefixWord ++ tailWord_3942673).sum := by decide
  have hdescent : baseEnd_3942673 < baseStart_3942673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942689 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3942689 : Nat := 118140960795 + 3942689 * 2 ^ 59
def prefixEnd_3942689 : Nat := 4983230072969 + 3 ^ 40 * 3942689 * 2
def baseEnd_3942689 : Nat := 2024494528194629944855409

theorem tailTrace_3942689 : CollatzResearch.WordTrace tailWord_3942689 prefixEnd_3942689 2024494528194629944855409 := by
  unfold tailWord_3942689
  simp only [CollatzResearch.WordTrace]
  refine ⟨143801681613318585517567121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95867787742212390345044747 143801681613318585517567121)
  ·
    refine ⟨107851261209988939138175341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143801681613318585517567121 107851261209988939138175341)
    ·
      refine ⟨40444222953745852176815753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107851261209988939138175341 40444222953745852176815753)
      ·
        refine ⟨30333167215309389132611815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40444222953745852176815753 30333167215309389132611815)
        ·
          refine ⟨45499750822964083698917723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30333167215309389132611815 45499750822964083698917723)
          ·
            refine ⟨68249626234446125548376585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45499750822964083698917723 68249626234446125548376585)
            ·
              refine ⟨51187219675834594161282439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68249626234446125548376585 51187219675834594161282439)
              ·
                refine ⟨76780829513751891241923659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51187219675834594161282439 76780829513751891241923659)
                ·
                  refine ⟨115171244270627836862885489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76780829513751891241923659 115171244270627836862885489)
                  ·
                    refine ⟨86378433202970877647164117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115171244270627836862885489 86378433202970877647164117)
                    ·
                      refine ⟨2024494528194629944855409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86378433202970877647164117 2024494528194629944855409)
                      ·
                        rfl

theorem cell23_3942689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3942689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942689 prefixEnd_3942689 := by exact prefixLift 3942689
  have htrace : WordTrace (prefixWord ++ tailWord_3942689) baseStart_3942689 baseEnd_3942689 := by
    simpa [prefixWord, tailWord_3942689, baseEnd_3942689] using wordTrace_append hprefix tailTrace_3942689
  have hstable : (prefixWord ++ tailWord_3942689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942689).length < 2 ^ (prefixWord ++ tailWord_3942689).sum := by decide
  have hdescent : baseEnd_3942689 < baseStart_3942689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942746 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_3942746 : Nat := 118140960795 + 3942746 * 2 ^ 59
def prefixEnd_3942746 : Nat := 4983230072969 + 3 ^ 40 * 3942746 * 2
def baseEnd_3942746 : Nat := 2024523796591936221842647

theorem tailTrace_3942746 : CollatzResearch.WordTrace tailWord_3942746 prefixEnd_3942746 2024523796591936221842647 := by
  unfold tailWord_3942746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35950940143528021063098023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95869173716074722834928061 35950940143528021063098023)
  ·
    refine ⟨53926410215292031594647035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35950940143528021063098023 53926410215292031594647035)
    ·
      refine ⟨80889615322938047391970553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53926410215292031594647035 80889615322938047391970553)
      ·
        refine ⟨60667211492203535543977915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80889615322938047391970553 60667211492203535543977915)
        ·
          refine ⟨91000817238305303315966873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60667211492203535543977915 91000817238305303315966873)
          ·
            refine ⟨68250612928728977486975155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91000817238305303315966873 68250612928728977486975155)
            ·
              refine ⟨102375919393093466230462733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68250612928728977486975155 102375919393093466230462733)
              ·
                refine ⟨38390969772410049836423525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102375919393093466230462733 38390969772410049836423525)
                ·
                  refine ⟨7198306832326884344329411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38390969772410049836423525 7198306832326884344329411)
                  ·
                    refine ⟨10797460248490326516494117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7198306832326884344329411 10797460248490326516494117)
                    ·
                      refine ⟨2024523796591936221842647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10797460248490326516494117 2024523796591936221842647)
                      ·
                        rfl

theorem cell23_3942746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_3942746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942746 prefixEnd_3942746 := by exact prefixLift 3942746
  have htrace : WordTrace (prefixWord ++ tailWord_3942746) baseStart_3942746 baseEnd_3942746 := by
    simpa [prefixWord, tailWord_3942746, baseEnd_3942746] using wordTrace_append hprefix tailTrace_3942746
  have hstable : (prefixWord ++ tailWord_3942746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942746).length < 2 ^ (prefixWord ++ tailWord_3942746).sum := by decide
  have hdescent : baseEnd_3942746 < baseStart_3942746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942833 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 3, 5]
def baseStart_3942833 : Nat := 118140960795 + 3942833 * 2 ^ 59
def prefixEnd_3942833 : Nat := 4983230072969 + 3 ^ 40 * 3942833 * 2
def baseEnd_3942833 : Nat := 674856156469625793818249

theorem tailTrace_3942833 : CollatzResearch.WordTrace tailWord_3942833 prefixEnd_3942833 674856156469625793818249 := by
  unfold tailWord_3942833
  simp only [CollatzResearch.WordTrace]
  refine ⟨143806933724796898110809153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95871289149864598740539435 143806933724796898110809153)
  ·
    refine ⟨107855200293597673583106865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143806933724796898110809153 107855200293597673583106865)
    ·
      refine ⟨80891400220198255187330149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107855200293597673583106865 80891400220198255187330149)
      ·
        refine ⟨15167137541287172847624403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80891400220198255187330149 15167137541287172847624403)
        ·
          refine ⟨22750706311930759271436605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15167137541287172847624403 22750706311930759271436605)
          ·
            refine ⟨8531514866974034726788727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22750706311930759271436605 8531514866974034726788727)
            ·
              refine ⟨12797272300461052090183091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8531514866974034726788727 12797272300461052090183091)
              ·
                refine ⟨19195908450691578135274637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12797272300461052090183091 19195908450691578135274637)
                ·
                  refine ⟨7198465669009341800727989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19195908450691578135274637 7198465669009341800727989)
                  ·
                    refine ⟨674856156469625793818249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7198465669009341800727989 674856156469625793818249)
                    ·
                      rfl

theorem cell23_3942833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_3942833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942833 prefixEnd_3942833 := by exact prefixLift 3942833
  have htrace : WordTrace (prefixWord ++ tailWord_3942833) baseStart_3942833 baseEnd_3942833 := by
    simpa [prefixWord, tailWord_3942833, baseEnd_3942833] using wordTrace_append hprefix tailTrace_3942833
  have hstable : (prefixWord ++ tailWord_3942833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942833).length < 2 ^ (prefixWord ++ tailWord_3942833).sum := by decide
  have hdescent : baseEnd_3942833 < baseStart_3942833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942870 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3942870 : Nat := 118140960795 + 3942870 * 2 ^ 59
def prefixEnd_3942870 : Nat := 4983230072969 + 3 ^ 40 * 3942870 * 2
def baseEnd_3942870 : Nat := 2024587468193093736692077

theorem tailTrace_3942870 : CollatzResearch.WordTrace tailWord_3942870 prefixEnd_3942870 2024587468193093736692077 := by
  unfold tailWord_3942870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988017701603928339369129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95872188817108568953270709 8988017701603928339369129)
  ·
    refine ⟨6741013276202946254526847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8988017701603928339369129 6741013276202946254526847)
    ·
      refine ⟨10111519914304419381790271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6741013276202946254526847 10111519914304419381790271)
      ·
        refine ⟨15167279871456629072685407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10111519914304419381790271 15167279871456629072685407)
        ·
          refine ⟨22750919807184943609028111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15167279871456629072685407 22750919807184943609028111)
          ·
            refine ⟨34126379710777415413542167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22750919807184943609028111 34126379710777415413542167)
            ·
              refine ⟨51189569566166123120313251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34126379710777415413542167 51189569566166123120313251)
              ·
                refine ⟨76784354349249184680469877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51189569566166123120313251 76784354349249184680469877)
                ·
                  refine ⟨7198533220242111063794051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76784354349249184680469877 7198533220242111063794051)
                  ·
                    refine ⟨10797799830363166595691077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7198533220242111063794051 10797799830363166595691077)
                    ·
                      refine ⟨2024587468193093736692077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10797799830363166595691077 2024587468193093736692077)
                      ·
                        rfl

theorem cell23_3942870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3942870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942870 prefixEnd_3942870 := by exact prefixLift 3942870
  have htrace : WordTrace (prefixWord ++ tailWord_3942870) baseStart_3942870 baseEnd_3942870 := by
    simpa [prefixWord, tailWord_3942870, baseEnd_3942870] using wordTrace_append hprefix tailTrace_3942870
  have hstable : (prefixWord ++ tailWord_3942870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942870).length < 2 ^ (prefixWord ++ tailWord_3942870).sum := by decide
  have hdescent : baseEnd_3942870 < baseStart_3942870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942873 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 3]
def baseStart_3942873 : Nat := 118140960795 + 3942873 * 2 ^ 59
def prefixEnd_3942873 : Nat := 4983230072969 + 3 ^ 40 * 3942873 * 2
def baseEnd_3942873 : Nat := 2024589008635057224954563

theorem tailTrace_3942873 : CollatzResearch.WordTrace tailWord_3942873 prefixEnd_3942873 2024589008635057224954563 := by
  unfold tailWord_3942873
  simp only [CollatzResearch.WordTrace]
  refine ⟨143808392644651984942265273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95872261763101323294843515 143808392644651984942265273)
  ·
    refine ⟨107856294483488988706698955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143808392644651984942265273 107856294483488988706698955)
    ·
      refine ⟨161784441725233483060048433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107856294483488988706698955 161784441725233483060048433)
      ·
        refine ⟨121338331293925112295036325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161784441725233483060048433 121338331293925112295036325)
        ·
          refine ⟨22750937117610958555319311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121338331293925112295036325 22750937117610958555319311)
          ·
            refine ⟨34126405676416437832978967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22750937117610958555319311 34126405676416437832978967)
            ·
              refine ⟨51189608514624656749468451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34126405676416437832978967 51189608514624656749468451)
              ·
                refine ⟨76784412771936985124202677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51189608514624656749468451 76784412771936985124202677)
                ·
                  refine ⟨7198538697369092355394001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76784412771936985124202677 7198538697369092355394001)
                  ·
                    refine ⟨5398904023026819266545501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198538697369092355394001 5398904023026819266545501)
                    ·
                      refine ⟨2024589008635057224954563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5398904023026819266545501 2024589008635057224954563)
                      ·
                        rfl

theorem cell23_3942873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_3942873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942873 prefixEnd_3942873 := by exact prefixLift 3942873
  have htrace : WordTrace (prefixWord ++ tailWord_3942873) baseStart_3942873 baseEnd_3942873 := by
    simpa [prefixWord, tailWord_3942873, baseEnd_3942873] using wordTrace_append hprefix tailTrace_3942873
  have hstable : (prefixWord ++ tailWord_3942873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942873).length < 2 ^ (prefixWord ++ tailWord_3942873).sum := by decide
  have hdescent : baseEnd_3942873 < baseStart_3942873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942887 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_3942887 : Nat := 118140960795 + 3942887 * 2 ^ 59
def prefixEnd_3942887 : Nat := 4983230072969 + 3 ^ 40 * 3942887 * 2
def baseEnd_3942887 : Nat := 2024596197364220170179499

theorem tailTrace_3942887 : CollatzResearch.WordTrace tailWord_3942887 prefixEnd_3942887 2024596197364220170179499 := by
  unfold tailWord_3942887
  simp only [CollatzResearch.WordTrace]
  refine ⟨143808903266601265333274915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95872602177734176888849943 143808903266601265333274915)
  ·
    refine ⟨215713354899901897999912373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143808903266601265333274915 215713354899901897999912373)
    ·
      refine ⟨20223127021865802937491785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215713354899901897999912373 20223127021865802937491785)
      ·
        refine ⟨15167345266399352203118839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20223127021865802937491785 15167345266399352203118839)
        ·
          refine ⟨22751017899599028304678259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15167345266399352203118839 22751017899599028304678259)
          ·
            refine ⟨34126526849398542457017389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22751017899599028304678259 34126526849398542457017389)
            ·
              refine ⟨12797447568524453421381521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34126526849398542457017389 12797447568524453421381521)
              ·
                refine ⟨9598085676393340066036141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12797447568524453421381521 9598085676393340066036141)
                ·
                  refine ⟨3599282128647502524763553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9598085676393340066036141 3599282128647502524763553)
                  ·
                    refine ⟨2699461596485626893572665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599282128647502524763553 2699461596485626893572665)
                    ·
                      refine ⟨2024596197364220170179499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699461596485626893572665 2024596197364220170179499)
                      ·
                        rfl

theorem cell23_3942887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_3942887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942887 prefixEnd_3942887 := by exact prefixLift 3942887
  have htrace : WordTrace (prefixWord ++ tailWord_3942887) baseStart_3942887 baseEnd_3942887 := by
    simpa [prefixWord, tailWord_3942887, baseEnd_3942887] using wordTrace_append hprefix tailTrace_3942887
  have hstable : (prefixWord ++ tailWord_3942887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942887).length < 2 ^ (prefixWord ++ tailWord_3942887).sum := by decide
  have hdescent : baseEnd_3942887 < baseStart_3942887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942890 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_3942890 : Nat := 118140960795 + 3942890 * 2 ^ 59
def prefixEnd_3942890 : Nat := 4983230072969 + 3 ^ 40 * 3942890 * 2
def baseEnd_3942890 : Nat := 2024597737806183658441985

theorem tailTrace_3942890 : CollatzResearch.WordTrace tailWord_3942890 prefixEnd_3942890 2024597737806183658441985 := by
  unfold tailWord_3942890
  simp only [CollatzResearch.WordTrace]
  refine ⟨35952253171397599211408531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95872675123726931230422749 35952253171397599211408531)
  ·
    refine ⟨53928379757096398817112797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35952253171397599211408531 53928379757096398817112797)
    ·
      refine ⟨20223142408911149556417299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53928379757096398817112797 20223142408911149556417299)
      ·
        refine ⟨30334713613366724334625949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20223142408911149556417299 30334713613366724334625949)
        ·
          refine ⟨11375517605012521625484731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30334713613366724334625949 11375517605012521625484731)
          ·
            refine ⟨17063276407518782438227097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11375517605012521625484731 17063276407518782438227097)
            ·
              refine ⟨12797457305639086828670323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17063276407518782438227097 12797457305639086828670323)
              ·
                refine ⟨19196185958458630243005485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12797457305639086828670323 19196185958458630243005485)
                ·
                  refine ⟨7198569734421986341127057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19196185958458630243005485 7198569734421986341127057)
                  ·
                    refine ⟨5398927300816489755845293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198569734421986341127057 5398927300816489755845293)
                    ·
                      refine ⟨2024597737806183658441985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5398927300816489755845293 2024597737806183658441985)
                      ·
                        rfl

theorem cell23_3942890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_3942890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942890 prefixEnd_3942890 := by exact prefixLift 3942890
  have htrace : WordTrace (prefixWord ++ tailWord_3942890) baseStart_3942890 baseEnd_3942890 := by
    simpa [prefixWord, tailWord_3942890, baseEnd_3942890] using wordTrace_append hprefix tailTrace_3942890
  have hstable : (prefixWord ++ tailWord_3942890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942890).length < 2 ^ (prefixWord ++ tailWord_3942890).sum := by decide
  have hdescent : baseEnd_3942890 < baseStart_3942890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942901 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3942901 : Nat := 118140960795 + 3942901 * 2 ^ 59
def prefixEnd_3942901 : Nat := 4983230072969 + 3 ^ 40 * 3942901 * 2
def baseEnd_3942901 : Nat := 674867795364461038468145

theorem tailTrace_3942901 : CollatzResearch.WordTrace tailWord_3942901 prefixEnd_3942901 674867795364461038468145 := by
  unfold tailWord_3942901
  simp only [CollatzResearch.WordTrace]
  refine ⟨143809413888550545724284557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95872942592367030482856371 143809413888550545724284557)
  ·
    refine ⟨53928530208206454646606709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143809413888550545724284557 53928530208206454646606709)
    ·
      refine ⟨5055799707019355123119379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53928530208206454646606709 5055799707019355123119379)
      ·
        refine ⟨7583699560529032684679069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5055799707019355123119379 7583699560529032684679069)
        ·
          refine ⟨2843887335198387256754651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7583699560529032684679069 2843887335198387256754651)
          ·
            refine ⟨4265831002797580885131977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843887335198387256754651 4265831002797580885131977)
            ·
              refine ⟨3199373252098185663848983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4265831002797580885131977 3199373252098185663848983)
              ·
                refine ⟨4799059878147278495773475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199373252098185663848983 4799059878147278495773475)
                ·
                  refine ⟨7198589817220917743660213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799059878147278495773475 7198589817220917743660213)
                  ·
                    refine ⟨674867795364461038468145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7198589817220917743660213 674867795364461038468145)
                    ·
                      rfl

theorem cell23_3942901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3942901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942901 prefixEnd_3942901 := by exact prefixLift 3942901
  have htrace : WordTrace (prefixWord ++ tailWord_3942901) baseStart_3942901 baseEnd_3942901 := by
    simpa [prefixWord, tailWord_3942901, baseEnd_3942901] using wordTrace_append hprefix tailTrace_3942901
  have hstable : (prefixWord ++ tailWord_3942901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942901).length < 2 ^ (prefixWord ++ tailWord_3942901).sum := by decide
  have hdescent : baseEnd_3942901 < baseStart_3942901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942904 : List Nat := [2, 1, 2, 1, 1, 4, 4, 3, 1, 2, 2]
def baseStart_3942904 : Nat := 118140960795 + 3942904 * 2 ^ 59
def prefixEnd_3942904 : Nat := 4983230072969 + 3 ^ 40 * 3942904 * 2
def baseEnd_3942904 : Nat := 2024604926535346603666921

theorem tailTrace_3942904 : CollatzResearch.WordTrace tailWord_3942904 prefixEnd_3942904 2024604926535346603666921 := by
  unfold tailWord_3942904
  simp only [CollatzResearch.WordTrace]
  refine ⟨71904761653769838618321883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95873015538359784824429177 71904761653769838618321883)
  ·
    refine ⟨107857142480654757927482825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71904761653769838618321883 107857142480654757927482825)
    ·
      refine ⟨80892856860491068445612119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107857142480654757927482825 80892856860491068445612119)
      ·
        refine ⟨121339285290736602668418179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80892856860491068445612119 121339285290736602668418179)
        ·
          refine ⟨182008927936104904002627269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121339285290736602668418179 182008927936104904002627269)
          ·
            refine ⟨34126673988019669500492613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182008927936104904002627269 34126673988019669500492613)
            ·
              refine ⟨6398751372753688031342365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34126673988019669500492613 6398751372753688031342365)
              ·
                refine ⟨2399531764782633011753387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6398751372753688031342365 2399531764782633011753387)
                ·
                  refine ⟨3599297647173949517630081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399531764782633011753387 3599297647173949517630081)
                  ·
                    refine ⟨2699473235380462138222561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599297647173949517630081 2699473235380462138222561)
                    ·
                      refine ⟨2024604926535346603666921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699473235380462138222561 2024604926535346603666921)
                      ·
                        rfl

theorem cell23_3942904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_3942904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942904 prefixEnd_3942904 := by exact prefixLift 3942904
  have htrace : WordTrace (prefixWord ++ tailWord_3942904) baseStart_3942904 baseEnd_3942904 := by
    simpa [prefixWord, tailWord_3942904, baseEnd_3942904] using wordTrace_append hprefix tailTrace_3942904
  have hstable : (prefixWord ++ tailWord_3942904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942904).length < 2 ^ (prefixWord ++ tailWord_3942904).sum := by decide
  have hdescent : baseEnd_3942904 < baseStart_3942904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942906 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_3942906 : Nat := 118140960795 + 3942906 * 2 ^ 59
def prefixEnd_3942906 : Nat := 4983230072969 + 3 ^ 40 * 3942906 * 2
def baseEnd_3942906 : Nat := 674868651165551865280637

theorem tailTrace_3942906 : CollatzResearch.WordTrace tailWord_3942906 prefixEnd_3942906 674868651165551865280637 := by
  unfold tailWord_3942906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35952399063383107894554143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95873064169021621052144381 35952399063383107894554143)
  ·
    refine ⟨53928598595074661841831215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35952399063383107894554143 53928598595074661841831215)
    ·
      refine ⟨80892897892611992762746823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53928598595074661841831215 80892897892611992762746823)
      ·
        refine ⟨121339346838917989144120235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80892897892611992762746823 121339346838917989144120235)
        ·
          refine ⟨182009020258376983716180353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121339346838917989144120235 182009020258376983716180353)
          ·
            refine ⟨136506765193782737787135265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182009020258376983716180353 136506765193782737787135265)
            ·
              refine ⟨102380073895337053340351449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136506765193782737787135265 102380073895337053340351449)
              ·
                refine ⟨76785055421502790005263587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102380073895337053340351449 76785055421502790005263587)
                ·
                  refine ⟨115177583132254185007895381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76785055421502790005263587 115177583132254185007895381)
                  ·
                    refine ⟨674868651165551865280637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115177583132254185007895381 674868651165551865280637)
                    ·
                      rfl

theorem cell23_3942906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_3942906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942906 prefixEnd_3942906 := by exact prefixLift 3942906
  have htrace : WordTrace (prefixWord ++ tailWord_3942906) baseStart_3942906 baseEnd_3942906 := by
    simpa [prefixWord, tailWord_3942906, baseEnd_3942906] using wordTrace_append hprefix tailTrace_3942906
  have hstable : (prefixWord ++ tailWord_3942906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942906).length < 2 ^ (prefixWord ++ tailWord_3942906).sum := by decide
  have hdescent : baseEnd_3942906 < baseStart_3942906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942947 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 1, 3, 2]
def baseStart_3942947 : Nat := 118140960795 + 3942947 * 2 ^ 59
def prefixEnd_3942947 : Nat := 4983230072969 + 3 ^ 40 * 3942947 * 2
def baseEnd_3942947 : Nat := 2024627006203489935429223

theorem tailTrace_3942947 : CollatzResearch.WordTrace tailWord_3942947 prefixEnd_3942947 2024627006203489935429223 := by
  unfold tailWord_3942947
  simp only [CollatzResearch.WordTrace]
  refine ⟨143811091646383895580459095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95874061097589263720306063 143811091646383895580459095)
  ·
    refine ⟨215716637469575843370688643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143811091646383895580459095 215716637469575843370688643)
    ·
      refine ⟨323574956204363765056032965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215716637469575843370688643 323574956204363765056032965)
      ·
        refine ⟨60670304288318205948006181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323574956204363765056032965 60670304288318205948006181)
        ·
          refine ⟨11375682054059663615251159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60670304288318205948006181 11375682054059663615251159)
          ·
            refine ⟨17063523081089495422876739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11375682054059663615251159 17063523081089495422876739)
            ·
              refine ⟨25595284621634243134315109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17063523081089495422876739 25595284621634243134315109)
              ·
                refine ⟨4799115866556420587684083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25595284621634243134315109 4799115866556420587684083)
                ·
                  refine ⟨7198673799834630881526125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799115866556420587684083 7198673799834630881526125)
                  ·
                    refine ⟨2699502674937986580572297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7198673799834630881526125 2699502674937986580572297)
                    ·
                      refine ⟨2024627006203489935429223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699502674937986580572297 2024627006203489935429223)
                      ·
                        rfl

theorem cell23_3942947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_3942947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942947 prefixEnd_3942947 := by exact prefixLift 3942947
  have htrace : WordTrace (prefixWord ++ tailWord_3942947) baseStart_3942947 baseEnd_3942947 := by
    simpa [prefixWord, tailWord_3942947, baseEnd_3942947] using wordTrace_append hprefix tailTrace_3942947
  have hstable : (prefixWord ++ tailWord_3942947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942947).length < 2 ^ (prefixWord ++ tailWord_3942947).sum := by decide
  have hdescent : baseEnd_3942947 < baseStart_3942947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942960 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 1, 4, 2]
def baseStart_3942960 : Nat := 118140960795 + 3942960 * 2 ^ 59
def prefixEnd_3942960 : Nat := 4983230072969 + 3 ^ 40 * 3942960 * 2
def baseEnd_3942960 : Nat := 2024633681451998384566663

theorem tailTrace_3942960 : CollatzResearch.WordTrace tailWord_3942960 prefixEnd_3942960 2024633681451998384566663 := by
  unfold tailWord_3942960
  simp only [CollatzResearch.WordTrace]
  refine ⟨71905782897668399400341167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95874377196891199200454889 71905782897668399400341167)
  ·
    refine ⟨107858674346502599100511751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71905782897668399400341167 107858674346502599100511751)
    ·
      refine ⟨161788011519753898650767627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107858674346502599100511751 161788011519753898650767627)
      ·
        refine ⟨242682017279630847976151441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161788011519753898650767627 242682017279630847976151441)
        ·
          refine ⟨182011512959723135982113581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242682017279630847976151441 182011512959723135982113581)
          ·
            refine ⟨68254317359896175993292593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182011512959723135982113581 68254317359896175993292593)
            ·
              refine ⟨51190738019922131994969445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68254317359896175993292593 51190738019922131994969445)
              ·
                refine ⟨9598263378735399749056771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51190738019922131994969445 9598263378735399749056771)
                ·
                  refine ⟨14397395068103099623585157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9598263378735399749056771 14397395068103099623585157)
                  ·
                    refine ⟨2699511575269331179422217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14397395068103099623585157 2699511575269331179422217)
                    ·
                      refine ⟨2024633681451998384566663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699511575269331179422217 2024633681451998384566663)
                      ·
                        rfl

theorem cell23_3942960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 4, 2].length) (baseStart_3942960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942960 prefixEnd_3942960 := by exact prefixLift 3942960
  have htrace : WordTrace (prefixWord ++ tailWord_3942960) baseStart_3942960 baseEnd_3942960 := by
    simpa [prefixWord, tailWord_3942960, baseEnd_3942960] using wordTrace_append hprefix tailTrace_3942960
  have hstable : (prefixWord ++ tailWord_3942960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942960).length < 2 ^ (prefixWord ++ tailWord_3942960).sum := by decide
  have hdescent : baseEnd_3942960 < baseStart_3942960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942963 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5]
def baseStart_3942963 : Nat := 118140960795 + 3942963 * 2 ^ 59
def prefixEnd_3942963 : Nat := 4983230072969 + 3 ^ 40 * 3942963 * 2
def baseEnd_3942963 : Nat := 2024635221893961872829149

theorem tailTrace_3942963 : CollatzResearch.WordTrace tailWord_3942963 prefixEnd_3942963 2024635221893961872829149 := by
  unfold tailWord_3942963
  simp only [CollatzResearch.WordTrace]
  refine ⟨143811675214325930313041543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95874450142883953542027695 143811675214325930313041543)
  ·
    refine ⟨215717512821488895469562315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143811675214325930313041543 215717512821488895469562315)
    ·
      refine ⟨323576269232233343204343473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215717512821488895469562315 323576269232233343204343473)
      ·
        refine ⟨242682201924175007403257605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323576269232233343204343473 242682201924175007403257605)
        ·
          refine ⟨45502912860782813888110801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242682201924175007403257605 45502912860782813888110801)
          ·
            refine ⟨34127184645587110416083101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45502912860782813888110801 34127184645587110416083101)
            ·
              refine ⟨12797694242095166406031163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34127184645587110416083101 12797694242095166406031163)
              ·
                refine ⟨19196541363142749609046745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12797694242095166406031163 19196541363142749609046745)
                ·
                  refine ⟨14397406022357062206785059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19196541363142749609046745 14397406022357062206785059)
                  ·
                    refine ⟨21596109033535593310177589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14397406022357062206785059 21596109033535593310177589)
                    ·
                      refine ⟨2024635221893961872829149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21596109033535593310177589 2024635221893961872829149)
                      ·
                        rfl

theorem cell23_3942963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_3942963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942963 prefixEnd_3942963 := by exact prefixLift 3942963
  have htrace : WordTrace (prefixWord ++ tailWord_3942963) baseStart_3942963 baseEnd_3942963 := by
    simpa [prefixWord, tailWord_3942963, baseEnd_3942963] using wordTrace_append hprefix tailTrace_3942963
  have hstable : (prefixWord ++ tailWord_3942963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942963).length < 2 ^ (prefixWord ++ tailWord_3942963).sum := by decide
  have hdescent : baseEnd_3942963 < baseStart_3942963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942994 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_3942994 : Nat := 118140960795 + 3942994 * 2 ^ 59
def prefixEnd_3942994 : Nat := 4983230072969 + 3 ^ 40 * 3942994 * 2
def baseEnd_3942994 : Nat := 2024651139794251251541507

theorem tailTrace_3942994 : CollatzResearch.WordTrace tailWord_3942994 prefixEnd_3942994 2024651139794251251541507 := by
  unfold tailWord_3942994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35953201469303405651855009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95875203918142415071613357 35953201469303405651855009)
  ·
    refine ⟨26964901101977554238891257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35953201469303405651855009 26964901101977554238891257)
    ·
      refine ⟨20223675826483165679168443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26964901101977554238891257 20223675826483165679168443)
      ·
        refine ⟨30335513739724748518752665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20223675826483165679168443 30335513739724748518752665)
        ·
          refine ⟨22751635304793561389064499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30335513739724748518752665 22751635304793561389064499)
          ·
            refine ⟨34127452957190342083596749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22751635304793561389064499 34127452957190342083596749)
            ·
              refine ⟨12797794858946378281348781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34127452957190342083596749 12797794858946378281348781)
              ·
                refine ⟨4799173072104891855505793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12797794858946378281348781 4799173072104891855505793)
                ·
                  refine ⟨3599379804078668891629345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4799173072104891855505793 3599379804078668891629345)
                  ·
                    refine ⟨2699534853059001668722009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599379804078668891629345 2699534853059001668722009)
                    ·
                      refine ⟨2024651139794251251541507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699534853059001668722009 2024651139794251251541507)
                      ·
                        rfl

theorem cell23_3942994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_3942994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3942994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3942994 prefixEnd_3942994 := by exact prefixLift 3942994
  have htrace : WordTrace (prefixWord ++ tailWord_3942994) baseStart_3942994 baseEnd_3942994 := by
    simpa [prefixWord, tailWord_3942994, baseEnd_3942994] using wordTrace_append hprefix tailTrace_3942994
  have hstable : (prefixWord ++ tailWord_3942994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942994).length < 2 ^ (prefixWord ++ tailWord_3942994).sum := by decide
  have hdescent : baseEnd_3942994 < baseStart_3942994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943023 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_3943023 : Nat := 118140960795 + 3943023 * 2 ^ 59
def prefixEnd_3943023 : Nat := 4983230072969 + 3 ^ 40 * 3943023 * 2
def baseEnd_3943023 : Nat := 2024666030733231638078873

theorem tailTrace_3943023 : CollatzResearch.WordTrace tailWord_3943023 prefixEnd_3943023 2024666030733231638078873 := by
  unfold tailWord_3943023
  simp only [CollatzResearch.WordTrace]
  refine ⟨143813863594108560560225723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95875909062739040373483815 143813863594108560560225723)
  ·
    refine ⟨215720795391162840840338585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143813863594108560560225723 215720795391162840840338585)
    ·
      refine ⟨161790596543372130630253939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215720795391162840840338585 161790596543372130630253939)
      ·
        refine ⟨242685894815058195945380909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161790596543372130630253939 242685894815058195945380909)
        ·
          refine ⟨91007210555646823479517841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242685894815058195945380909 91007210555646823479517841)
          ·
            refine ⟨68255407916735117609638381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91007210555646823479517841 68255407916735117609638381)
            ·
              refine ⟨25595777968775669103614393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68255407916735117609638381 25595777968775669103614393)
              ·
                refine ⟨19196833476581751827710795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25595777968775669103614393 19196833476581751827710795)
                ·
                  refine ⟨28795250214872627741566193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19196833476581751827710795 28795250214872627741566193)
                  ·
                    refine ⟨21596437661154470806174645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28795250214872627741566193 21596437661154470806174645)
                    ·
                      refine ⟨2024666030733231638078873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21596437661154470806174645 2024666030733231638078873)
                      ·
                        rfl

theorem cell23_3943023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_3943023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943023 prefixEnd_3943023 := by exact prefixLift 3943023
  have htrace : WordTrace (prefixWord ++ tailWord_3943023) baseStart_3943023 baseEnd_3943023 := by
    simpa [prefixWord, tailWord_3943023, baseEnd_3943023] using wordTrace_append hprefix tailTrace_3943023
  have hstable : (prefixWord ++ tailWord_3943023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943023).length < 2 ^ (prefixWord ++ tailWord_3943023).sum := by decide
  have hdescent : baseEnd_3943023 < baseStart_3943023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943127 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 1, 5, 2]
def baseStart_3943127 : Nat := 118140960795 + 3943127 * 2 ^ 59
def prefixEnd_3943127 : Nat := 4983230072969 + 3 ^ 40 * 3943127 * 2
def baseEnd_3943127 : Nat := 2024719432721299231178395

theorem tailTrace_3943127 : CollatzResearch.WordTrace tailWord_3943127 prefixEnd_3943127 2024719432721299231178395 := by
  unfold tailWord_3943127
  simp only [CollatzResearch.WordTrace]
  refine ⟨143817656785731786322011635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95878437857154524214674423 143817656785731786322011635)
  ·
    refine ⟨215726485178597679483017453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143817656785731786322011635 215726485178597679483017453)
    ·
      refine ⟨80897431941974129806131545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215726485178597679483017453 80897431941974129806131545)
      ·
        refine ⟨60673073956480597354598659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80897431941974129806131545 60673073956480597354598659)
        ·
          refine ⟨91009610934720896031897989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60673073956480597354598659 91009610934720896031897989)
          ·
            refine ⟨17064302050260168005980873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91009610934720896031897989 17064302050260168005980873)
            ·
              refine ⟨12798226537695126004485655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17064302050260168005980873 12798226537695126004485655)
              ·
                refine ⟨19197339806542689006728483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12798226537695126004485655 19197339806542689006728483)
                ·
                  refine ⟨28796009709814033510092725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19197339806542689006728483 28796009709814033510092725)
                  ·
                    refine ⟨2699625910295065641571193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28796009709814033510092725 2699625910295065641571193)
                    ·
                      refine ⟨2024719432721299231178395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699625910295065641571193 2024719432721299231178395)
                      ·
                        rfl

theorem cell23_3943127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_3943127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943127 prefixEnd_3943127 := by exact prefixLift 3943127
  have htrace : WordTrace (prefixWord ++ tailWord_3943127) baseStart_3943127 baseEnd_3943127 := by
    simpa [prefixWord, tailWord_3943127, baseEnd_3943127] using wordTrace_append hprefix tailTrace_3943127
  have hstable : (prefixWord ++ tailWord_3943127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943127).length < 2 ^ (prefixWord ++ tailWord_3943127).sum := by decide
  have hdescent : baseEnd_3943127 < baseStart_3943127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943137 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 1, 5]
def baseStart_3943137 : Nat := 118140960795 + 3943137 * 2 ^ 59
def prefixEnd_3943137 : Nat := 4983230072969 + 3 ^ 40 * 3943137 * 2
def baseEnd_3943137 : Nat := 674908189175948064017783

theorem tailTrace_3943137 : CollatzResearch.WordTrace tailWord_3943137 prefixEnd_3943137 674908189175948064017783 := by
  unfold tailWord_3943137
  simp only [CollatzResearch.WordTrace]
  refine ⟨143818021515695558029875665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95878681010463705353250443 143818021515695558029875665)
  ·
    refine ⟨107863516136771668522406749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143818021515695558029875665 107863516136771668522406749)
    ·
      refine ⟨40448818551289375695902531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107863516136771668522406749 40448818551289375695902531)
      ·
        refine ⟨60673227826934063543853797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40448818551289375695902531 60673227826934063543853797)
        ·
          refine ⟨11376230217550136914472587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60673227826934063543853797 11376230217550136914472587)
          ·
            refine ⟨17064345326325205371708881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11376230217550136914472587 17064345326325205371708881)
            ·
              refine ⟨12798258994743904028781661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17064345326325205371708881 12798258994743904028781661)
              ·
                refine ⟨4799347123028964010793123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12798258994743904028781661 4799347123028964010793123)
                ·
                  refine ⟨7199020684543446016189685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799347123028964010793123 7199020684543446016189685)
                  ·
                    refine ⟨674908189175948064017783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7199020684543446016189685 674908189175948064017783)
                    ·
                      rfl

theorem cell23_3943137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_3943137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943137 prefixEnd_3943137 := by exact prefixLift 3943137
  have htrace : WordTrace (prefixWord ++ tailWord_3943137) baseStart_3943137 baseEnd_3943137 := by
    simpa [prefixWord, tailWord_3943137, baseEnd_3943137] using wordTrace_append hprefix tailTrace_3943137
  have hstable : (prefixWord ++ tailWord_3943137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943137).length < 2 ^ (prefixWord ++ tailWord_3943137).sum := by decide
  have hdescent : baseEnd_3943137 < baseStart_3943137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943160 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_3943160 : Nat := 118140960795 + 3943160 * 2 ^ 59
def prefixEnd_3943160 : Nat := 4983230072969 + 3 ^ 40 * 3943160 * 2
def baseEnd_3943160 : Nat := 2024736377582897602065743

theorem tailTrace_3943160 : CollatzResearch.WordTrace tailWord_3943160 prefixEnd_3943160 2024736377582897602065743 := by
  unfold tailWord_3943160
  simp only [CollatzResearch.WordTrace]
  refine ⟨71909430197306116478981467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95879240263074821971975289 71909430197306116478981467)
  ·
    refine ⟨107864145295959174718472201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71909430197306116478981467 107864145295959174718472201)
    ·
      refine ⟨80898108971969381038854151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107864145295959174718472201 80898108971969381038854151)
      ·
        refine ⟨121347163457954071558281227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80898108971969381038854151 121347163457954071558281227)
        ·
          refine ⟨182020745186931107337421841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121347163457954071558281227 182020745186931107337421841)
          ·
            refine ⟨136515558890198330503066381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182020745186931107337421841 136515558890198330503066381)
            ·
              refine ⟨51193334583824373938649893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136515558890198330503066381 51193334583824373938649893)
              ·
                refine ⟨9598750234467070113496855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51193334583824373938649893 9598750234467070113496855)
                ·
                  refine ⟨14398125351700605170245283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9598750234467070113496855 14398125351700605170245283)
                  ·
                    refine ⟨21597188027550907755367925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14398125351700605170245283 21597188027550907755367925)
                    ·
                      refine ⟨2024736377582897602065743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21597188027550907755367925 2024736377582897602065743)
                      ·
                        rfl

theorem cell23_3943160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_3943160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943160 prefixEnd_3943160 := by exact prefixLift 3943160
  have htrace : WordTrace (prefixWord ++ tailWord_3943160) baseStart_3943160 baseEnd_3943160 := by
    simpa [prefixWord, tailWord_3943160, baseEnd_3943160] using wordTrace_append hprefix tailTrace_3943160
  have hstable : (prefixWord ++ tailWord_3943160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943160).length < 2 ^ (prefixWord ++ tailWord_3943160).sum := by decide
  have hdescent : baseEnd_3943160 < baseStart_3943160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943191 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 1, 1, 4]
def baseStart_3943191 : Nat := 118140960795 + 3943191 * 2 ^ 59
def prefixEnd_3943191 : Nat := 4983230072969 + 3 ^ 40 * 3943191 * 2
def baseEnd_3943191 : Nat := 2024752295483186980778101

theorem tailTrace_3943191 : CollatzResearch.WordTrace tailWord_3943191 prefixEnd_3943191 2024752295483186980778101 := by
  unfold tailWord_3943191
  simp only [CollatzResearch.WordTrace]
  refine ⟨143819991057499925252341427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95879994038333283501560951 143819991057499925252341427)
  ·
    refine ⟨215729986586249887878512141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143819991057499925252341427 215729986586249887878512141)
    ·
      refine ⟨80898744969843707954442053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215729986586249887878512141 80898744969843707954442053)
      ·
        refine ⟨15168514681845695241457885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80898744969843707954442053 15168514681845695241457885)
        ·
          refine ⟨5688193005692135715546707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15168514681845695241457885 5688193005692135715546707)
          ·
            refine ⟨8532289508538203573320061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688193005692135715546707 8532289508538203573320061)
            ·
              refine ⟨3199608565701826339995023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8532289508538203573320061 3199608565701826339995023)
              ·
                refine ⟨4799412848552739509992535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199608565701826339995023 4799412848552739509992535)
                ·
                  refine ⟨7199119272829109264988803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799412848552739509992535 7199119272829109264988803)
                  ·
                    refine ⟨10798678909243663897483205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199119272829109264988803 10798678909243663897483205)
                    ·
                      refine ⟨2024752295483186980778101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10798678909243663897483205 2024752295483186980778101)
                      ·
                        rfl

theorem cell23_3943191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_3943191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943191 prefixEnd_3943191 := by exact prefixLift 3943191
  have htrace : WordTrace (prefixWord ++ tailWord_3943191) baseStart_3943191 baseEnd_3943191 := by
    simpa [prefixWord, tailWord_3943191, baseEnd_3943191] using wordTrace_append hprefix tailTrace_3943191
  have hstable : (prefixWord ++ tailWord_3943191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943191).length < 2 ^ (prefixWord ++ tailWord_3943191).sum := by decide
  have hdescent : baseEnd_3943191 < baseStart_3943191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943197 : List Nat := [1, 4, 2, 4, 1, 11]
def baseStart_3943197 : Nat := 118140960795 + 3943197 * 2 ^ 59
def prefixEnd_3943197 : Nat := 4983230072969 + 3 ^ 40 * 3943197 * 2
def baseEnd_3943197 : Nat := 8332326651716518342811

theorem tailTrace_3943197 : CollatzResearch.WordTrace tailWord_3943197 prefixEnd_3943197 8332326651716518342811 := by
  unfold tailWord_3943197
  simp only [CollatzResearch.WordTrace]
  refine ⟨143820209895478188277059845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95880139930318792184706563 143820209895478188277059845)
  ·
    refine ⟨26966289355402160301948721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143820209895478188277059845 26966289355402160301948721)
    ·
      refine ⟨20224717016551620226461541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26966289355402160301948721 20224717016551620226461541)
      ·
        refine ⟨3792134440603428792461539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20224717016551620226461541 3792134440603428792461539)
        ·
          refine ⟨5688201660905143188692309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792134440603428792461539 5688201660905143188692309)
          ·
            refine ⟨8332326651716518342811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5688201660905143188692309 8332326651716518342811)
            ·
              rfl

theorem cell23_3943197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 11].length) (baseStart_3943197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943197 prefixEnd_3943197 := by exact prefixLift 3943197
  have htrace : WordTrace (prefixWord ++ tailWord_3943197) baseStart_3943197 baseEnd_3943197 := by
    simpa [prefixWord, tailWord_3943197, baseEnd_3943197] using wordTrace_append hprefix tailTrace_3943197
  have hstable : (prefixWord ++ tailWord_3943197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943197).length < 2 ^ (prefixWord ++ tailWord_3943197).sum := by decide
  have hdescent : baseEnd_3943197 < baseStart_3943197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943208 : List Nat := [2, 1, 5, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_3943208 : Nat := 118140960795 + 3943208 * 2 ^ 59
def prefixEnd_3943208 : Nat := 4983230072969 + 3 ^ 40 * 3943208 * 2
def baseEnd_3943208 : Nat := 2024761024654313414265523

theorem tailTrace_3943208 : CollatzResearch.WordTrace tailWord_3943208 prefixEnd_3943208 2024761024654313414265523 := by
  unfold tailWord_3943208
  simp only [CollatzResearch.WordTrace]
  refine ⟨71910305549219168577855139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95880407398958891437140185 71910305549219168577855139)
  ·
    refine ⟨107865458323828752866782709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71910305549219168577855139 107865458323828752866782709)
    ·
      refine ⟨10112386717858945581260879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107865458323828752866782709 10112386717858945581260879)
      ·
        refine ⟨15168580076788418371891319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10112386717858945581260879 15168580076788418371891319)
        ·
          refine ⟨22752870115182627557836979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15168580076788418371891319 22752870115182627557836979)
          ·
            refine ⟨34129305172773941336755469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22752870115182627557836979 34129305172773941336755469)
            ·
              refine ⟨12798489439790228001283301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34129305172773941336755469 12798489439790228001283301)
              ·
                refine ⟨2399716769960667750240619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12798489439790228001283301 2399716769960667750240619)
                ·
                  refine ⟨3599575154941001625360929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399716769960667750240619 3599575154941001625360929)
                  ·
                    refine ⟨2699681366205751219020697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599575154941001625360929 2699681366205751219020697)
                    ·
                      refine ⟨2024761024654313414265523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699681366205751219020697 2024761024654313414265523)
                      ·
                        rfl

theorem cell23_3943208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_3943208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943208 prefixEnd_3943208 := by exact prefixLift 3943208
  have htrace : WordTrace (prefixWord ++ tailWord_3943208) baseStart_3943208 baseEnd_3943208 := by
    simpa [prefixWord, tailWord_3943208, baseEnd_3943208] using wordTrace_append hprefix tailTrace_3943208
  have hstable : (prefixWord ++ tailWord_3943208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943208).length < 2 ^ (prefixWord ++ tailWord_3943208).sum := by decide
  have hdescent : baseEnd_3943208 < baseStart_3943208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943214 : List Nat := [4, 1, 3, 2, 1, 3, 1, 8]
def baseStart_3943214 : Nat := 118140960795 + 3943214 * 2 ^ 59
def prefixEnd_3943214 : Nat := 4983230072969 + 3 ^ 40 * 3943214 * 2
def baseEnd_3943214 : Nat := 74991263168082977436685

theorem tailTrace_3943214 : CollatzResearch.WordTrace tailWord_3943214 prefixEnd_3943214 74991263168082977436685 := by
  unfold tailWord_3943214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17977603742052075022553587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95880553290944400120285797 17977603742052075022553587)
  ·
    refine ⟨26966405613078112533830381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17977603742052075022553587 26966405613078112533830381)
    ·
      refine ⟨10112402104904292200186393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26966405613078112533830381 10112402104904292200186393)
      ·
        refine ⟨7584301578678219150139795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10112402104904292200186393 7584301578678219150139795)
        ·
          refine ⟨11376452368017328725209693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584301578678219150139795 11376452368017328725209693)
          ·
            refine ⟨4266169638006498271953635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11376452368017328725209693 4266169638006498271953635)
            ·
              refine ⟨6399254457009747407930453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266169638006498271953635 6399254457009747407930453)
              ·
                refine ⟨74991263168082977436685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6399254457009747407930453 74991263168082977436685)
                ·
                  rfl

theorem cell23_3943214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_3943214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943214 prefixEnd_3943214 := by exact prefixLift 3943214
  have htrace : WordTrace (prefixWord ++ tailWord_3943214) baseStart_3943214 baseEnd_3943214 := by
    simpa [prefixWord, tailWord_3943214, baseEnd_3943214] using wordTrace_append hprefix tailTrace_3943214
  have hstable : (prefixWord ++ tailWord_3943214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943214).length < 2 ^ (prefixWord ++ tailWord_3943214).sum := by decide
  have hdescent : baseEnd_3943214 < baseStart_3943214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943224 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_3943224 : Nat := 118140960795 + 3943224 * 2 ^ 59
def prefixEnd_3943224 : Nat := 4983230072969 + 3 ^ 40 * 3943224 * 2
def baseEnd_3943224 : Nat := 2024769240344785351665449

theorem tailTrace_3943224 : CollatzResearch.WordTrace tailWord_3943224 prefixEnd_3943224 2024769240344785351665449 := by
  unfold tailWord_3943224
  simp only [CollatzResearch.WordTrace]
  refine ⟨71910597333190185944146363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95880796444253581258861817 71910597333190185944146363)
  ·
    refine ⟨107865895999785278916219545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71910597333190185944146363 107865895999785278916219545)
    ·
      refine ⟨80899421999838959187164659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107865895999785278916219545 80899421999838959187164659)
      ·
        refine ⟨121349132999758438780746989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80899421999838959187164659 121349132999758438780746989)
        ·
          refine ⟨45505924874909414542780121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121349132999758438780746989 45505924874909414542780121)
          ·
            refine ⟨34129443656182060907085091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45505924874909414542780121 34129443656182060907085091)
            ·
              refine ⟨51194165484273091360627637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34129443656182060907085091 51194165484273091360627637)
              ·
                refine ⟨4799453014150602315058841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51194165484273091360627637 4799453014150602315058841)
                ·
                  refine ⟨3599589760612951736294131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4799453014150602315058841 3599589760612951736294131)
                  ·
                    refine ⟨5399384640919427604441197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3599589760612951736294131 5399384640919427604441197)
                    ·
                      refine ⟨2024769240344785351665449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5399384640919427604441197 2024769240344785351665449)
                      ·
                        rfl

theorem cell23_3943224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_3943224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943224 prefixEnd_3943224 := by exact prefixLift 3943224
  have htrace : WordTrace (prefixWord ++ tailWord_3943224) baseStart_3943224 baseEnd_3943224 := by
    simpa [prefixWord, tailWord_3943224, baseEnd_3943224] using wordTrace_append hprefix tailTrace_3943224
  have hstable : (prefixWord ++ tailWord_3943224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943224).length < 2 ^ (prefixWord ++ tailWord_3943224).sum := by decide
  have hdescent : baseEnd_3943224 < baseStart_3943224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943240 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 1, 8]
def baseStart_3943240 : Nat := 118140960795 + 3943240 * 2 ^ 59
def prefixEnd_3943240 : Nat := 4983230072969 + 3 ^ 40 * 3943240 * 2
def baseEnd_3943240 : Nat := 674925818678419096355125

theorem tailTrace_3943240 : CollatzResearch.WordTrace tailWord_3943240 prefixEnd_3943240 674925818678419096355125 := by
  unfold tailWord_3943240
  simp only [CollatzResearch.WordTrace]
  refine ⟨71910889117161203310437587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95881185489548271080583449 71910889117161203310437587)
  ·
    refine ⟨107866333675741804965656381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71910889117161203310437587 107866333675741804965656381)
    ·
      refine ⟨40449875128403176862121143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107866333675741804965656381 40449875128403176862121143)
      ·
        refine ⟨60674812692604765293181715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40449875128403176862121143 60674812692604765293181715)
        ·
          refine ⟨91012219038907147939772573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60674812692604765293181715 91012219038907147939772573)
          ·
            refine ⟨34129582139590180477414715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91012219038907147939772573 34129582139590180477414715)
            ·
              refine ⟨51194373209385270716122073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34129582139590180477414715 51194373209385270716122073)
              ·
                refine ⟨38395779907038953037091555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51194373209385270716122073 38395779907038953037091555)
                ·
                  refine ⟨57593669860558429555637333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38395779907038953037091555 57593669860558429555637333)
                  ·
                    refine ⟨674925818678419096355125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57593669860558429555637333 674925818678419096355125)
                    ·
                      rfl

theorem cell23_3943240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_3943240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943240 prefixEnd_3943240 := by exact prefixLift 3943240
  have htrace : WordTrace (prefixWord ++ tailWord_3943240) baseStart_3943240 baseEnd_3943240 := by
    simpa [prefixWord, tailWord_3943240, baseEnd_3943240] using wordTrace_append hprefix tailTrace_3943240
  have hstable : (prefixWord ++ tailWord_3943240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943240).length < 2 ^ (prefixWord ++ tailWord_3943240).sum := by decide
  have hdescent : baseEnd_3943240 < baseStart_3943240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943245 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3943245 : Nat := 118140960795 + 3943245 * 2 ^ 59
def prefixEnd_3943245 : Nat := 4983230072969 + 3 ^ 40 * 3943245 * 2
def baseEnd_3943245 : Nat := 2024780023438529769502853

theorem tailTrace_3943245 : CollatzResearch.WordTrace tailWord_3943245 prefixEnd_3943245 2024780023438529769502853 := by
  unfold tailWord_3943245
  simp only [CollatzResearch.WordTrace]
  refine ⟨143821960599304292474807189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95881307066202861649871459 143821960599304292474807189)
  ·
    refine ⟨6741654403092388709756587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143821960599304292474807189 6741654403092388709756587)
    ·
      refine ⟨10112481604638583064634881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6741654403092388709756587 10112481604638583064634881)
      ·
        refine ⟨7584361203478937298476161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10112481604638583064634881 7584361203478937298476161)
        ·
          refine ⟨5688270902609202973857121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7584361203478937298476161 5688270902609202973857121)
          ·
            refine ⟨4266203176956902230392841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5688270902609202973857121 4266203176956902230392841)
            ·
              refine ⟨3199652382717676672794631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4266203176956902230392841 3199652382717676672794631)
              ·
                refine ⟨4799478574076515009191947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199652382717676672794631 4799478574076515009191947)
                ·
                  refine ⟨7199217861114772513787921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799478574076515009191947 7199217861114772513787921)
                  ·
                    refine ⟨5399413395836079385340941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7199217861114772513787921 5399413395836079385340941)
                    ·
                      refine ⟨2024780023438529769502853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5399413395836079385340941 2024780023438529769502853)
                      ·
                        rfl

theorem cell23_3943245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3943245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943245 prefixEnd_3943245 := by exact prefixLift 3943245
  have htrace : WordTrace (prefixWord ++ tailWord_3943245) baseStart_3943245 baseEnd_3943245 := by
    simpa [prefixWord, tailWord_3943245, baseEnd_3943245] using wordTrace_append hprefix tailTrace_3943245
  have hstable : (prefixWord ++ tailWord_3943245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943245).length < 2 ^ (prefixWord ++ tailWord_3943245).sum := by decide
  have hdescent : baseEnd_3943245 < baseStart_3943245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943281 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 1, 4, 2]
def baseStart_3943281 : Nat := 118140960795 + 3943281 * 2 ^ 59
def prefixEnd_3943281 : Nat := 4983230072969 + 3 ^ 40 * 3943281 * 2
def baseEnd_3943281 : Nat := 2024798508742091628652687

theorem tailTrace_3943281 : CollatzResearch.WordTrace tailWord_3943281 prefixEnd_3943281 2024798508742091628652687 := by
  unfold tailWord_3943281
  simp only [CollatzResearch.WordTrace]
  refine ⟨143823273627173870623117697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95882182418115913748745131 143823273627173870623117697)
  ·
    refine ⟨107867455220380402967338273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143823273627173870623117697 107867455220380402967338273)
    ·
      refine ⟨80900591415285302225503705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107867455220380402967338273 80900591415285302225503705)
      ·
        refine ⟨60675443561463976669127779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80900591415285302225503705 60675443561463976669127779)
        ·
          refine ⟨91013165342195965003691669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60675443561463976669127779 91013165342195965003691669)
          ·
            refine ⟨4266242125415435859548047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91013165342195965003691669 4266242125415435859548047)
            ·
              refine ⟨6399363188123153789322071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266242125415435859548047 6399363188123153789322071)
              ·
                refine ⟨9599044782184730683983107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399363188123153789322071 9599044782184730683983107)
                ·
                  refine ⟨14398567173277096025974661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599044782184730683983107 14398567173277096025974661)
                  ·
                    refine ⟨2699731344989455504870249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14398567173277096025974661 2699731344989455504870249)
                    ·
                      refine ⟨2024798508742091628652687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699731344989455504870249 2024798508742091628652687)
                      ·
                        rfl

theorem cell23_3943281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_3943281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943281 prefixEnd_3943281 := by exact prefixLift 3943281
  have htrace : WordTrace (prefixWord ++ tailWord_3943281) baseStart_3943281 baseEnd_3943281 := by
    simpa [prefixWord, tailWord_3943281, baseEnd_3943281] using wordTrace_append hprefix tailTrace_3943281
  have hstable : (prefixWord ++ tailWord_3943281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943281).length < 2 ^ (prefixWord ++ tailWord_3943281).sum := by decide
  have hdescent : baseEnd_3943281 < baseStart_3943281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943317 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3943317 : Nat := 118140960795 + 3943317 * 2 ^ 59
def prefixEnd_3943317 : Nat := 4983230072969 + 3 ^ 40 * 3943317 * 2
def baseEnd_3943317 : Nat := 674938998015217829267507

theorem tailTrace_3943317 : CollatzResearch.WordTrace tailWord_3943317 prefixEnd_3943317 674938998015217829267507 := by
  unfold tailWord_3943317
  simp only [CollatzResearch.WordTrace]
  refine ⟨143824586655043448771428205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95883057770028965847618803 143824586655043448771428205)
  ·
    refine ⟨53934219995641293289285577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143824586655043448771428205 53934219995641293289285577)
    ·
      refine ⟨40450664996730969966964183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53934219995641293289285577 40450664996730969966964183)
      ·
        refine ⟨60675997495096454950446275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40450664996730969966964183 60675997495096454950446275)
        ·
          refine ⟨91013996242644682425669413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60675997495096454950446275 91013996242644682425669413)
          ·
            refine ⟨17065124295495877954813015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91013996242644682425669413 17065124295495877954813015)
            ·
              refine ⟨25597686443243816932219523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17065124295495877954813015 25597686443243816932219523)
              ·
                refine ⟨38396529664865725398329285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25597686443243816932219523 38396529664865725398329285)
                ·
                  refine ⟨7199349312162323512186741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38396529664865725398329285 7199349312162323512186741)
                  ·
                    refine ⟨674938998015217829267507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7199349312162323512186741 674938998015217829267507)
                    ·
                      rfl

theorem cell23_3943317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3943317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943317 prefixEnd_3943317 := by exact prefixLift 3943317
  have htrace : WordTrace (prefixWord ++ tailWord_3943317) baseStart_3943317 baseEnd_3943317 := by
    simpa [prefixWord, tailWord_3943317, baseEnd_3943317] using wordTrace_append hprefix tailTrace_3943317
  have hstable : (prefixWord ++ tailWord_3943317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943317).length < 2 ^ (prefixWord ++ tailWord_3943317).sum := by decide
  have hdescent : baseEnd_3943317 < baseStart_3943317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943327 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3943327 : Nat := 118140960795 + 3943327 * 2 ^ 59
def prefixEnd_3943327 : Nat := 4983230072969 + 3 ^ 40 * 3943327 * 2
def baseEnd_3943327 : Nat := 2024822128852198448677475

theorem tailTrace_3943327 : CollatzResearch.WordTrace tailWord_3943327 prefixEnd_3943327 2024822128852198448677475 := by
  unfold tailWord_3943327
  simp only [CollatzResearch.WordTrace]
  refine ⟨143824951385007220479292235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95883300923338146986194823 143824951385007220479292235)
  ·
    refine ⟨215737427077510830718938353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143824951385007220479292235 215737427077510830718938353)
    ·
      refine ⟨161803070308133123039203765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215737427077510830718938353 161803070308133123039203765)
      ·
        refine ⟨15169037841387480284925353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161803070308133123039203765 15169037841387480284925353)
        ·
          refine ⟨11376778381040610213694015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15169037841387480284925353 11376778381040610213694015)
          ·
            refine ⟨17065167571560915320541023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11376778381040610213694015 17065167571560915320541023)
            ·
              refine ⟨25597751357341372980811535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17065167571560915320541023 25597751357341372980811535)
              ·
                refine ⟨38396627036012059471217303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25597751357341372980811535 38396627036012059471217303)
                ·
                  refine ⟨57594940554018089206825955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38396627036012059471217303 57594940554018089206825955)
                  ·
                    refine ⟨86392410831027133810238933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57594940554018089206825955 86392410831027133810238933)
                    ·
                      refine ⟨2024822128852198448677475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86392410831027133810238933 2024822128852198448677475)
                      ·
                        rfl

theorem cell23_3943327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3943327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943327 prefixEnd_3943327 := by exact prefixLift 3943327
  have htrace : WordTrace (prefixWord ++ tailWord_3943327) baseStart_3943327 baseEnd_3943327 := by
    simpa [prefixWord, tailWord_3943327, baseEnd_3943327] using wordTrace_append hprefix tailTrace_3943327
  have hstable : (prefixWord ++ tailWord_3943327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943327).length < 2 ^ (prefixWord ++ tailWord_3943327).sum := by decide
  have hdescent : baseEnd_3943327 < baseStart_3943327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943337 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_3943337 : Nat := 118140960795 + 3943337 * 2 ^ 59
def prefixEnd_3943337 : Nat := 4983230072969 + 3 ^ 40 * 3943337 * 2
def baseEnd_3943337 : Nat := 2024827263658743409552429

theorem tailTrace_3943337 : CollatzResearch.WordTrace tailWord_3943337 prefixEnd_3943337 2024827263658743409552429 := by
  unfold tailWord_3943337
  simp only [CollatzResearch.WordTrace]
  refine ⟨143825316114970992187156265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95883544076647328124770843 143825316114970992187156265)
  ·
    refine ⟨107868987086228244140367199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143825316114970992187156265 107868987086228244140367199)
    ·
      refine ⟨161803480629342366210550799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107868987086228244140367199 161803480629342366210550799)
      ·
        refine ⟨242705220944013549315826199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161803480629342366210550799 242705220944013549315826199)
        ·
          refine ⟨364057831416020323973739299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242705220944013549315826199 364057831416020323973739299)
          ·
            refine ⟨546086747124030485960608949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364057831416020323973739299 546086747124030485960608949)
            ·
              refine ⟨51195632542877858058807089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546086747124030485960608949 51195632542877858058807089)
              ·
                refine ⟨38396724407158393544105317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51195632542877858058807089 38396724407158393544105317)
                ·
                  refine ⟨7199385826342198789519747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38396724407158393544105317 7199385826342198789519747)
                  ·
                    refine ⟨10799078739513298184279621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199385826342198789519747 10799078739513298184279621)
                    ·
                      refine ⟨2024827263658743409552429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10799078739513298184279621 2024827263658743409552429)
                      ·
                        rfl

theorem cell23_3943337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_3943337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943337 prefixEnd_3943337 := by exact prefixLift 3943337
  have htrace : WordTrace (prefixWord ++ tailWord_3943337) baseStart_3943337 baseEnd_3943337 := by
    simpa [prefixWord, tailWord_3943337, baseEnd_3943337] using wordTrace_append hprefix tailTrace_3943337
  have hstable : (prefixWord ++ tailWord_3943337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943337).length < 2 ^ (prefixWord ++ tailWord_3943337).sum := by decide
  have hdescent : baseEnd_3943337 < baseStart_3943337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943354 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_3943354 : Nat := 118140960795 + 3943354 * 2 ^ 59
def prefixEnd_3943354 : Nat := 4983230072969 + 3 ^ 40 * 3943354 * 2
def baseEnd_3943354 : Nat := 2024835992829869843039851

theorem tailTrace_3943354 : CollatzResearch.WordTrace tailWord_3943354 prefixEnd_3943354 2024835992829869843039851 := by
  unfold tailWord_3943354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35956484038977351022631279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95883957437272936060350077 35956484038977351022631279)
  ·
    refine ⟨53934726058466026533946919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35956484038977351022631279 53934726058466026533946919)
    ·
      refine ⟨80902089087699039800920379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53934726058466026533946919 80902089087699039800920379)
      ·
        refine ⟨121353133631548559701380569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80902089087699039800920379 121353133631548559701380569)
        ·
          refine ⟨91014850223661419776035427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121353133631548559701380569 91014850223661419776035427)
          ·
            refine ⟨136522275335492129664053141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91014850223661419776035427 136522275335492129664053141)
            ·
              refine ⟨6399481656351193578002491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136522275335492129664053141 6399481656351193578002491)
              ·
                refine ⟨9599222484526790367003737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399481656351193578002491 9599222484526790367003737)
                ·
                  refine ⟨7199416863395092775252803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599222484526790367003737 7199416863395092775252803)
                  ·
                    refine ⟨10799125295092639162879205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199416863395092775252803 10799125295092639162879205)
                    ·
                      refine ⟨2024835992829869843039851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10799125295092639162879205 2024835992829869843039851)
                      ·
                        rfl

theorem cell23_3943354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_3943354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943354 prefixEnd_3943354 := by exact prefixLift 3943354
  have htrace : WordTrace (prefixWord ++ tailWord_3943354) baseStart_3943354 baseEnd_3943354 := by
    simpa [prefixWord, tailWord_3943354, baseEnd_3943354] using wordTrace_append hprefix tailTrace_3943354
  have hstable : (prefixWord ++ tailWord_3943354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943354).length < 2 ^ (prefixWord ++ tailWord_3943354).sum := by decide
  have hdescent : baseEnd_3943354 < baseStart_3943354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943366 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3943366 : Nat := 118140960795 + 3943366 * 2 ^ 59
def prefixEnd_3943366 : Nat := 4983230072969 + 3 ^ 40 * 3943366 * 2
def baseEnd_3943366 : Nat := 2024842154597723796089797

theorem tailTrace_3943366 : CollatzResearch.WordTrace tailWord_3943366 prefixEnd_3943366 2024842154597723796089797 := by
  unfold tailWord_3943366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494574182245810316873811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95884249221243953426641301 4494574182245810316873811)
  ·
    refine ⟨6741861273368715475310717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4494574182245810316873811 6741861273368715475310717)
    ·
      refine ⟨2528197977513268303241519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6741861273368715475310717 2528197977513268303241519)
      ·
        refine ⟨3792296966269902454862279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528197977513268303241519 3792296966269902454862279)
        ·
          refine ⟨5688445449404853682293419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792296966269902454862279 5688445449404853682293419)
          ·
            refine ⟨8532668174107280523440129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688445449404853682293419 8532668174107280523440129)
            ·
              refine ⟨6399501130580460392580097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8532668174107280523440129 6399501130580460392580097)
              ·
                refine ⟨4799625847935345294435073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399501130580460392580097 4799625847935345294435073)
                ·
                  refine ⟨3599719385951508970826305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4799625847935345294435073 3599719385951508970826305)
                  ·
                    refine ⟨2699789539463631728119729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599719385951508970826305 2699789539463631728119729)
                    ·
                      refine ⟨2024842154597723796089797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699789539463631728119729 2024842154597723796089797)
                      ·
                        rfl

theorem cell23_3943366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3943366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943366 prefixEnd_3943366 := by exact prefixLift 3943366
  have htrace : WordTrace (prefixWord ++ tailWord_3943366) baseStart_3943366 baseEnd_3943366 := by
    simpa [prefixWord, tailWord_3943366, baseEnd_3943366] using wordTrace_append hprefix tailTrace_3943366
  have hstable : (prefixWord ++ tailWord_3943366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943366).length < 2 ^ (prefixWord ++ tailWord_3943366).sum := by decide
  have hdescent : baseEnd_3943366 < baseStart_3943366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943431 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_3943431 : Nat := 118140960795 + 3943431 * 2 ^ 59
def prefixEnd_3943431 : Nat := 4983230072969 + 3 ^ 40 * 3943431 * 2
def baseEnd_3943431 : Nat := 2024875530840266041776997

theorem tailTrace_3943431 : CollatzResearch.WordTrace tailWord_3943431 prefixEnd_3943431 2024875530840266041776997 := by
  unfold tailWord_3943431
  simp only [CollatzResearch.WordTrace]
  refine ⟨143828744576630446241078147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95885829717753630827385431 143828744576630446241078147)
  ·
    refine ⟨215743116864945669361617221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143828744576630446241078147 215743116864945669361617221)
    ·
      refine ⟨40451834412177313005303229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215743116864945669361617221 40451834412177313005303229)
      ·
        refine ⟨15169437904566492376988711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40451834412177313005303229 15169437904566492376988711)
        ·
          refine ⟨22754156856849738565483067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15169437904566492376988711 22754156856849738565483067)
          ·
            refine ⟨34131235285274607848224601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22754156856849738565483067 34131235285274607848224601)
            ·
              refine ⟨25598426463955955886168451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34131235285274607848224601 25598426463955955886168451)
              ·
                refine ⟨38397639695933933829252677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25598426463955955886168451 38397639695933933829252677)
                ·
                  refine ⟨7199557442987612592984877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38397639695933933829252677 7199557442987612592984877)
                  ·
                    refine ⟨2699834041120354722369329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7199557442987612592984877 2699834041120354722369329)
                    ·
                      refine ⟨2024875530840266041776997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699834041120354722369329 2024875530840266041776997)
                      ·
                        rfl

theorem cell23_3943431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_3943431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943431 prefixEnd_3943431 := by exact prefixLift 3943431
  have htrace : WordTrace (prefixWord ++ tailWord_3943431) baseStart_3943431 baseEnd_3943431 := by
    simpa [prefixWord, tailWord_3943431, baseEnd_3943431] using wordTrace_append hprefix tailTrace_3943431
  have hstable : (prefixWord ++ tailWord_3943431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943431).length < 2 ^ (prefixWord ++ tailWord_3943431).sum := by decide
  have hdescent : baseEnd_3943431 < baseStart_3943431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943438 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3943438 : Nat := 118140960795 + 3943438 * 2 ^ 59
def prefixEnd_3943438 : Nat := 4983230072969 + 3 ^ 40 * 3943438 * 2
def baseEnd_3943438 : Nat := 2024879125204847514389465

theorem tailTrace_3943438 : CollatzResearch.WordTrace tailWord_3943438 prefixEnd_3943438 2024879125204847514389465 := by
  unfold tailWord_3943438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17978624985950635804572871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95885999925070057624388645 17978624985950635804572871)
  ·
    refine ⟨26967937478925953706859307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17978624985950635804572871 26967937478925953706859307)
    ·
      refine ⟨40451906218388930560288961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26967937478925953706859307 40451906218388930560288961)
      ·
        refine ⟨30338929663791697920216721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40451906218388930560288961 30338929663791697920216721)
        ·
          refine ⟨22754197247843773440162541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30338929663791697920216721 22754197247843773440162541)
          ·
            refine ⟨8532823967941415040060953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22754197247843773440162541 8532823967941415040060953)
            ·
              refine ⟨6399617975956061280045715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8532823967941415040060953 6399617975956061280045715)
              ·
                refine ⟨9599426963934091920068573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399617975956061280045715 9599426963934091920068573)
                ·
                  refine ⟨3599785111475284470025715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9599426963934091920068573 3599785111475284470025715)
                  ·
                    refine ⟨5399677667212926705038573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3599785111475284470025715 5399677667212926705038573)
                    ·
                      refine ⟨2024879125204847514389465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5399677667212926705038573 2024879125204847514389465)
                      ·
                        rfl

theorem cell23_3943438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3943438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943438 prefixEnd_3943438 := by exact prefixLift 3943438
  have htrace : WordTrace (prefixWord ++ tailWord_3943438) baseStart_3943438 baseEnd_3943438 := by
    simpa [prefixWord, tailWord_3943438, baseEnd_3943438] using wordTrace_append hprefix tailTrace_3943438
  have hstable : (prefixWord ++ tailWord_3943438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943438).length < 2 ^ (prefixWord ++ tailWord_3943438).sum := by decide
  have hdescent : baseEnd_3943438 < baseStart_3943438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943461 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_3943461 : Nat := 118140960795 + 3943461 * 2 ^ 59
def prefixEnd_3943461 : Nat := 4983230072969 + 3 ^ 40 * 3943461 * 2
def baseEnd_3943461 : Nat := 2024890935259900924401859

theorem tailTrace_3943461 : CollatzResearch.WordTrace tailWord_3943461 prefixEnd_3943461 2024890935259900924401859 := by
  unfold tailWord_3943461
  simp only [CollatzResearch.WordTrace]
  refine ⟨143829838766521761364670237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95886559177681174243113491 143829838766521761364670237)
  ·
    refine ⟨53936189537445660511751339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143829838766521761364670237 53936189537445660511751339)
    ·
      refine ⟨80904284306168490767627009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53936189537445660511751339 80904284306168490767627009)
      ·
        refine ⟨60678213229626368075720257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80904284306168490767627009 60678213229626368075720257)
        ·
          refine ⟨45508659922219776056790193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60678213229626368075720257 45508659922219776056790193)
          ·
            refine ⟨34131494941664832042592645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45508659922219776056790193 34131494941664832042592645)
            ·
              refine ⟨6399655301562156007986121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34131494941664832042592645 6399655301562156007986121)
              ·
                refine ⟨4799741476171617005989591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399655301562156007986121 4799741476171617005989591)
                ·
                  refine ⟨7199612214257425508984387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799741476171617005989591 7199612214257425508984387)
                  ·
                    refine ⟨10799418321386138263476581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199612214257425508984387 10799418321386138263476581)
                    ·
                      refine ⟨2024890935259900924401859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10799418321386138263476581 2024890935259900924401859)
                      ·
                        rfl

theorem cell23_3943461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_3943461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943461 prefixEnd_3943461 := by exact prefixLift 3943461
  have htrace : WordTrace (prefixWord ++ tailWord_3943461) baseStart_3943461 baseEnd_3943461 := by
    simpa [prefixWord, tailWord_3943461, baseEnd_3943461] using wordTrace_append hprefix tailTrace_3943461
  have hstable : (prefixWord ++ tailWord_3943461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943461).length < 2 ^ (prefixWord ++ tailWord_3943461).sum := by decide
  have hdescent : baseEnd_3943461 < baseStart_3943461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943467 : List Nat := [1, 1, 1, 1, 2, 1, 7, 9]
def baseStart_3943467 : Nat := 118140960795 + 3943467 * 2 ^ 59
def prefixEnd_3943467 : Nat := 4983230072969 + 3 ^ 40 * 3943467 * 2
def baseEnd_3943467 : Nat := 74996074671993625960253

theorem tailTrace_3943467 : CollatzResearch.WordTrace tailWord_3943467 prefixEnd_3943467 74996074671993625960253 := by
  unfold tailWord_3943467
  simp only [CollatzResearch.WordTrace]
  refine ⟨143830057604500024389388655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95886705069666682926259103 143830057604500024389388655)
  ·
    refine ⟨215745086406750036584082983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143830057604500024389388655 215745086406750036584082983)
    ·
      refine ⟨323617629610125054876124475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215745086406750036584082983 323617629610125054876124475)
      ·
        refine ⟨485426444415187582314186713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323617629610125054876124475 485426444415187582314186713)
        ·
          refine ⟨364069833311390686735640035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485426444415187582314186713 364069833311390686735640035)
          ·
            refine ⟨546104749967086030103460053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364069833311390686735640035 546104749967086030103460053)
            ·
              refine ⟨12799330077353578830549845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 546104749967086030103460053 12799330077353578830549845)
              ·
                refine ⟨74996074671993625960253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12799330077353578830549845 74996074671993625960253)
                ·
                  rfl

theorem cell23_3943467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 9].length) (baseStart_3943467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943467 prefixEnd_3943467 := by exact prefixLift 3943467
  have htrace : WordTrace (prefixWord ++ tailWord_3943467) baseStart_3943467 baseEnd_3943467 := by
    simpa [prefixWord, tailWord_3943467, baseEnd_3943467] using wordTrace_append hprefix tailTrace_3943467
  have hstable : (prefixWord ++ tailWord_3943467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943467).length < 2 ^ (prefixWord ++ tailWord_3943467).sum := by decide
  have hdescent : baseEnd_3943467 < baseStart_3943467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943474 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_3943474 : Nat := 118140960795 + 3943474 * 2 ^ 59
def prefixEnd_3943474 : Nat := 4983230072969 + 3 ^ 40 * 3943474 * 2
def baseEnd_3943474 : Nat := 2024897610508409373539299

theorem tailTrace_3943474 : CollatzResearch.WordTrace tailWord_3943474 prefixEnd_3943474 2024897610508409373539299 := by
  unfold tailWord_3943474
  simp only [CollatzResearch.WordTrace]
  refine ⟨35957578228868666146223369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95886875276983109723262317 35957578228868666146223369)
  ·
    refine ⟨26968183671651499609667527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35957578228868666146223369 26968183671651499609667527)
    ·
      refine ⟨40452275507477249414501291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26968183671651499609667527 40452275507477249414501291)
      ·
        refine ⟨60678413261215874121751937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40452275507477249414501291 60678413261215874121751937)
        ·
          refine ⟨45508809945911905591313953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60678413261215874121751937 45508809945911905591313953)
          ·
            refine ⟨34131607459433929193485465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45508809945911905591313953 34131607459433929193485465)
            ·
              refine ⟨25598705594575446895114099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34131607459433929193485465 25598705594575446895114099)
              ·
                refine ⟨38398058391863170342671149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25598705594575446895114099 38398058391863170342671149)
                ·
                  refine ⟨14399271896948688878501681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38398058391863170342671149 14399271896948688878501681)
                  ·
                    refine ⟨10799453922711516658876261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14399271896948688878501681 10799453922711516658876261)
                    ·
                      refine ⟨2024897610508409373539299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10799453922711516658876261 2024897610508409373539299)
                      ·
                        rfl

theorem cell23_3943474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_3943474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943474 prefixEnd_3943474 := by exact prefixLift 3943474
  have htrace : WordTrace (prefixWord ++ tailWord_3943474) baseStart_3943474 baseEnd_3943474 := by
    simpa [prefixWord, tailWord_3943474, baseEnd_3943474] using wordTrace_append hprefix tailTrace_3943474
  have hstable : (prefixWord ++ tailWord_3943474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943474).length < 2 ^ (prefixWord ++ tailWord_3943474).sum := by decide
  have hdescent : baseEnd_3943474 < baseStart_3943474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943478 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_3943478 : Nat := 118140960795 + 3943478 * 2 ^ 59
def prefixEnd_3943478 : Nat := 4983230072969 + 3 ^ 40 * 3943478 * 2
def baseEnd_3943478 : Nat := 2024899664431027357889281

theorem tailTrace_3943478 : CollatzResearch.WordTrace tailWord_3943478 prefixEnd_3943478 2024899664431027357889281 := by
  unfold tailWord_3943478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8989403675466260829252443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95886972538306782178692725 8989403675466260829252443)
  ·
    refine ⟨13484105513199391243878665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8989403675466260829252443 13484105513199391243878665)
    ·
      refine ⟨10113079134899543432908999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13484105513199391243878665 10113079134899543432908999)
      ·
        refine ⟨15169618702349315149363499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10113079134899543432908999 15169618702349315149363499)
        ·
          refine ⟨22754428053523972724045249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15169618702349315149363499 22754428053523972724045249)
          ·
            refine ⟨17065821040142979543033937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22754428053523972724045249 17065821040142979543033937)
            ·
              refine ⟨12799365780107234657275453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17065821040142979543033937 12799365780107234657275453)
              ·
                refine ⟨4799762167540212996478295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12799365780107234657275453 4799762167540212996478295)
                ·
                  refine ⟨7199643251310319494717443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799762167540212996478295 7199643251310319494717443)
                  ·
                    refine ⟨10799464876965479242076165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199643251310319494717443 10799464876965479242076165)
                    ·
                      refine ⟨2024899664431027357889281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10799464876965479242076165 2024899664431027357889281)
                      ·
                        rfl

theorem cell23_3943478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_3943478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943478 prefixEnd_3943478 := by exact prefixLift 3943478
  have htrace : WordTrace (prefixWord ++ tailWord_3943478) baseStart_3943478 baseEnd_3943478 := by
    simpa [prefixWord, tailWord_3943478, baseEnd_3943478] using wordTrace_append hprefix tailTrace_3943478
  have hstable : (prefixWord ++ tailWord_3943478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943478).length < 2 ^ (prefixWord ++ tailWord_3943478).sum := by decide
  have hdescent : baseEnd_3943478 < baseStart_3943478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943481 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3943481 : Nat := 118140960795 + 3943481 * 2 ^ 59
def prefixEnd_3943481 : Nat := 4983230072969 + 3 ^ 40 * 3943481 * 2
def baseEnd_3943481 : Nat := 2024901204872990846151767

theorem tailTrace_3943481 : CollatzResearch.WordTrace tailWord_3943481 prefixEnd_3943481 2024901204872990846151767 := by
  unfold tailWord_3943481
  simp only [CollatzResearch.WordTrace]
  refine ⟨143830568226449304780398297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95887045484299536520265531 143830568226449304780398297)
  ·
    refine ⟨107872926169836978585298723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143830568226449304780398297 107872926169836978585298723)
    ·
      refine ⟨161809389254755467877948085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107872926169836978585298723 161809389254755467877948085)
      ·
        refine ⟨15169630242633325113557633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161809389254755467877948085 15169630242633325113557633)
        ·
          refine ⟨11377222681974993835168225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15169630242633325113557633 11377222681974993835168225)
          ·
            refine ⟨8532917011481245376376169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11377222681974993835168225 8532917011481245376376169)
            ·
              refine ⟨6399687758610934032282127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8532917011481245376376169 6399687758610934032282127)
              ·
                refine ⟨9599531637916401048423191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399687758610934032282127 9599531637916401048423191)
                ·
                  refine ⟨14399297456874601572634787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599531637916401048423191 14399297456874601572634787)
                  ·
                    refine ⟨21598946185311902358952181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14399297456874601572634787 21598946185311902358952181)
                    ·
                      refine ⟨2024901204872990846151767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21598946185311902358952181 2024901204872990846151767)
                      ·
                        rfl

theorem cell23_3943481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3943481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943481 prefixEnd_3943481 := by exact prefixLift 3943481
  have htrace : WordTrace (prefixWord ++ tailWord_3943481) baseStart_3943481 baseEnd_3943481 := by
    simpa [prefixWord, tailWord_3943481, baseEnd_3943481] using wordTrace_append hprefix tailTrace_3943481
  have hstable : (prefixWord ++ tailWord_3943481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943481).length < 2 ^ (prefixWord ++ tailWord_3943481).sum := by decide
  have hdescent : baseEnd_3943481 < baseStart_3943481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943484 : List Nat := [2, 2, 2, 2, 2, 4, 9]
def baseStart_3943484 : Nat := 118140960795 + 3943484 * 2 ^ 59
def prefixEnd_3943484 : Nat := 4983230072969 + 3 ^ 40 * 3943484 * 2
def baseEnd_3943484 : Nat := 24998799324875979437213

theorem tailTrace_3943484 : CollatzResearch.WordTrace tailWord_3943484 prefixEnd_3943484 24998799324875979437213 := by
  unfold tailWord_3943484
  simp only [CollatzResearch.WordTrace]
  refine ⟨71915338822719218146378753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95887118430292290861838337 71915338822719218146378753)
  ·
    refine ⟨53936504117039413609784065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71915338822719218146378753 53936504117039413609784065)
    ·
      refine ⟨40452378087779560207338049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53936504117039413609784065 40452378087779560207338049)
      ·
        refine ⟨30339283565834670155503537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40452378087779560207338049 30339283565834670155503537)
        ·
          refine ⟨22754462674376002616627653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30339283565834670155503537 22754462674376002616627653)
          ·
            refine ⟨4266461751445500490617685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22754462674376002616627653 4266461751445500490617685)
            ·
              refine ⟨24998799324875979437213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4266461751445500490617685 24998799324875979437213)
              ·
                rfl

theorem cell23_3943484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 9].length) (baseStart_3943484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943484 prefixEnd_3943484 := by exact prefixLift 3943484
  have htrace : WordTrace (prefixWord ++ tailWord_3943484) baseStart_3943484 baseEnd_3943484 := by
    simpa [prefixWord, tailWord_3943484, baseEnd_3943484] using wordTrace_append hprefix tailTrace_3943484
  have hstable : (prefixWord ++ tailWord_3943484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943484).length < 2 ^ (prefixWord ++ tailWord_3943484).sum := by decide
  have hdescent : baseEnd_3943484 < baseStart_3943484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943495 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_3943495 : Nat := 118140960795 + 3943495 * 2 ^ 59
def prefixEnd_3943495 : Nat := 4983230072969 + 3 ^ 40 * 3943495 * 2
def baseEnd_3943495 : Nat := 2024908393602153791376703

theorem tailTrace_3943495 : CollatzResearch.WordTrace tailWord_3943495 prefixEnd_3943495 2024908393602153791376703 := by
  unfold tailWord_3943495
  simp only [CollatzResearch.WordTrace]
  refine ⟨143831078848398585171407939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95887385898932390114271959 143831078848398585171407939)
  ·
    refine ⟨215746618272597877757111909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143831078848398585171407939 215746618272597877757111909)
    ·
      refine ⟨40452490926112102079458483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215746618272597877757111909 40452490926112102079458483)
      ·
        refine ⟨60678736389168153119187725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40452490926112102079458483 60678736389168153119187725)
        ·
          refine ⟨22754526145938057419695397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60678736389168153119187725 22754526145938057419695397)
          ·
            refine ⟨4266473652363385766192887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22754526145938057419695397 4266473652363385766192887)
            ·
              refine ⟨6399710478545078649289331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266473652363385766192887 6399710478545078649289331)
              ·
                refine ⟨9599565717817617973933997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399710478545078649289331 9599565717817617973933997)
                ·
                  refine ⟨3599837144181606740225249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9599565717817617973933997 3599837144181606740225249)
                  ·
                    refine ⟨2699877858136205055168937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599837144181606740225249 2699877858136205055168937)
                    ·
                      refine ⟨2024908393602153791376703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2699877858136205055168937 2024908393602153791376703)
                      ·
                        rfl

theorem cell23_3943495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_3943495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943495 prefixEnd_3943495 := by exact prefixLift 3943495
  have htrace : WordTrace (prefixWord ++ tailWord_3943495) baseStart_3943495 baseEnd_3943495 := by
    simpa [prefixWord, tailWord_3943495, baseEnd_3943495] using wordTrace_append hprefix tailTrace_3943495
  have hstable : (prefixWord ++ tailWord_3943495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943495).length < 2 ^ (prefixWord ++ tailWord_3943495).sum := by decide
  have hdescent : baseEnd_3943495 < baseStart_3943495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943501 : List Nat := [1, 6, 1, 1, 1, 3, 2, 8]
def baseStart_3943501 : Nat := 118140960795 + 3943501 * 2 ^ 59
def prefixEnd_3943501 : Nat := 4983230072969 + 3 ^ 40 * 3943501 * 2
def baseEnd_3943501 : Nat := 74996721277262250663025

theorem tailTrace_3943501 : CollatzResearch.WordTrace tailWord_3943501 prefixEnd_3943501 74996721277262250663025 := by
  unfold tailWord_3943501
  simp only [CollatzResearch.WordTrace]
  refine ⟨143831297686376848196126357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95887531790917898797417571 143831297686376848196126357)
  ·
    refine ⟨6742092079048914759193423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143831297686376848196126357 6742092079048914759193423)
    ·
      refine ⟨10113138118573372138790135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742092079048914759193423 10113138118573372138790135)
      ·
        refine ⟨15169707177860058208185203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10113138118573372138790135 15169707177860058208185203)
        ·
          refine ⟨22754560766790087312277805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15169707177860058208185203 22754560766790087312277805)
          ·
            refine ⟨8532960287546282742104177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22754560766790087312277805 8532960287546282742104177)
            ·
              refine ⟨6399720215659712056578133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8532960287546282742104177 6399720215659712056578133)
              ·
                refine ⟨74996721277262250663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6399720215659712056578133 74996721277262250663025)
                ·
                  rfl

theorem cell23_3943501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 8].length) (baseStart_3943501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943501 prefixEnd_3943501 := by exact prefixLift 3943501
  have htrace : WordTrace (prefixWord ++ tailWord_3943501) baseStart_3943501 baseEnd_3943501 := by
    simpa [prefixWord, tailWord_3943501, baseEnd_3943501] using wordTrace_append hprefix tailTrace_3943501
  have hstable : (prefixWord ++ tailWord_3943501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943501).length < 2 ^ (prefixWord ++ tailWord_3943501).sum := by decide
  have hdescent : baseEnd_3943501 < baseStart_3943501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3943518 : List Nat := [4, 4, 1, 1, 1, 1, 2, 9]
def baseStart_3943518 : Nat := 118140960795 + 3943518 * 2 ^ 59
def prefixEnd_3943518 : Nat := 4983230072969 + 3 ^ 40 * 3943518 * 2
def baseEnd_3943518 : Nat := 74997044579896563014411

theorem tailTrace_3943518 : CollatzResearch.WordTrace tailWord_3943518 prefixEnd_3943518 74997044579896563014411 := by
  unfold tailWord_3943518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17978989715914407512436901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95887945151543506732996805 17978989715914407512436901)
  ·
    refine ⟨3371060571733951408581919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17978989715914407512436901 3371060571733951408581919)
    ·
      refine ⟨5056590857600927112872879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371060571733951408581919 5056590857600927112872879)
      ·
        refine ⟨7584886286401390669309319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5056590857600927112872879 7584886286401390669309319)
        ·
          refine ⟨11377329429602086003963979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584886286401390669309319 11377329429602086003963979)
          ·
            refine ⟨17065994144403129005945969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11377329429602086003963979 17065994144403129005945969)
            ·
              refine ⟨12799495608302346754459477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17065994144403129005945969 12799495608302346754459477)
              ·
                refine ⟨74997044579896563014411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12799495608302346754459477 74997044579896563014411)
                ·
                  rfl

theorem cell23_3943518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_3943518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3943518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3943518 prefixEnd_3943518 := by exact prefixLift 3943518
  have htrace : WordTrace (prefixWord ++ tailWord_3943518) baseStart_3943518 baseEnd_3943518 := by
    simpa [prefixWord, tailWord_3943518, baseEnd_3943518] using wordTrace_append hprefix tailTrace_3943518
  have hstable : (prefixWord ++ tailWord_3943518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3943518).length < 2 ^ (prefixWord ++ tailWord_3943518).sum := by decide
  have hdescent : baseEnd_3943518 < baseStart_3943518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3943518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
