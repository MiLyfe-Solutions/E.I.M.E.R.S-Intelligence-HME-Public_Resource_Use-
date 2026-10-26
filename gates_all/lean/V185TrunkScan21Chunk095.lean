import V185TrunkScan21Chunk094

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1153919 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 6]
def baseStart_1153919 : Nat := 118140960795 + 1153919 * 2 ^ 59
def prefixEnd_1153919 : Nat := 4983230072969 + 3 ^ 40 * 1153919 * 2
def baseEnd_1153919 : Nat := 263340037046922675691435

theorem tailTrace_1153919 : CollatzResearch.WordTrace tailWord_1153919 prefixEnd_1153919 263340037046922675691435 := by
  unfold tailWord_1153919
  simp only [CollatzResearch.WordTrace]
  refine ⟨42086883506556011520472811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28057922337704007680315207 42086883506556011520472811)
  ·
    refine ⟨63130325259834017280709217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42086883506556011520472811 63130325259834017280709217)
    ·
      refine ⟨47347743944875512960531913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63130325259834017280709217 47347743944875512960531913)
      ·
        refine ⟨35510807958656634720398935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47347743944875512960531913 35510807958656634720398935)
        ·
          refine ⟨53266211937984952080598403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35510807958656634720398935 53266211937984952080598403)
          ·
            refine ⟨79899317906977428120897605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53266211937984952080598403 79899317906977428120897605)
            ·
              refine ⟨14981122107558267772668301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79899317906977428120897605 14981122107558267772668301)
              ·
                refine ⟨5617920790334350414750613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14981122107558267772668301 5617920790334350414750613)
                ·
                  refine ⟨263340037046922675691435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5617920790334350414750613 263340037046922675691435)
                  ·
                    rfl

theorem cell21_1153919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_1153919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153919 prefixEnd_1153919 := by exact prefixLift 1153919
  have htrace : WordTrace (prefixWord ++ tailWord_1153919) baseStart_1153919 baseEnd_1153919 := by
    simpa [prefixWord, tailWord_1153919, baseEnd_1153919] using wordTrace_append hprefix tailTrace_1153919
  have hstable : (prefixWord ++ tailWord_1153919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153919).length < 2 ^ (prefixWord ++ tailWord_1153919).sum := by decide
  have hdescent : baseEnd_1153919 < baseStart_1153919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153942 : List Nat := [5, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1153942 : Nat := 118140960795 + 1153942 * 2 ^ 59
def prefixEnd_1153942 : Nat := 4983230072969 + 3 ^ 40 * 1153942 * 2
def baseEnd_1153942 : Nat := 87781761986759915602685

theorem tailTrace_1153942 : CollatzResearch.WordTrace tailWord_1153942 prefixEnd_1153942 87781761986759915602685 := by
  unfold tailWord_1153942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2630482649092042903035005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28058481590315124299040053 2630482649092042903035005)
  ·
    refine ⟨986430993409516088638127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2630482649092042903035005 986430993409516088638127)
    ·
      refine ⟨1479646490114274132957191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986430993409516088638127 1479646490114274132957191)
      ·
        refine ⟨2219469735171411199435787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479646490114274132957191 2219469735171411199435787)
        ·
          refine ⟨3329204602757116799153681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219469735171411199435787 3329204602757116799153681)
          ·
            refine ⟨2496903452067837599365261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3329204602757116799153681 2496903452067837599365261)
            ·
              refine ⟨936338794525439099761973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2496903452067837599365261 936338794525439099761973)
              ·
                refine ⟨87781761986759915602685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 936338794525439099761973 87781761986759915602685)
                ·
                  rfl

theorem cell21_1153942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1153942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1153942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1153942 prefixEnd_1153942 := by exact prefixLift 1153942
  have htrace : WordTrace (prefixWord ++ tailWord_1153942) baseStart_1153942 baseEnd_1153942 := by
    simpa [prefixWord, tailWord_1153942, baseEnd_1153942] using wordTrace_append hprefix tailTrace_1153942
  have hstable : (prefixWord ++ tailWord_1153942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153942).length < 2 ^ (prefixWord ++ tailWord_1153942).sum := by decide
  have hdescent : baseEnd_1153942 < baseStart_1153942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154026 : List Nat := [3, 1, 3, 1, 2, 2, 9]
def baseStart_1154026 : Nat := 118140960795 + 1154026 * 2 ^ 59
def prefixEnd_1154026 : Nat := 4983230072969 + 3 ^ 40 * 1154026 * 2
def baseEnd_1154026 : Nat := 29262717322746029711987

theorem tailTrace_1154026 : CollatzResearch.WordTrace tailWord_1154026 prefixEnd_1154026 29262717322746029711987 := by
  unfold tailWord_1154026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10522696529292092198654483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28060524078112245863078621 10522696529292092198654483)
  ·
    refine ⟨15784044793938138297981725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10522696529292092198654483 15784044793938138297981725)
    ·
      refine ⟨5919016797726801861743147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15784044793938138297981725 5919016797726801861743147)
      ·
        refine ⟨8878525196590202792614721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5919016797726801861743147 8878525196590202792614721)
        ·
          refine ⟨6658893897442652094461041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8878525196590202792614721 6658893897442652094461041)
          ·
            refine ⟨4994170423081989070845781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6658893897442652094461041 4994170423081989070845781)
            ·
              refine ⟨29262717322746029711987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4994170423081989070845781 29262717322746029711987)
              ·
                rfl

theorem cell21_1154026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 9].length) (baseStart_1154026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154026 prefixEnd_1154026 := by exact prefixLift 1154026
  have htrace : WordTrace (prefixWord ++ tailWord_1154026) baseStart_1154026 baseEnd_1154026 := by
    simpa [prefixWord, tailWord_1154026, baseEnd_1154026] using wordTrace_append hprefix tailTrace_1154026
  have hstable : (prefixWord ++ tailWord_1154026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154026).length < 2 ^ (prefixWord ++ tailWord_1154026).sum := by decide
  have hdescent : baseEnd_1154026 < baseStart_1154026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154046 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1154046 : Nat := 118140960795 + 1154046 * 2 ^ 59
def prefixEnd_1154046 : Nat := 4983230072969 + 3 ^ 40 * 1154046 * 2
def baseEnd_1154046 : Nat := 263369020177198677074509

theorem tailTrace_1154046 : CollatzResearch.WordTrace tailWord_1154046 prefixEnd_1154046 263369020177198677074509 := by
  unfold tailWord_1154046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5261439447136989026293249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28061010384730608140230661 5261439447136989026293249)
  ·
    refine ⟨3946079585352741769719937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5261439447136989026293249 3946079585352741769719937)
    ·
      refine ⟨2959559689014556327289953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3946079585352741769719937 2959559689014556327289953)
      ·
        refine ⟨2219669766760917245467465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2959559689014556327289953 2219669766760917245467465)
        ·
          refine ⟨1664752325070687934100599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2219669766760917245467465 1664752325070687934100599)
          ·
            refine ⟨2497128487606031901150899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664752325070687934100599 2497128487606031901150899)
            ·
              refine ⟨3745692731409047851726349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497128487606031901150899 3745692731409047851726349)
              ·
                refine ⟨1404634774278392944397381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3745692731409047851726349 1404634774278392944397381)
                ·
                  refine ⟨263369020177198677074509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404634774278392944397381 263369020177198677074509)
                  ·
                    rfl

theorem cell21_1154046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1154046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154046 prefixEnd_1154046 := by exact prefixLift 1154046
  have htrace : WordTrace (prefixWord ++ tailWord_1154046) baseStart_1154046 baseEnd_1154046 := by
    simpa [prefixWord, tailWord_1154046, baseEnd_1154046] using wordTrace_append hprefix tailTrace_1154046
  have hstable : (prefixWord ++ tailWord_1154046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154046).length < 2 ^ (prefixWord ++ tailWord_1154046).sum := by decide
  have hdescent : baseEnd_1154046 < baseStart_1154046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154074 : List Nat := [3, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_1154074 : Nat := 118140960795 + 1154074 * 2 ^ 59
def prefixEnd_1154074 : Nat := 4983230072969 + 3 ^ 40 * 1154074 * 2
def baseEnd_1154074 : Nat := 263375410158676850607785

theorem tailTrace_1154074 : CollatzResearch.WordTrace tailWord_1154074 prefixEnd_1154074 263375410158676850607785 := by
  unfold tailWord_1154074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523134205248618248091319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28061691213996315328243517 10523134205248618248091319)
  ·
    refine ⟨15784701307872927372136979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10523134205248618248091319 15784701307872927372136979)
    ·
      refine ⟨23677051961809391058205469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15784701307872927372136979 23677051961809391058205469)
      ·
        refine ⟨8878894485678521646827051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23677051961809391058205469 8878894485678521646827051)
        ·
          refine ⟨13318341728517782470240577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8878894485678521646827051 13318341728517782470240577)
          ·
            refine ⟨9988756296388336852680433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13318341728517782470240577 9988756296388336852680433)
            ·
              refine ⟨7491567222291252639510325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9988756296388336852680433 7491567222291252639510325)
              ·
                refine ⟨702334427089804934954093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7491567222291252639510325 702334427089804934954093)
                ·
                  refine ⟨263375410158676850607785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702334427089804934954093 263375410158676850607785)
                  ·
                    rfl

theorem cell21_1154074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_1154074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154074 prefixEnd_1154074 := by exact prefixLift 1154074
  have htrace : WordTrace (prefixWord ++ tailWord_1154074) baseStart_1154074 baseEnd_1154074 := by
    simpa [prefixWord, tailWord_1154074, baseEnd_1154074] using wordTrace_append hprefix tailTrace_1154074
  have hstable : (prefixWord ++ tailWord_1154074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154074).length < 2 ^ (prefixWord ++ tailWord_1154074).sum := by decide
  have hdescent : baseEnd_1154074 < baseStart_1154074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154119 : List Nat := [1, 1, 4, 1, 3, 3, 3, 5]
def baseStart_1154119 : Nat := 118140960795 + 1154119 * 2 ^ 59
def prefixEnd_1154119 : Nat := 4983230072969 + 3 ^ 40 * 1154119 * 2
def baseEnd_1154119 : Nat := 87795226590588924119231

theorem tailTrace_1154119 : CollatzResearch.WordTrace tailWord_1154119 prefixEnd_1154119 87795226590588924119231 := by
  unfold tailWord_1154119
  simp only [CollatzResearch.WordTrace]
  refine ⟨42094178105831445677753411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28062785403887630451835607 42094178105831445677753411)
  ·
    refine ⟨63141267158747168516630117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42094178105831445677753411 63141267158747168516630117)
    ·
      refine ⟨11838987592265094096868147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63141267158747168516630117 11838987592265094096868147)
      ·
        refine ⟨17758481388397641145302221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11838987592265094096868147 17758481388397641145302221)
        ·
          refine ⟨6659430520649115429488333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17758481388397641145302221 6659430520649115429488333)
          ·
            refine ⟨2497286445243418286058125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6659430520649115429488333 2497286445243418286058125)
            ·
              refine ⟨936482416966281857271797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2497286445243418286058125 936482416966281857271797)
              ·
                refine ⟨87795226590588924119231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 936482416966281857271797 87795226590588924119231)
                ·
                  rfl

theorem cell21_1154119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 5].length) (baseStart_1154119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154119 prefixEnd_1154119 := by exact prefixLift 1154119
  have htrace : WordTrace (prefixWord ++ tailWord_1154119) baseStart_1154119 baseEnd_1154119 := by
    simpa [prefixWord, tailWord_1154119, baseEnd_1154119] using wordTrace_append hprefix tailTrace_1154119
  have hstable : (prefixWord ++ tailWord_1154119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154119).length < 2 ^ (prefixWord ++ tailWord_1154119).sum := by decide
  have hdescent : baseEnd_1154119 < baseStart_1154119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154184 : List Nat := [2, 1, 3, 4, 2, 2, 1, 3, 3]
def baseStart_1154184 : Nat := 118140960795 + 1154184 * 2 ^ 59
def prefixEnd_1154184 : Nat := 4983230072969 + 3 ^ 40 * 1154184 * 2
def baseEnd_1154184 : Nat := 263400513657341103774227

theorem tailTrace_1154184 : CollatzResearch.WordTrace tailWord_1154184 prefixEnd_1154184 263400513657341103774227 := by
  unfold tailWord_1154184
  simp only [CollatzResearch.WordTrace]
  refine ⟨21048274425297980889434803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28064365900397307852579737 21048274425297980889434803)
  ·
    refine ⟨31572411637946971334152205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21048274425297980889434803 31572411637946971334152205)
    ·
      refine ⟨11839654364230114250307077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31572411637946971334152205 11839654364230114250307077)
      ·
        refine ⟨2219935193293146421932577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11839654364230114250307077 2219935193293146421932577)
        ·
          refine ⟨1664951394969859816449433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2219935193293146421932577 1664951394969859816449433)
          ·
            refine ⟨1248713546227394862337075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664951394969859816449433 1248713546227394862337075)
            ·
              refine ⟨1873070319341092293505613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248713546227394862337075 1873070319341092293505613)
              ·
                refine ⟨702401369752909610064605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1873070319341092293505613 702401369752909610064605)
                ·
                  refine ⟨263400513657341103774227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702401369752909610064605 263400513657341103774227)
                  ·
                    rfl

theorem cell21_1154184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_1154184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154184 prefixEnd_1154184 := by exact prefixLift 1154184
  have htrace : WordTrace (prefixWord ++ tailWord_1154184) baseStart_1154184 baseEnd_1154184 := by
    simpa [prefixWord, tailWord_1154184, baseEnd_1154184] using wordTrace_append hprefix tailTrace_1154184
  have hstable : (prefixWord ++ tailWord_1154184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154184).length < 2 ^ (prefixWord ++ tailWord_1154184).sum := by decide
  have hdescent : baseEnd_1154184 < baseStart_1154184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154254 : List Nat := [4, 1, 1, 1, 5, 9]
def baseStart_1154254 : Nat := 118140960795 + 1154254 * 2 ^ 59
def prefixEnd_1154254 : Nat := 4983230072969 + 3 ^ 40 * 1154254 * 2
def baseEnd_1154254 : Nat := 9756166244853205096571

theorem tailTrace_1154254 : CollatzResearch.WordTrace tailWord_1154254 prefixEnd_1154254 9756166244853205096571 := by
  unfold tailWord_1154254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262387745042795466739727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28066067973561575822611877 5262387745042795466739727)
  ·
    refine ⟨7893581617564193200109591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5262387745042795466739727 7893581617564193200109591)
    ·
      refine ⟨11840372426346289800164387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7893581617564193200109591 11840372426346289800164387)
      ·
        refine ⟨17760558639519434700246581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11840372426346289800164387 17760558639519434700246581)
        ·
          refine ⟨1665052372454947003148117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17760558639519434700246581 1665052372454947003148117)
          ·
            refine ⟨9756166244853205096571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1665052372454947003148117 9756166244853205096571)
            ·
              rfl

theorem cell21_1154254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 9].length) (baseStart_1154254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154254 prefixEnd_1154254 := by exact prefixLift 1154254
  have htrace : WordTrace (prefixWord ++ tailWord_1154254) baseStart_1154254 baseEnd_1154254 := by
    simpa [prefixWord, tailWord_1154254, baseEnd_1154254] using wordTrace_append hprefix tailTrace_1154254
  have hstable : (prefixWord ++ tailWord_1154254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154254).length < 2 ^ (prefixWord ++ tailWord_1154254).sum := by decide
  have hdescent : baseEnd_1154254 < baseStart_1154254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154260 : List Nat := [2, 4, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1154260 : Nat := 118140960795 + 1154260 * 2 ^ 59
def prefixEnd_1154260 : Nat := 4983230072969 + 3 ^ 40 * 1154260 * 2
def baseEnd_1154260 : Nat := 263417857892781860507405

theorem tailTrace_1154260 : CollatzResearch.WordTrace tailWord_1154260 prefixEnd_1154260 263417857892781860507405 := by
  unfold tailWord_1154260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21049660399160313379318117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28066213865547084505757489 21049660399160313379318117)
  ·
    refine ⟨3946811324842558758622147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21049660399160313379318117 3946811324842558758622147)
    ·
      refine ⟨5920216987263838137933221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3946811324842558758622147 5920216987263838137933221)
      ·
        refine ⟨1110040685111969650862479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5920216987263838137933221 1110040685111969650862479)
        ·
          refine ⟨1665061027667954476293719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110040685111969650862479 1665061027667954476293719)
          ·
            refine ⟨2497591541501931714440579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665061027667954476293719 2497591541501931714440579)
            ·
              refine ⟨3746387312252897571660869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497591541501931714440579 3746387312252897571660869)
              ·
                refine ⟨702447621047418294686413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3746387312252897571660869 702447621047418294686413)
                ·
                  refine ⟨263417857892781860507405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702447621047418294686413 263417857892781860507405)
                  ·
                    rfl

theorem cell21_1154260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1154260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154260 prefixEnd_1154260 := by exact prefixLift 1154260
  have htrace : WordTrace (prefixWord ++ tailWord_1154260) baseStart_1154260 baseEnd_1154260 := by
    simpa [prefixWord, tailWord_1154260, baseEnd_1154260] using wordTrace_append hprefix tailTrace_1154260
  have hstable : (prefixWord ++ tailWord_1154260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154260).length < 2 ^ (prefixWord ++ tailWord_1154260).sum := by decide
  have hdescent : baseEnd_1154260 < baseStart_1154260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154285 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1154285 : Nat := 118140960795 + 1154285 * 2 ^ 59
def prefixEnd_1154285 : Nat := 4983230072969 + 3 ^ 40 * 1154285 * 2
def baseEnd_1154285 : Nat := 263423563233387372590687

theorem tailTrace_1154285 : CollatzResearch.WordTrace tailWord_1154285 prefixEnd_1154285 263423563233387372590687 := by
  unfold tailWord_1154285
  simp only [CollatzResearch.WordTrace]
  refine ⟨42100232623230056028296309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28066821748820037352197539 42100232623230056028296309)
  ·
    refine ⟨3946896808427817752652779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42100232623230056028296309 3946896808427817752652779)
    ·
      refine ⟨5920345212641726628979169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3946896808427817752652779 5920345212641726628979169)
      ·
        refine ⟨4440258909481294971734377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5920345212641726628979169 4440258909481294971734377)
        ·
          refine ⟨3330194182110971228800783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4440258909481294971734377 3330194182110971228800783)
          ·
            refine ⟨4995291273166456843201175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330194182110971228800783 4995291273166456843201175)
            ·
              refine ⟨7492936909749685264801763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4995291273166456843201175 7492936909749685264801763)
              ·
                refine ⟨11239405364624527897202645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7492936909749685264801763 11239405364624527897202645)
                ·
                  refine ⟨263423563233387372590687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11239405364624527897202645 263423563233387372590687)
                  ·
                    rfl

theorem cell21_1154285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1154285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154285 prefixEnd_1154285 := by exact prefixLift 1154285
  have htrace : WordTrace (prefixWord ++ tailWord_1154285) baseStart_1154285 baseEnd_1154285 := by
    simpa [prefixWord, tailWord_1154285, baseEnd_1154285] using wordTrace_append hprefix tailTrace_1154285
  have hstable : (prefixWord ++ tailWord_1154285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154285).length < 2 ^ (prefixWord ++ tailWord_1154285).sum := by decide
  have hdescent : baseEnd_1154285 < baseStart_1154285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154313 : List Nat := [1, 2, 1, 1, 3, 3, 10]
def baseStart_1154313 : Nat := 118140960795 + 1154313 * 2 ^ 59
def prefixEnd_1154313 : Nat := 4983230072969 + 3 ^ 40 * 1154313 * 2
def baseEnd_1154313 : Nat := 29269994801651727347107

theorem tailTrace_1154313 : CollatzResearch.WordTrace tailWord_1154313 prefixEnd_1154313 29269994801651727347107 := by
  unfold tailWord_1154313
  simp only [CollatzResearch.WordTrace]
  refine ⟨42101253867128616810315593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28067502578085744540210395 42101253867128616810315593)
  ·
    refine ⟨31575940400346462607736695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42101253867128616810315593 31575940400346462607736695)
    ·
      refine ⟨47363910600519693911605043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31575940400346462607736695 47363910600519693911605043)
      ·
        refine ⟨71045865900779540867407565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47363910600519693911605043 71045865900779540867407565)
        ·
          refine ⟨26642199712792327825277837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71045865900779540867407565 26642199712792327825277837)
          ·
            refine ⟨9990824892297122934479189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26642199712792327825277837 9990824892297122934479189)
            ·
              refine ⟨29269994801651727347107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9990824892297122934479189 29269994801651727347107)
              ·
                rfl

theorem cell21_1154313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 10].length) (baseStart_1154313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154313 prefixEnd_1154313 := by exact prefixLift 1154313
  have htrace : WordTrace (prefixWord ++ tailWord_1154313) baseStart_1154313 baseEnd_1154313 := by
    simpa [prefixWord, tailWord_1154313, baseEnd_1154313] using wordTrace_append hprefix tailTrace_1154313
  have hstable : (prefixWord ++ tailWord_1154313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154313).length < 2 ^ (prefixWord ++ tailWord_1154313).sum := by decide
  have hdescent : baseEnd_1154313 < baseStart_1154313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154316 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1154316 : Nat := 118140960795 + 1154316 * 2 ^ 59
def prefixEnd_1154316 : Nat := 4983230072969 + 3 ^ 40 * 1154316 * 2
def baseEnd_1154316 : Nat := 263430637855738207573957

theorem tailTrace_1154316 : CollatzResearch.WordTrace tailWord_1154316 prefixEnd_1154316 263430637855738207573957 := by
  unfold tailWord_1154316
  simp only [CollatzResearch.WordTrace]
  refine ⟨21050681643058874161337401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28067575524078498881783201 21050681643058874161337401)
  ·
    refine ⟨15788011232294155621003051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21050681643058874161337401 15788011232294155621003051)
    ·
      refine ⟨23682016848441233431504577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15788011232294155621003051 23682016848441233431504577)
      ·
        refine ⟨17761512636330925073628433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23682016848441233431504577 17761512636330925073628433)
        ·
          refine ⟨13321134477248193805221325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17761512636330925073628433 13321134477248193805221325)
          ·
            refine ⟨4995425428968072676957997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13321134477248193805221325 4995425428968072676957997)
            ·
              refine ⟨1873284535863027253859249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4995425428968072676957997 1873284535863027253859249)
              ·
                refine ⟨1404963401897270440394437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873284535863027253859249 1404963401897270440394437)
                ·
                  refine ⟨263430637855738207573957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404963401897270440394437 263430637855738207573957)
                  ·
                    rfl

theorem cell21_1154316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1154316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154316 prefixEnd_1154316 := by exact prefixLift 1154316
  have htrace : WordTrace (prefixWord ++ tailWord_1154316) baseStart_1154316 baseEnd_1154316 := by
    simpa [prefixWord, tailWord_1154316, baseEnd_1154316] using wordTrace_append hprefix tailTrace_1154316
  have hstable : (prefixWord ++ tailWord_1154316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154316).length < 2 ^ (prefixWord ++ tailWord_1154316).sum := by decide
  have hdescent : baseEnd_1154316 < baseStart_1154316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154375 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 6]
def baseStart_1154375 : Nat := 118140960795 + 1154375 * 2 ^ 59
def prefixEnd_1154375 : Nat := 4983230072969 + 3 ^ 40 * 1154375 * 2
def baseEnd_1154375 : Nat := 263444102459567216090503

theorem tailTrace_1154375 : CollatzResearch.WordTrace tailWord_1154375 prefixEnd_1154375 263444102459567216090503 := by
  unfold tailWord_1154375
  simp only [CollatzResearch.WordTrace]
  refine ⟨42103515192904001399072579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28069010128602667599381719 42103515192904001399072579)
  ·
    refine ⟨63155272789356002098608869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42103515192904001399072579 63155272789356002098608869)
    ·
      refine ⟨11841613648004250393489163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63155272789356002098608869 11841613648004250393489163)
      ·
        refine ⟨17762420472006375590233745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11841613648004250393489163 17762420472006375590233745)
        ·
          refine ⟨13321815354004781692675309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17762420472006375590233745 13321815354004781692675309)
          ·
            refine ⟨4995680757751793134753241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13321815354004781692675309 4995680757751793134753241)
            ·
              refine ⟨3746760568313844851064931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4995680757751793134753241 3746760568313844851064931)
              ·
                refine ⟨5620140852470767276597397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746760568313844851064931 5620140852470767276597397)
                ·
                  refine ⟨263444102459567216090503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5620140852470767276597397 263444102459567216090503)
                  ·
                    rfl

theorem cell21_1154375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_1154375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154375 prefixEnd_1154375 := by exact prefixLift 1154375
  have htrace : WordTrace (prefixWord ++ tailWord_1154375) baseStart_1154375 baseEnd_1154375 := by
    simpa [prefixWord, tailWord_1154375, baseEnd_1154375] using wordTrace_append hprefix tailTrace_1154375
  have hstable : (prefixWord ++ tailWord_1154375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154375).length < 2 ^ (prefixWord ++ tailWord_1154375).sum := by decide
  have hdescent : baseEnd_1154375 < baseStart_1154375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154485 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 4]
def baseStart_1154485 : Nat := 118140960795 + 1154485 * 2 ^ 59
def prefixEnd_1154485 : Nat := 4983230072969 + 3 ^ 40 * 1154485 * 2
def baseEnd_1154485 : Nat := 263469205958231469256945

theorem tailTrace_1154485 : CollatzResearch.WordTrace tailWord_1154485 prefixEnd_1154485 263469205958231469256945 := by
  unfold tailWord_1154485
  simp only [CollatzResearch.WordTrace]
  refine ⟨42107527222505490185576909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28071684815003660123717939 42107527222505490185576909)
  ·
    refine ⟨15790322708439558819591341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42107527222505490185576909 15790322708439558819591341)
    ·
      refine ⟨5921371015664834557346753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15790322708439558819591341 5921371015664834557346753)
      ·
        refine ⟨4441028261748625918010065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5921371015664834557346753 4441028261748625918010065)
        ·
          refine ⟨3330771196311469438507549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4441028261748625918010065 3330771196311469438507549)
          ·
            refine ⟨1249039198616801039440331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3330771196311469438507549 1249039198616801039440331)
            ·
              refine ⟨1873558797925201559160497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249039198616801039440331 1873558797925201559160497)
              ·
                refine ⟨1405169098443901169370373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873558797925201559160497 1405169098443901169370373)
                ·
                  refine ⟨263469205958231469256945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405169098443901169370373 263469205958231469256945)
                  ·
                    rfl

theorem cell21_1154485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_1154485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154485 prefixEnd_1154485 := by exact prefixLift 1154485
  have htrace : WordTrace (prefixWord ++ tailWord_1154485) baseStart_1154485 baseEnd_1154485 := by
    simpa [prefixWord, tailWord_1154485, baseEnd_1154485] using wordTrace_append hprefix tailTrace_1154485
  have hstable : (prefixWord ++ tailWord_1154485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154485).length < 2 ^ (prefixWord ++ tailWord_1154485).sum := by decide
  have hdescent : baseEnd_1154485 < baseStart_1154485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154496 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_1154496 : Nat := 118140960795 + 1154496 * 2 ^ 59
def prefixEnd_1154496 : Nat := 4983230072969 + 3 ^ 40 * 1154496 * 2
def baseEnd_1154496 : Nat := 263471716308097894573589

theorem tailTrace_1154496 : CollatzResearch.WordTrace tailWord_1154496 prefixEnd_1154496 263471716308097894573589 := by
  unfold tailWord_1154496
  simp only [CollatzResearch.WordTrace]
  refine ⟨21053964212732819532113671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28071952283643759376151561 21053964212732819532113671)
  ·
    refine ⟨31580946319099229298170507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21053964212732819532113671 31580946319099229298170507)
    ·
      refine ⟨47371419478648843947255761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31580946319099229298170507 47371419478648843947255761)
      ·
        refine ⟨35528564608986632960441821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47371419478648843947255761 35528564608986632960441821)
        ·
          refine ⟨13323211728369987360165683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35528564608986632960441821 13323211728369987360165683)
          ·
            refine ⟨19984817592554981040248525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13323211728369987360165683 19984817592554981040248525)
            ·
              refine ⟨7494306597208117890093197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19984817592554981040248525 7494306597208117890093197)
              ·
                refine ⟨2810364973953044208784949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7494306597208117890093197 2810364973953044208784949)
                ·
                  refine ⟨263471716308097894573589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2810364973953044208784949 263471716308097894573589)
                  ·
                    rfl

theorem cell21_1154496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_1154496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154496 prefixEnd_1154496 := by exact prefixLift 1154496
  have htrace : WordTrace (prefixWord ++ tailWord_1154496) baseStart_1154496 baseEnd_1154496 := by
    simpa [prefixWord, tailWord_1154496, baseEnd_1154496] using wordTrace_append hprefix tailTrace_1154496
  have hstable : (prefixWord ++ tailWord_1154496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154496).length < 2 ^ (prefixWord ++ tailWord_1154496).sum := by decide
  have hdescent : baseEnd_1154496 < baseStart_1154496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154516 : List Nat := [2, 4, 1, 2, 3, 2, 2, 5]
def baseStart_1154516 : Nat := 118140960795 + 1154516 * 2 ^ 59
def prefixEnd_1154516 : Nat := 4983230072969 + 3 ^ 40 * 1154516 * 2
def baseEnd_1154516 : Nat := 87825426860194101413405

theorem tailTrace_1154516 : CollatzResearch.WordTrace tailWord_1154516 prefixEnd_1154516 87825426860194101413405 := by
  unfold tailWord_1154516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054328942696591239977701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28072438590262121653303601 21054328942696591239977701)
  ·
    refine ⟨3947686676755610857495819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21054328942696591239977701 3947686676755610857495819)
    ·
      refine ⟨5921530015133416286243729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3947686676755610857495819 5921530015133416286243729)
      ·
        refine ⟨4441147511350062214682797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5921530015133416286243729 4441147511350062214682797)
        ·
          refine ⟨1665430316756273330506049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4441147511350062214682797 1665430316756273330506049)
          ·
            refine ⟨1249072737567204997879537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1665430316756273330506049 1249072737567204997879537)
            ·
              refine ⟨936804553175403748409653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249072737567204997879537 936804553175403748409653)
              ·
                refine ⟨87825426860194101413405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 936804553175403748409653 87825426860194101413405)
                ·
                  rfl

theorem cell21_1154516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_1154516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154516 prefixEnd_1154516 := by exact prefixLift 1154516
  have htrace : WordTrace (prefixWord ++ tailWord_1154516) baseStart_1154516 baseEnd_1154516 := by
    simpa [prefixWord, tailWord_1154516, baseEnd_1154516] using wordTrace_append hprefix tailTrace_1154516
  have hstable : (prefixWord ++ tailWord_1154516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154516).length < 2 ^ (prefixWord ++ tailWord_1154516).sum := by decide
  have hdescent : baseEnd_1154516 < baseStart_1154516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154634 : List Nat := [3, 1, 2, 1, 1, 3, 5, 5]
def baseStart_1154634 : Nat := 118140960795 + 1154634 * 2 ^ 59
def prefixEnd_1154634 : Nat := 4983230072969 + 3 ^ 40 * 1154634 * 2
def baseEnd_1154634 : Nat := 87834403262746773757769

theorem tailTrace_1154634 : CollatzResearch.WordTrace tailWord_1154634 prefixEnd_1154634 87834403262746773757769 := by
  unfold tailWord_1154634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10528240424741422158187739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28075307799310459088500637 10528240424741422158187739)
  ·
    refine ⟨15792360637112133237281609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10528240424741422158187739 15792360637112133237281609)
    ·
      refine ⟨11844270477834099927961207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15792360637112133237281609 11844270477834099927961207)
      ·
        refine ⟨17766405716751149891941811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11844270477834099927961207 17766405716751149891941811)
        ·
          refine ⟨26649608575126724837912717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17766405716751149891941811 26649608575126724837912717)
          ·
            refine ⟨9993603215672521814217269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26649608575126724837912717 9993603215672521814217269)
            ·
              refine ⟨936900301469298920082869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9993603215672521814217269 936900301469298920082869)
              ·
                refine ⟨87834403262746773757769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 936900301469298920082869 87834403262746773757769)
                ·
                  rfl

theorem cell21_1154634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_1154634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154634 prefixEnd_1154634 := by exact prefixLift 1154634
  have htrace : WordTrace (prefixWord ++ tailWord_1154634) baseStart_1154634 baseEnd_1154634 := by
    simpa [prefixWord, tailWord_1154634, baseEnd_1154634] using wordTrace_append hprefix tailTrace_1154634
  have hstable : (prefixWord ++ tailWord_1154634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154634).length < 2 ^ (prefixWord ++ tailWord_1154634).sum := by decide
  have hdescent : baseEnd_1154634 < baseStart_1154634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154665 : List Nat := [1, 2, 1, 1, 1, 4, 4, 4, 3]
def baseStart_1154665 : Nat := 118140960795 + 1154665 * 2 ^ 59
def prefixEnd_1154665 : Nat := 4983230072969 + 3 ^ 40 * 1154665 * 2
def baseEnd_1154665 : Nat := 263510284410591156256577

theorem tailTrace_1154665 : CollatzResearch.WordTrace tailWord_1154665 prefixEnd_1154665 263510284410591156256577 := by
  unfold tailWord_1154665
  simp only [CollatzResearch.WordTrace]
  refine ⟨42114092361853380927129449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28076061574568920618086299 42114092361853380927129449)
  ·
    refine ⟨31585569271390035695347087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42114092361853380927129449 31585569271390035695347087)
    ·
      refine ⟨47378353907085053543020631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31585569271390035695347087 47378353907085053543020631)
      ·
        refine ⟨71067530860627580314530947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47378353907085053543020631 71067530860627580314530947)
        ·
          refine ⟨106601296290941370471796421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71067530860627580314530947 106601296290941370471796421)
          ·
            refine ⟨19987743054551506963461829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106601296290941370471796421 19987743054551506963461829)
            ·
              refine ⟨3747701822728407555649093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19987743054551506963461829 3747701822728407555649093)
              ·
                refine ⟨702694091761576416684205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3747701822728407555649093 702694091761576416684205)
                ·
                  refine ⟨263510284410591156256577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702694091761576416684205 263510284410591156256577)
                  ·
                    rfl

theorem cell21_1154665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_1154665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154665 prefixEnd_1154665 := by exact prefixLift 1154665
  have htrace : WordTrace (prefixWord ++ tailWord_1154665) baseStart_1154665 baseEnd_1154665 := by
    simpa [prefixWord, tailWord_1154665, baseEnd_1154665] using wordTrace_append hprefix tailTrace_1154665
  have hstable : (prefixWord ++ tailWord_1154665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154665).length < 2 ^ (prefixWord ++ tailWord_1154665).sum := by decide
  have hdescent : baseEnd_1154665 < baseStart_1154665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154693 : List Nat := [1, 3, 1, 1, 4, 1, 3, 7]
def baseStart_1154693 : Nat := 118140960795 + 1154693 * 2 ^ 59
def prefixEnd_1154693 : Nat := 4983230072969 + 3 ^ 40 * 1154693 * 2
def baseEnd_1154693 : Nat := 87838891464023109929951

theorem tailTrace_1154693 : CollatzResearch.WordTrace tailWord_1154693 prefixEnd_1154693 87838891464023109929951 := by
  unfold tailWord_1154693
  simp only [CollatzResearch.WordTrace]
  refine ⟨42115113605751941709148733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28076742403834627806099155 42115113605751941709148733)
  ·
    refine ⟨15793167602156978140930775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42115113605751941709148733 15793167602156978140930775)
    ·
      refine ⟨23689751403235467211396163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15793167602156978140930775 23689751403235467211396163)
      ·
        refine ⟨35534627104853200817094245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23689751403235467211396163 35534627104853200817094245)
        ·
          refine ⟨6662742582159975153205171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35534627104853200817094245 6662742582159975153205171)
          ·
            refine ⟨9994113873239962729807757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6662742582159975153205171 9994113873239962729807757)
            ·
              refine ⟨3747792702464986023677909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9994113873239962729807757 3747792702464986023677909)
              ·
                refine ⟨87838891464023109929951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3747792702464986023677909 87838891464023109929951)
                ·
                  rfl

theorem cell21_1154693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 7].length) (baseStart_1154693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154693 prefixEnd_1154693 := by exact prefixLift 1154693
  have htrace : WordTrace (prefixWord ++ tailWord_1154693) baseStart_1154693 baseEnd_1154693 := by
    simpa [prefixWord, tailWord_1154693, baseEnd_1154693] using wordTrace_append hprefix tailTrace_1154693
  have hstable : (prefixWord ++ tailWord_1154693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154693).length < 2 ^ (prefixWord ++ tailWord_1154693).sum := by decide
  have hdescent : baseEnd_1154693 < baseStart_1154693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154772 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1154772 : Nat := 118140960795 + 1154772 * 2 ^ 59
def prefixEnd_1154772 : Nat := 4983230072969 + 3 ^ 40 * 1154772 * 2
def baseEnd_1154772 : Nat := 263534703268382747973025

theorem tailTrace_1154772 : CollatzResearch.WordTrace tailWord_1154772 prefixEnd_1154772 263534703268382747973025 := by
  unfold tailWord_1154772
  simp only [CollatzResearch.WordTrace]
  refine ⟨21058997486232869100637285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28078663314977158800849713 21058997486232869100637285)
  ·
    refine ⟨3948562028668662956369491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21058997486232869100637285 3948562028668662956369491)
    ·
      refine ⟨5922843043002994434554237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948562028668662956369491 5922843043002994434554237)
      ·
        refine ⟨2221066141126122912957839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5922843043002994434554237 2221066141126122912957839)
        ·
          refine ⟨3331599211689184369436759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221066141126122912957839 3331599211689184369436759)
          ·
            refine ⟨4997398817533776554155139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3331599211689184369436759 4997398817533776554155139)
            ·
              refine ⟨7496098226300664831232709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4997398817533776554155139 7496098226300664831232709)
              ·
                refine ⟨1405518417431374655856133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7496098226300664831232709 1405518417431374655856133)
                ·
                  refine ⟨263534703268382747973025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405518417431374655856133 263534703268382747973025)
                  ·
                    rfl

theorem cell21_1154772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1154772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154772 prefixEnd_1154772 := by exact prefixLift 1154772
  have htrace : WordTrace (prefixWord ++ tailWord_1154772) baseStart_1154772 baseEnd_1154772 := by
    simpa [prefixWord, tailWord_1154772, baseEnd_1154772] using wordTrace_append hprefix tailTrace_1154772
  have hstable : (prefixWord ++ tailWord_1154772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154772).length < 2 ^ (prefixWord ++ tailWord_1154772).sum := by decide
  have hdescent : baseEnd_1154772 < baseStart_1154772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154817 : List Nat := [1, 2, 4, 1, 1, 1, 3, 5, 3]
def baseStart_1154817 : Nat := 118140960795 + 1154817 * 2 ^ 59
def prefixEnd_1154817 : Nat := 4983230072969 + 3 ^ 40 * 1154817 * 2
def baseEnd_1154817 : Nat := 263544972881472669722933

theorem tailTrace_1154817 : CollatzResearch.WordTrace tailWord_1154817 prefixEnd_1154817 263544972881472669722933 := by
  unfold tailWord_1154817
  simp only [CollatzResearch.WordTrace]
  refine ⟨42119636257302710886662705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28079757504868473924441803 42119636257302710886662705)
  ·
    refine ⟨31589727192977033164997029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42119636257302710886662705 31589727192977033164997029)
    ·
      refine ⟨5923073848683193718436943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31589727192977033164997029 5923073848683193718436943)
      ·
        refine ⟨8884610773024790577655415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5923073848683193718436943 8884610773024790577655415)
        ·
          refine ⟨13326916159537185866483123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8884610773024790577655415 13326916159537185866483123)
          ·
            refine ⟨19990374239305778799724685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13326916159537185866483123 19990374239305778799724685)
            ·
              refine ⟨7496390339739667049896757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19990374239305778799724685 7496390339739667049896757)
              ·
                refine ⟨702786594350593785927821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7496390339739667049896757 702786594350593785927821)
                ·
                  refine ⟨263544972881472669722933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702786594350593785927821 263544972881472669722933)
                  ·
                    rfl

theorem cell21_1154817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_1154817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154817 prefixEnd_1154817 := by exact prefixLift 1154817
  have htrace : WordTrace (prefixWord ++ tailWord_1154817) baseStart_1154817 baseEnd_1154817 := by
    simpa [prefixWord, tailWord_1154817, baseEnd_1154817] using wordTrace_append hprefix tailTrace_1154817
  have hstable : (prefixWord ++ tailWord_1154817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154817).length < 2 ^ (prefixWord ++ tailWord_1154817).sum := by decide
  have hdescent : baseEnd_1154817 < baseStart_1154817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154834 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_1154834 : Nat := 118140960795 + 1154834 * 2 ^ 59
def prefixEnd_1154834 : Nat := 4983230072969 + 3 ^ 40 * 1154834 * 2
def baseEnd_1154834 : Nat := 263548852513084417939565

theorem tailTrace_1154834 : CollatzResearch.WordTrace tailWord_1154834 prefixEnd_1154834 263548852513084417939565 := by
  unfold tailWord_1154834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10530064074560280697507889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28080170865494081860021037 10530064074560280697507889)
  ·
    refine ⟨7897548055920210523130917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10530064074560280697507889 7897548055920210523130917)
    ·
      refine ⟨1480790260485039473087047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7897548055920210523130917 1480790260485039473087047)
      ·
        refine ⟨2221185390727559209630571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480790260485039473087047 2221185390727559209630571)
        ·
          refine ⟨3331778086091338814445857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221185390727559209630571 3331778086091338814445857)
          ·
            refine ⟨2498833564568504110834393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3331778086091338814445857 2498833564568504110834393)
            ·
              refine ⟨1874125173426378083125795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498833564568504110834393 1874125173426378083125795)
              ·
                refine ⟨2811187760139567124688693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874125173426378083125795 2811187760139567124688693)
                ·
                  refine ⟨263548852513084417939565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2811187760139567124688693 263548852513084417939565)
                  ·
                    rfl

theorem cell21_1154834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_1154834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154834 prefixEnd_1154834 := by exact prefixLift 1154834
  have htrace : WordTrace (prefixWord ++ tailWord_1154834) baseStart_1154834 baseEnd_1154834 := by
    simpa [prefixWord, tailWord_1154834, baseEnd_1154834] using wordTrace_append hprefix tailTrace_1154834
  have hstable : (prefixWord ++ tailWord_1154834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154834).length < 2 ^ (prefixWord ++ tailWord_1154834).sum := by decide
  have hdescent : baseEnd_1154834 < baseStart_1154834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154848 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_1154848 : Nat := 118140960795 + 1154848 * 2 ^ 59
def prefixEnd_1154848 : Nat := 4983230072969 + 3 ^ 40 * 1154848 * 2
def baseEnd_1154848 : Nat := 263552047503823504706203

theorem tailTrace_1154848 : CollatzResearch.WordTrace tailWord_1154848 prefixEnd_1154848 263552047503823504706203 := by
  unfold tailWord_1154848
  simp only [CollatzResearch.WordTrace]
  refine ⟨21060383460095201590520599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28080511280126935454027465 21060383460095201590520599)
  ·
    refine ⟨31590575190142802385780899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21060383460095201590520599 31590575190142802385780899)
    ·
      refine ⟨47385862785214203578671349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31590575190142802385780899 47385862785214203578671349)
      ·
        refine ⟨4442424636113831585500439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47385862785214203578671349 4442424636113831585500439)
        ·
          refine ⟨6663636954170747378250659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4442424636113831585500439 6663636954170747378250659)
          ·
            refine ⟨9995455431256121067375989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663636954170747378250659 9995455431256121067375989)
            ·
              refine ⟨937073946680261350066499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9995455431256121067375989 937073946680261350066499)
              ·
                refine ⟨1405610920020392025099749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937073946680261350066499 1405610920020392025099749)
                ·
                  refine ⟨263552047503823504706203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1405610920020392025099749 263552047503823504706203)
                  ·
                    rfl

theorem cell21_1154848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_1154848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154848 prefixEnd_1154848 := by exact prefixLift 1154848
  have htrace : WordTrace (prefixWord ++ tailWord_1154848) baseStart_1154848 baseEnd_1154848 := by
    simpa [prefixWord, tailWord_1154848, baseEnd_1154848] using wordTrace_append hprefix tailTrace_1154848
  have hstable : (prefixWord ++ tailWord_1154848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154848).length < 2 ^ (prefixWord ++ tailWord_1154848).sum := by decide
  have hdescent : baseEnd_1154848 < baseStart_1154848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154890 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1154890 : Nat := 118140960795 + 1154890 * 2 ^ 59
def prefixEnd_1154890 : Nat := 4983230072969 + 3 ^ 40 * 1154890 * 2
def baseEnd_1154890 : Nat := 263561632476040765006117

theorem tailTrace_1154890 : CollatzResearch.WordTrace tailWord_1154890 prefixEnd_1154890 263561632476040765006117 := by
  unfold tailWord_1154890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10530574696509561088517531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28081532524025496236046749 10530574696509561088517531)
  ·
    refine ⟨15795862044764341632776297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10530574696509561088517531 15795862044764341632776297)
    ·
      refine ⟨11846896533573256224582223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15795862044764341632776297 11846896533573256224582223)
      ·
        refine ⟨17770344800359884336873335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11846896533573256224582223 17770344800359884336873335)
        ·
          refine ⟨26655517200539826505310003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17770344800359884336873335 26655517200539826505310003)
          ·
            refine ⟨39983275800809739757965005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26655517200539826505310003 39983275800809739757965005)
            ·
              refine ⟨14993728425303652409236877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39983275800809739757965005 14993728425303652409236877)
              ·
                refine ⟨5622648159488869653463829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14993728425303652409236877 5622648159488869653463829)
                ·
                  refine ⟨263561632476040765006117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5622648159488869653463829 263561632476040765006117)
                  ·
                    rfl

theorem cell21_1154890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1154890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154890 prefixEnd_1154890 := by exact prefixLift 1154890
  have htrace : WordTrace (prefixWord ++ tailWord_1154890) baseStart_1154890 baseEnd_1154890 := by
    simpa [prefixWord, tailWord_1154890, baseEnd_1154890] using wordTrace_append hprefix tailTrace_1154890
  have hstable : (prefixWord ++ tailWord_1154890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154890).length < 2 ^ (prefixWord ++ tailWord_1154890).sum := by decide
  have hdescent : baseEnd_1154890 < baseStart_1154890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154997 : List Nat := [1, 3, 3, 2, 1, 3, 8]
def baseStart_1154997 : Nat := 118140960795 + 1154997 * 2 ^ 59
def prefixEnd_1154997 : Nat := 4983230072969 + 3 ^ 40 * 1154997 * 2
def baseEnd_1154997 : Nat := 29287339037092484080285

theorem tailTrace_1154997 : CollatzResearch.WordTrace tailWord_1154997 prefixEnd_1154997 29287339037092484080285 := by
  unfold tailWord_1154997
  simp only [CollatzResearch.WordTrace]
  refine ⟨42126201396650601628215245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28084134264433734418810163 42126201396650601628215245)
  ·
    refine ⟨15797325523743975610580717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42126201396650601628215245 15797325523743975610580717)
    ·
      refine ⟨5923997071403990853967769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15797325523743975610580717 5923997071403990853967769)
      ·
        refine ⟨4442997803552993140475827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5923997071403990853967769 4442997803552993140475827)
        ·
          refine ⟨6664496705329489710713741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4442997803552993140475827 6664496705329489710713741)
          ·
            refine ⟨2499186264498558641517653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6664496705329489710713741 2499186264498558641517653)
            ·
              refine ⟨29287339037092484080285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2499186264498558641517653 29287339037092484080285)
              ·
                rfl

theorem cell21_1154997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 8].length) (baseStart_1154997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1154997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1154997 prefixEnd_1154997 := by exact prefixLift 1154997
  have htrace : WordTrace (prefixWord ++ tailWord_1154997) baseStart_1154997 baseEnd_1154997 := by
    simpa [prefixWord, tailWord_1154997, baseEnd_1154997] using wordTrace_append hprefix tailTrace_1154997
  have hstable : (prefixWord ++ tailWord_1154997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154997).length < 2 ^ (prefixWord ++ tailWord_1154997).sum := by decide
  have hdescent : baseEnd_1154997 < baseStart_1154997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155028 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1155028 : Nat := 118140960795 + 1155028 * 2 ^ 59
def prefixEnd_1155028 : Nat := 4983230072969 + 3 ^ 40 * 1155028 * 2
def baseEnd_1155028 : Nat := 263593125956183191705835

theorem tailTrace_1155028 : CollatzResearch.WordTrace tailWord_1155028 prefixEnd_1155028 263593125956183191705835 := by
  unfold tailWord_1155028
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063666029769146961296869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28084888039692195948395825 21063666029769146961296869)
  ·
    refine ⟨3949437380581715055243163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21063666029769146961296869 3949437380581715055243163)
    ·
      refine ⟨5924156070872572582864745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3949437380581715055243163 5924156070872572582864745)
      ·
        refine ⟨4443117053154429437148559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5924156070872572582864745 4443117053154429437148559)
        ·
          refine ⟨6664675579731644155722839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4443117053154429437148559 6664675579731644155722839)
          ·
            refine ⟨9997013369597466233584259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6664675579731644155722839 9997013369597466233584259)
            ·
              refine ⟨14995520054396199350376389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9997013369597466233584259 14995520054396199350376389)
              ·
                refine ⟨2811660010199287378195573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14995520054396199350376389 2811660010199287378195573)
                ·
                  refine ⟨263593125956183191705835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2811660010199287378195573 263593125956183191705835)
                  ·
                    rfl

theorem cell21_1155028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1155028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155028 prefixEnd_1155028 := by exact prefixLift 1155028
  have htrace : WordTrace (prefixWord ++ tailWord_1155028) baseStart_1155028 baseEnd_1155028 := by
    simpa [prefixWord, tailWord_1155028, baseEnd_1155028] using wordTrace_append hprefix tailTrace_1155028
  have hstable : (prefixWord ++ tailWord_1155028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155028).length < 2 ^ (prefixWord ++ tailWord_1155028).sum := by decide
  have hdescent : baseEnd_1155028 < baseStart_1155028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155056 : List Nat := [2, 1, 1, 1, 3, 2, 11]
def baseStart_1155056 : Nat := 118140960795 + 1155056 * 2 ^ 59
def prefixEnd_1155056 : Nat := 4983230072969 + 3 ^ 40 * 1155056 * 2
def baseEnd_1155056 : Nat := 29288835104184596137679

theorem tailTrace_1155056 : CollatzResearch.WordTrace tailWord_1155056 prefixEnd_1155056 29288835104184596137679 := by
  unfold tailWord_1155056
  simp only [CollatzResearch.WordTrace]
  refine ⟨21064176651718427352306511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28085568868957903136408681 21064176651718427352306511)
  ·
    refine ⟨31596264977577641028459767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21064176651718427352306511 31596264977577641028459767)
    ·
      refine ⟨47394397466366461542689651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31596264977577641028459767 47394397466366461542689651)
      ·
        refine ⟨71091596199549692314034477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47394397466366461542689651 71091596199549692314034477)
        ·
          refine ⟨26659348574831134617762929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71091596199549692314034477 26659348574831134617762929)
          ·
            refine ⟨19994511431123350963322197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26659348574831134617762929 19994511431123350963322197)
            ·
              refine ⟨29288835104184596137679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19994511431123350963322197 29288835104184596137679)
              ·
                rfl

theorem cell21_1155056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 11].length) (baseStart_1155056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155056 prefixEnd_1155056 := by exact prefixLift 1155056
  have htrace : WordTrace (prefixWord ++ tailWord_1155056) baseStart_1155056 baseEnd_1155056 := by
    simpa [prefixWord, tailWord_1155056, baseEnd_1155056] using wordTrace_append hprefix tailTrace_1155056
  have hstable : (prefixWord ++ tailWord_1155056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155056).length < 2 ^ (prefixWord ++ tailWord_1155056).sum := by decide
  have hdescent : baseEnd_1155056 < baseStart_1155056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155062 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1155062 : Nat := 118140960795 + 1155062 * 2 ^ 59
def prefixEnd_1155062 : Nat := 4983230072969 + 3 ^ 40 * 1155062 * 2
def baseEnd_1155062 : Nat := 263600885219406688139099

theorem tailTrace_1155062 : CollatzResearch.WordTrace tailWord_1155062 prefixEnd_1155062 263600885219406688139099 := by
  unfold tailWord_1155062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633035758838444858083215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28085714760943411819554293 2633035758838444858083215)
  ·
    refine ⟨3949553638257667287124823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2633035758838444858083215 3949553638257667287124823)
    ·
      refine ⟨5924330457386500930687235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3949553638257667287124823 5924330457386500930687235)
      ·
        refine ⟨8886495686079751396030853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5924330457386500930687235 8886495686079751396030853)
        ·
          refine ⟨1666217941139953386755785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8886495686079751396030853 1666217941139953386755785)
          ·
            refine ⟨1249663455854965040066839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666217941139953386755785 1249663455854965040066839)
            ·
              refine ⟨1874495183782447560100259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249663455854965040066839 1874495183782447560100259)
              ·
                refine ⟨2811742775673671340150389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874495183782447560100259 2811742775673671340150389)
                ·
                  refine ⟨263600885219406688139099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2811742775673671340150389 263600885219406688139099)
                  ·
                    rfl

theorem cell21_1155062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1155062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155062 prefixEnd_1155062 := by exact prefixLift 1155062
  have htrace : WordTrace (prefixWord ++ tailWord_1155062) baseStart_1155062 baseEnd_1155062 := by
    simpa [prefixWord, tailWord_1155062, baseEnd_1155062] using wordTrace_append hprefix tailTrace_1155062
  have hstable : (prefixWord ++ tailWord_1155062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155062).length < 2 ^ (prefixWord ++ tailWord_1155062).sum := by decide
  have hdescent : baseEnd_1155062 < baseStart_1155062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155073 : List Nat := [1, 2, 4, 1, 2, 1, 4, 6]
def baseStart_1155073 : Nat := 118140960795 + 1155073 * 2 ^ 59
def prefixEnd_1155073 : Nat := 4983230072969 + 3 ^ 40 * 1155073 * 2
def baseEnd_1155073 : Nat := 87867798523091037818581

theorem tailTrace_1155073 : CollatzResearch.WordTrace tailWord_1155073 prefixEnd_1155073 87867798523091037818581 := by
  unfold tailWord_1155073
  simp only [CollatzResearch.WordTrace]
  refine ⟨42128973344375266607981873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28085982229583511071987915 42128973344375266607981873)
  ·
    refine ⟨31596730008281449955986405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42128973344375266607981873 31596730008281449955986405)
    ·
      refine ⟨5924386876552771866747451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31596730008281449955986405 5924386876552771866747451)
      ·
        refine ⟨8886580314829157800121177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5924386876552771866747451 8886580314829157800121177)
        ·
          refine ⟨6664935236121868350090883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8886580314829157800121177 6664935236121868350090883)
          ·
            refine ⟨9997402854182802525136325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6664935236121868350090883 9997402854182802525136325)
            ·
              refine ⟨1874513035159275473463061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9997402854182802525136325 1874513035159275473463061)
              ·
                refine ⟨87867798523091037818581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1874513035159275473463061 87867798523091037818581)
                ·
                  rfl

theorem cell21_1155073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 6].length) (baseStart_1155073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155073 prefixEnd_1155073 := by exact prefixLift 1155073
  have htrace : WordTrace (prefixWord ++ tailWord_1155073) baseStart_1155073 baseEnd_1155073 := by
    simpa [prefixWord, tailWord_1155073, baseEnd_1155073] using wordTrace_append hprefix tailTrace_1155073
  have hstable : (prefixWord ++ tailWord_1155073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155073).length < 2 ^ (prefixWord ++ tailWord_1155073).sum := by decide
  have hdescent : baseEnd_1155073 < baseStart_1155073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155121 : List Nat := [1, 2, 2, 3, 1, 4, 1, 4, 3]
def baseStart_1155121 : Nat := 118140960795 + 1155121 * 2 ^ 59
def prefixEnd_1155121 : Nat := 4983230072969 + 3 ^ 40 * 1155121 * 2
def baseEnd_1155121 : Nat := 263614349823235696655645

theorem tailTrace_1155121 : CollatzResearch.WordTrace tailWord_1155121 prefixEnd_1155121 263614349823235696655645 := by
  unfold tailWord_1155121
  simp only [CollatzResearch.WordTrace]
  refine ⟨42130724048201370805729217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28087149365467580537152811 42130724048201370805729217)
  ·
    refine ⟨31598043036151028104296913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42130724048201370805729217 31598043036151028104296913)
    ·
      refine ⟨23698532277113271078222685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31598043036151028104296913 23698532277113271078222685)
      ·
        refine ⟨8886949603917476654333507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23698532277113271078222685 8886949603917476654333507)
        ·
          refine ⟨13330424405876214981500261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8886949603917476654333507 13330424405876214981500261)
          ·
            refine ⟨2499454576101790309031299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13330424405876214981500261 2499454576101790309031299)
            ·
              refine ⟨3749181864152685463546949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499454576101790309031299 3749181864152685463546949)
              ·
                refine ⟨702971599528628524415053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3749181864152685463546949 702971599528628524415053)
                ·
                  refine ⟨263614349823235696655645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702971599528628524415053 263614349823235696655645)
                  ·
                    rfl

theorem cell21_1155121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_1155121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155121 prefixEnd_1155121 := by exact prefixLift 1155121
  have htrace : WordTrace (prefixWord ++ tailWord_1155121) baseStart_1155121 baseEnd_1155121 := by
    simpa [prefixWord, tailWord_1155121, baseEnd_1155121] using wordTrace_append hprefix tailTrace_1155121
  have hstable : (prefixWord ++ tailWord_1155121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155121).length < 2 ^ (prefixWord ++ tailWord_1155121).sum := by decide
  have hdescent : baseEnd_1155121 < baseStart_1155121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155124 : List Nat := [2, 5, 1, 2, 3, 1, 1, 6]
def baseStart_1155124 : Nat := 118140960795 + 1155124 * 2 ^ 59
def prefixEnd_1155124 : Nat := 4983230072969 + 3 ^ 40 * 1155124 * 2
def baseEnd_1155124 : Nat := 87871678154702786035213

theorem tailTrace_1155124 : CollatzResearch.WordTrace tailWord_1155124 prefixEnd_1155124 87871678154702786035213 := by
  unfold tailWord_1155124
  simp only [CollatzResearch.WordTrace]
  refine ⟨21065416733595251159044213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28087222311460334878725617 21065416733595251159044213)
  ·
    refine ⟨1974882818774554796160395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21065416733595251159044213 1974882818774554796160395)
    ·
      refine ⟨2962324228161832194240593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974882818774554796160395 2962324228161832194240593)
      ·
        refine ⟨2221743171121374145680445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2962324228161832194240593 2221743171121374145680445)
        ·
          refine ⟨833153689170515304630167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2221743171121374145680445 833153689170515304630167)
          ·
            refine ⟨1249730533755772956945251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833153689170515304630167 1249730533755772956945251)
            ·
              refine ⟨1874595800633659435417877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249730533755772956945251 1874595800633659435417877)
              ·
                refine ⟨87871678154702786035213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1874595800633659435417877 87871678154702786035213)
                ·
                  rfl

theorem cell21_1155124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_1155124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155124 prefixEnd_1155124 := by exact prefixLift 1155124
  have htrace : WordTrace (prefixWord ++ tailWord_1155124) baseStart_1155124 baseEnd_1155124 := by
    simpa [prefixWord, tailWord_1155124, baseEnd_1155124] using wordTrace_append hprefix tailTrace_1155124
  have hstable : (prefixWord ++ tailWord_1155124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155124).length < 2 ^ (prefixWord ++ tailWord_1155124).sum := by decide
  have hdescent : baseEnd_1155124 < baseStart_1155124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155180 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1155180 : Nat := 118140960795 + 1155180 * 2 ^ 59
def prefixEnd_1155180 : Nat := 4983230072969 + 3 ^ 40 * 1155180 * 2
def baseEnd_1155180 : Nat := 263627814427064705172191

theorem tailTrace_1155180 : CollatzResearch.WordTrace tailWord_1155180 prefixEnd_1155180 263627814427064705172191 := by
  unfold tailWord_1155180
  simp only [CollatzResearch.WordTrace]
  refine ⟨21066437977493811941063497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28088583969991749254751329 21066437977493811941063497)
  ·
    refine ⟨15799828483120358955797623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21066437977493811941063497 15799828483120358955797623)
    ·
      refine ⟨23699742724680538433696435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15799828483120358955797623 23699742724680538433696435)
      ·
        refine ⟨35549614087020807650544653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23699742724680538433696435 35549614087020807650544653)
        ·
          refine ⟨13331105282632802868954245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35549614087020807650544653 13331105282632802868954245)
          ·
            refine ⟨2499582240493650537928921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13331105282632802868954245 2499582240493650537928921)
            ·
              refine ⟨1874686680370237903446691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2499582240493650537928921 1874686680370237903446691)
              ·
                refine ⟨2812030020555356855170037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874686680370237903446691 2812030020555356855170037)
                ·
                  refine ⟨263627814427064705172191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2812030020555356855170037 263627814427064705172191)
                  ·
                    rfl

theorem cell21_1155180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1155180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155180 prefixEnd_1155180 := by exact prefixLift 1155180
  have htrace : WordTrace (prefixWord ++ tailWord_1155180) baseStart_1155180 baseEnd_1155180 := by
    simpa [prefixWord, tailWord_1155180, baseEnd_1155180] using wordTrace_append hprefix tailTrace_1155180
  have hstable : (prefixWord ++ tailWord_1155180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155180).length < 2 ^ (prefixWord ++ tailWord_1155180).sum := by decide
  have hdescent : baseEnd_1155180 < baseStart_1155180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155245 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1155245 : Nat := 118140960795 + 1155245 * 2 ^ 59
def prefixEnd_1155245 : Nat := 4983230072969 + 3 ^ 40 * 1155245 * 2
def baseEnd_1155245 : Nat := 263642648312639036588725

theorem tailTrace_1155245 : CollatzResearch.WordTrace tailWord_1155245 prefixEnd_1155245 263642648312639036588725 := by
  unfold tailWord_1155245
  simp only [CollatzResearch.WordTrace]
  refine ⟨42135246699752139983243189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28090164466501426655495459 42135246699752139983243189)
  ·
    refine ⟨3950179378101763123429049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42135246699752139983243189 3950179378101763123429049)
    ·
      refine ⟨2962634533576322342571787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3950179378101763123429049 2962634533576322342571787)
      ·
        refine ⟨4443951800364483513857681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962634533576322342571787 4443951800364483513857681)
        ·
          refine ⟨3332963850273362635393261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4443951800364483513857681 3332963850273362635393261)
          ·
            refine ⟨1249861443852510988272473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3332963850273362635393261 1249861443852510988272473)
            ·
              refine ⟨937396082889383241204355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249861443852510988272473 937396082889383241204355)
              ·
                refine ⟨1406094124334074861806533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937396082889383241204355 1406094124334074861806533)
                ·
                  refine ⟨263642648312639036588725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406094124334074861806533 263642648312639036588725)
                  ·
                    rfl

theorem cell21_1155245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1155245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155245 prefixEnd_1155245 := by exact prefixLift 1155245
  have htrace : WordTrace (prefixWord ++ tailWord_1155245) baseStart_1155245 baseEnd_1155245 := by
    simpa [prefixWord, tailWord_1155245, baseEnd_1155245] using wordTrace_append hprefix tailTrace_1155245
  have hstable : (prefixWord ++ tailWord_1155245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155245).length < 2 ^ (prefixWord ++ tailWord_1155245).sum := by decide
  have hdescent : baseEnd_1155245 < baseStart_1155245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155284 : List Nat := [2, 4, 1, 14]
def baseStart_1155284 : Nat := 118140960795 + 1155284 * 2 ^ 59
def prefixEnd_1155284 : Nat := 4983230072969 + 3 ^ 40 * 1155284 * 2
def baseEnd_1155284 : Nat := 1084985796888821545015

theorem tailTrace_1155284 : CollatzResearch.WordTrace tailWord_1155284 prefixEnd_1155284 1084985796888821545015 := by
  unfold tailWord_1155284
  simp only [CollatzResearch.WordTrace]
  refine ⟨21068334573305424821956453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28091112764407233095941937 21068334573305424821956453)
  ·
    refine ⟨3950312732494767154116835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21068334573305424821956453 3950312732494767154116835)
    ·
      refine ⟨5925469098742150731175253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3950312732494767154116835 5925469098742150731175253)
      ·
        refine ⟨1084985796888821545015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 5925469098742150731175253 1084985796888821545015)
        ·
          rfl

theorem cell21_1155284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 14].length) (baseStart_1155284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155284 prefixEnd_1155284 := by exact prefixLift 1155284
  have htrace : WordTrace (prefixWord ++ tailWord_1155284) baseStart_1155284 baseEnd_1155284 := by
    simpa [prefixWord, tailWord_1155284, baseEnd_1155284] using wordTrace_append hprefix tailTrace_1155284
  have hstable : (prefixWord ++ tailWord_1155284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155284).length < 2 ^ (prefixWord ++ tailWord_1155284).sum := by decide
  have hdescent : baseEnd_1155284 < baseStart_1155284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155301 : List Nat := [1, 3, 1, 4, 2, 1, 3, 6]
def baseStart_1155301 : Nat := 118140960795 + 1155301 * 2 ^ 59
def prefixEnd_1155301 : Nat := 4983230072969 + 3 ^ 40 * 1155301 * 2
def baseEnd_1155301 : Nat := 87885142758531794551759

theorem tailTrace_1155301 : CollatzResearch.WordTrace tailWord_1155301 prefixEnd_1155301 87885142758531794551759 := by
  unfold tailWord_1155301
  simp only [CollatzResearch.WordTrace]
  refine ⟨42137289187549261547281757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28091526125032841031521171 42137289187549261547281757)
  ·
    refine ⟨15801483445330973080230659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42137289187549261547281757 15801483445330973080230659)
    ·
      refine ⟨23702225167996459620345989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15801483445330973080230659 23702225167996459620345989)
      ·
        refine ⟨4444167218999336178814873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23702225167996459620345989 4444167218999336178814873)
        ·
          refine ⟨3333125414249502134111155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4444167218999336178814873 3333125414249502134111155)
          ·
            refine ⟨4999688121374253201166733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333125414249502134111155 4999688121374253201166733)
            ·
              refine ⟨1874883045515344950437525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4999688121374253201166733 1874883045515344950437525)
              ·
                refine ⟨87885142758531794551759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1874883045515344950437525 87885142758531794551759)
                ·
                  rfl

theorem cell21_1155301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 6].length) (baseStart_1155301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155301 prefixEnd_1155301 := by exact prefixLift 1155301
  have htrace : WordTrace (prefixWord ++ tailWord_1155301) baseStart_1155301 baseEnd_1155301 := by
    simpa [prefixWord, tailWord_1155301, baseEnd_1155301] using wordTrace_append hprefix tailTrace_1155301
  have hstable : (prefixWord ++ tailWord_1155301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155301).length < 2 ^ (prefixWord ++ tailWord_1155301).sum := by decide
  have hdescent : baseEnd_1155301 < baseStart_1155301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155315 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 5]
def baseStart_1155315 : Nat := 118140960795 + 1155315 * 2 ^ 59
def prefixEnd_1155315 : Nat := 4983230072969 + 3 ^ 40 * 1155315 * 2
def baseEnd_1155315 : Nat := 263658623266334470421915

theorem tailTrace_1155315 : CollatzResearch.WordTrace tailWord_1155315 prefixEnd_1155315 263658623266334470421915 := by
  unfold tailWord_1155315
  simp only [CollatzResearch.WordTrace]
  refine ⟨42137799809498541938291399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28091866539665694625527599 42137799809498541938291399)
  ·
    refine ⟨63206699714247812907437099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42137799809498541938291399 63206699714247812907437099)
    ·
      refine ⟨94810049571371719361155649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63206699714247812907437099 94810049571371719361155649)
      ·
        refine ⟨71107537178528789520866737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94810049571371719361155649 71107537178528789520866737)
        ·
          refine ⟨53330652883896592140650053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71107537178528789520866737 53330652883896592140650053)
          ·
            refine ⟨9999497415730611026371885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53330652883896592140650053 9999497415730611026371885)
            ·
              refine ⟨3749811530898979134889457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9999497415730611026371885 3749811530898979134889457)
              ·
                refine ⟨2812358648174234351167093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3749811530898979134889457 2812358648174234351167093)
                ·
                  refine ⟨263658623266334470421915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2812358648174234351167093 263658623266334470421915)
                  ·
                    rfl

theorem cell21_1155315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_1155315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155315 prefixEnd_1155315 := by exact prefixLift 1155315
  have htrace : WordTrace (prefixWord ++ tailWord_1155315) baseStart_1155315 baseEnd_1155315 := by
    simpa [prefixWord, tailWord_1155315, baseEnd_1155315] using wordTrace_append hprefix tailTrace_1155315
  have hstable : (prefixWord ++ tailWord_1155315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155315).length < 2 ^ (prefixWord ++ tailWord_1155315).sum := by decide
  have hdescent : baseEnd_1155315 < baseStart_1155315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155363 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 4]
def baseStart_1155363 : Nat := 118140960795 + 1155363 * 2 ^ 59
def prefixEnd_1155363 : Nat := 4983230072969 + 3 ^ 40 * 1155363 * 2
def baseEnd_1155363 : Nat := 263669577520297053621817

theorem tailTrace_1155363 : CollatzResearch.WordTrace tailWord_1155363 prefixEnd_1155363 263669577520297053621817 := by
  unfold tailWord_1155363
  simp only [CollatzResearch.WordTrace]
  refine ⟨42139550513324646136038743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28093033675549764090692495 42139550513324646136038743)
  ·
    refine ⟨63209325769986969204058115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42139550513324646136038743 63209325769986969204058115)
    ·
      refine ⟨94813988654980453806087173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63209325769986969204058115 94813988654980453806087173)
      ·
        refine ⟨17777622872808835088641345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94813988654980453806087173 17777622872808835088641345)
        ·
          refine ⟨13333217154606626316481009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17777622872808835088641345 13333217154606626316481009)
          ·
            refine ⟨9999912865954969737360757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13333217154606626316481009 9999912865954969737360757)
            ·
              refine ⟨937491831183278412877571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9999912865954969737360757 937491831183278412877571)
              ·
                refine ⟨1406237746774917619316357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937491831183278412877571 1406237746774917619316357)
                ·
                  refine ⟨263669577520297053621817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406237746774917619316357 263669577520297053621817)
                  ·
                    rfl

theorem cell21_1155363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 4].length) (baseStart_1155363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155363 prefixEnd_1155363 := by exact prefixLift 1155363
  have htrace : WordTrace (prefixWord ++ tailWord_1155363) baseStart_1155363 baseEnd_1155363 := by
    simpa [prefixWord, tailWord_1155363, baseEnd_1155363] using wordTrace_append hprefix tailTrace_1155363
  have hstable : (prefixWord ++ tailWord_1155363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155363).length < 2 ^ (prefixWord ++ tailWord_1155363).sum := by decide
  have hdescent : baseEnd_1155363 < baseStart_1155363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155377 : List Nat := [1, 2, 2, 3, 4, 1, 1, 7]
def baseStart_1155377 : Nat := 118140960795 + 1155377 * 2 ^ 59
def prefixEnd_1155377 : Nat := 4983230072969 + 3 ^ 40 * 1155377 * 2
def baseEnd_1155377 : Nat := 87890924170345380129485

theorem tailTrace_1155377 : CollatzResearch.WordTrace tailWord_1155377 prefixEnd_1155377 87890924170345380129485 := by
  unfold tailWord_1155377
  simp only [CollatzResearch.WordTrace]
  refine ⟨42140061135273926527048385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28093374090182617684698923 42140061135273926527048385)
  ·
    refine ⟨31605045851455444895286289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42140061135273926527048385 31605045851455444895286289)
    ·
      refine ⟨23703784388591583671464717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31605045851455444895286289 23703784388591583671464717)
      ·
        refine ⟨8888919145721843876799269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23703784388591583671464717 8888919145721843876799269)
        ·
          refine ⟨1666672339822845726899863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8888919145721843876799269 1666672339822845726899863)
          ·
            refine ⟨2500008509734268590349795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666672339822845726899863 2500008509734268590349795)
            ·
              refine ⟨3750012764601402885524693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500008509734268590349795 3750012764601402885524693)
              ·
                refine ⟨87890924170345380129485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3750012764601402885524693 87890924170345380129485)
                ·
                  rfl

theorem cell21_1155377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 7].length) (baseStart_1155377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155377 prefixEnd_1155377 := by exact prefixLift 1155377
  have htrace : WordTrace (prefixWord ++ tailWord_1155377) baseStart_1155377 baseEnd_1155377 := by
    simpa [prefixWord, tailWord_1155377, baseEnd_1155377] using wordTrace_append hprefix tailTrace_1155377
  have hstable : (prefixWord ++ tailWord_1155377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155377).length < 2 ^ (prefixWord ++ tailWord_1155377).sum := by decide
  have hdescent : baseEnd_1155377 < baseStart_1155377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155408 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_1155408 : Nat := 118140960795 + 1155408 * 2 ^ 59
def prefixEnd_1155408 : Nat := 4983230072969 + 3 ^ 40 * 1155408 * 2
def baseEnd_1155408 : Nat := 263679847133386975371725

theorem tailTrace_1155408 : CollatzResearch.WordTrace tailWord_1155408 prefixEnd_1155408 263679847133386975371725 := by
  unfold tailWord_1155408
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070595899080809410713439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28094127865441079214284585 21070595899080809410713439)
  ·
    refine ⟨31605893848621214116070159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21070595899080809410713439 31605893848621214116070159)
    ·
      refine ⟨47408840772931821174105239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31605893848621214116070159 47408840772931821174105239)
      ·
        refine ⟨71113261159397731761157859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47408840772931821174105239 71113261159397731761157859)
        ·
          refine ⟨106669891739096597641736789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71113261159397731761157859 106669891739096597641736789)
          ·
            refine ⟨1250037793817538253614103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 106669891739096597641736789 1250037793817538253614103)
            ·
              refine ⟨1875056690726307380421155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250037793817538253614103 1875056690726307380421155)
              ·
                refine ⟨2812585036089461070631733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875056690726307380421155 2812585036089461070631733)
                ·
                  refine ⟨263679847133386975371725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2812585036089461070631733 263679847133386975371725)
                  ·
                    rfl

theorem cell21_1155408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_1155408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155408 prefixEnd_1155408 := by exact prefixLift 1155408
  have htrace : WordTrace (prefixWord ++ tailWord_1155408) baseStart_1155408 baseEnd_1155408 := by
    simpa [prefixWord, tailWord_1155408, baseEnd_1155408] using wordTrace_append hprefix tailTrace_1155408
  have hstable : (prefixWord ++ tailWord_1155408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155408).length < 2 ^ (prefixWord ++ tailWord_1155408).sum := by decide
  have hdescent : baseEnd_1155408 < baseStart_1155408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155459 : List Nat := [1, 1, 1, 3, 7, 1, 2, 2, 3]
def baseStart_1155459 : Nat := 118140960795 + 1155459 * 2 ^ 59
def prefixEnd_1155459 : Nat := 4983230072969 + 3 ^ 40 * 1155459 * 2
def baseEnd_1155459 : Nat := 263691486028222220021621

theorem tailTrace_1155459 : CollatzResearch.WordTrace tailWord_1155459 prefixEnd_1155459 263691486028222220021621 := by
  unfold tailWord_1155459
  simp only [CollatzResearch.WordTrace]
  refine ⟨42143051920976854531533431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28095367947317903021022287 42143051920976854531533431)
  ·
    refine ⟨63214577881465281797300147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42143051920976854531533431 63214577881465281797300147)
    ·
      refine ⟨94821866822197922695950221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63214577881465281797300147 94821866822197922695950221)
      ·
        refine ⟨35558200058324221010981333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94821866822197922695950221 35558200058324221010981333)
        ·
          refine ⟨833395313866973929944875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35558200058324221010981333 833395313866973929944875)
          ·
            refine ⟨1250092970800460894917313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833395313866973929944875 1250092970800460894917313)
            ·
              refine ⟨937569728100345671187985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250092970800460894917313 937569728100345671187985)
              ·
                refine ⟨703177296075259253390989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937569728100345671187985 703177296075259253390989)
                ·
                  refine ⟨263691486028222220021621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703177296075259253390989 263691486028222220021621)
                  ·
                    rfl

theorem cell21_1155459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 3].length) (baseStart_1155459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155459 prefixEnd_1155459 := by exact prefixLift 1155459
  have htrace : WordTrace (prefixWord ++ tailWord_1155459) baseStart_1155459 baseEnd_1155459 := by
    simpa [prefixWord, tailWord_1155459, baseEnd_1155459] using wordTrace_append hprefix tailTrace_1155459
  have hstable : (prefixWord ++ tailWord_1155459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155459).length < 2 ^ (prefixWord ++ tailWord_1155459).sum := by decide
  have hdescent : baseEnd_1155459 < baseStart_1155459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155470 : List Nat := [4, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1155470 : Nat := 118140960795 + 1155470 * 2 ^ 59
def prefixEnd_1155470 : Nat := 4983230072969 + 3 ^ 40 * 1155470 * 2
def baseEnd_1155470 : Nat := 87897998792696215112755

theorem tailTrace_1155470 : CollatzResearch.WordTrace tailWord_1155470 prefixEnd_1155470 87897998792696215112755 := by
  unfold tailWord_1155470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267931640492125426272983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28095635415958002273455909 5267931640492125426272983)
  ·
    refine ⟨7901897460738188139409475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5267931640492125426272983 7901897460738188139409475)
    ·
      refine ⟨11852846191107282209114213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7901897460738188139409475 11852846191107282209114213)
      ·
        refine ⟨2222408660832615414208915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11852846191107282209114213 2222408660832615414208915)
        ·
          refine ⟨3333612991248923121313373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222408660832615414208915 3333612991248923121313373)
          ·
            refine ⟨1250104871718346170492515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3333612991248923121313373 1250104871718346170492515)
            ·
              refine ⟨1875157307577519255738773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250104871718346170492515 1875157307577519255738773)
              ·
                refine ⟨87897998792696215112755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1875157307577519255738773 87897998792696215112755)
                ·
                  rfl

theorem cell21_1155470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1155470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155470 prefixEnd_1155470 := by exact prefixLift 1155470
  have htrace : WordTrace (prefixWord ++ tailWord_1155470) baseStart_1155470 baseEnd_1155470 := by
    simpa [prefixWord, tailWord_1155470, baseEnd_1155470] using wordTrace_append hprefix tailTrace_1155470
  have hstable : (prefixWord ++ tailWord_1155470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155470).length < 2 ^ (prefixWord ++ tailWord_1155470).sum := by decide
  have hdescent : baseEnd_1155470 < baseStart_1155470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155532 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_1155532 : Nat := 118140960795 + 1155532 * 2 ^ 59
def prefixEnd_1155532 : Nat := 4983230072969 + 3 ^ 40 * 1155532 * 2
def baseEnd_1155532 : Nat := 263708145622790315304805

theorem tailTrace_1155532 : CollatzResearch.WordTrace tailWord_1155532 prefixEnd_1155532 263708145622790315304805 := by
  unfold tailWord_1155532
  simp only [CollatzResearch.WordTrace]
  refine ⟨21072857224856193999470425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28097142966474925332627233 21072857224856193999470425)
  ·
    refine ⟨15804642918642145499602819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21072857224856193999470425 15804642918642145499602819)
    ·
      refine ⟨23706964377963218249404229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15804642918642145499602819 23706964377963218249404229)
      ·
        refine ⟨4445055820868103421763293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23706964377963218249404229 4445055820868103421763293)
        ·
          refine ⟨1666895932825538783161235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4445055820868103421763293 1666895932825538783161235)
          ·
            refine ⟨2500343899238308174741853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666895932825538783161235 2500343899238308174741853)
            ·
              refine ⟨937628962214365565528195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2500343899238308174741853 937628962214365565528195)
              ·
                refine ⟨1406443443321548348292293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937628962214365565528195 1406443443321548348292293)
                ·
                  refine ⟨263708145622790315304805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406443443321548348292293 263708145622790315304805)
                  ·
                    rfl

theorem cell21_1155532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_1155532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155532 prefixEnd_1155532 := by exact prefixLift 1155532
  have htrace : WordTrace (prefixWord ++ tailWord_1155532) baseStart_1155532 baseEnd_1155532 := by
    simpa [prefixWord, tailWord_1155532, baseEnd_1155532] using wordTrace_append hprefix tailTrace_1155532
  have hstable : (prefixWord ++ tailWord_1155532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155532).length < 2 ^ (prefixWord ++ tailWord_1155532).sum := by decide
  have hdescent : baseEnd_1155532 < baseStart_1155532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155574 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1155574 : Nat := 118140960795 + 1155574 * 2 ^ 59
def prefixEnd_1155574 : Nat := 4983230072969 + 3 ^ 40 * 1155574 * 2
def baseEnd_1155574 : Nat := 263717730595007575604719

theorem tailTrace_1155574 : CollatzResearch.WordTrace tailWord_1155574 prefixEnd_1155574 263717730595007575604719 := by
  unfold tailWord_1155574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634202894722514323248111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28098164210373486114646517 2634202894722514323248111)
  ·
    refine ⟨3951304342083771484872167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2634202894722514323248111 3951304342083771484872167)
    ·
      refine ⟨5926956513125657227308251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3951304342083771484872167 5926956513125657227308251)
      ·
        refine ⟨8890434769688485840962377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926956513125657227308251 8890434769688485840962377)
        ·
          refine ⟨6667826077266364380721783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8890434769688485840962377 6667826077266364380721783)
          ·
            refine ⟨10001739115899546571082675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667826077266364380721783 10001739115899546571082675)
            ·
              refine ⟨15002608673849319856624013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10001739115899546571082675 15002608673849319856624013)
              ·
                refine ⟨5625978252693494946234005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15002608673849319856624013 5625978252693494946234005)
                ·
                  refine ⟨263717730595007575604719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5625978252693494946234005 263717730595007575604719)
                  ·
                    rfl

theorem cell21_1155574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1155574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155574 prefixEnd_1155574 := by exact prefixLift 1155574
  have htrace : WordTrace (prefixWord ++ tailWord_1155574) baseStart_1155574 baseEnd_1155574 := by
    simpa [prefixWord, tailWord_1155574, baseEnd_1155574] using wordTrace_append hprefix tailTrace_1155574
  have hstable : (prefixWord ++ tailWord_1155574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155574).length < 2 ^ (prefixWord ++ tailWord_1155574).sum := by decide
  have hdescent : baseEnd_1155574 < baseStart_1155574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155591 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 4]
def baseStart_1155591 : Nat := 118140960795 + 1155591 * 2 ^ 59
def prefixEnd_1155591 : Nat := 4983230072969 + 3 ^ 40 * 1155591 * 2
def baseEnd_1155591 : Nat := 263721610226619323821351

theorem tailTrace_1155591 : CollatzResearch.WordTrace tailWord_1155591 prefixEnd_1155591 263721610226619323821351 := by
  unfold tailWord_1155591
  simp only [CollatzResearch.WordTrace]
  refine ⟨42147866356498641075338627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28098577570999094050225751 42147866356498641075338627)
  ·
    refine ⟨63221799534747961613007941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42147866356498641075338627 63221799534747961613007941)
    ·
      refine ⟨11854087412765242802438989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63221799534747961613007941 11854087412765242802438989)
      ·
        refine ⟨4445282779786966050914621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11854087412765242802438989 4445282779786966050914621)
        ·
          refine ⟨1666981042420112269092983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4445282779786966050914621 1666981042420112269092983)
          ·
            refine ⟨2500471563630168403639475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666981042420112269092983 2500471563630168403639475)
            ·
              refine ⟨3750707345445252605459213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500471563630168403639475 3750707345445252605459213)
              ·
                refine ⟨1406515254541969727047205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3750707345445252605459213 1406515254541969727047205)
                ·
                  refine ⟨263721610226619323821351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406515254541969727047205 263721610226619323821351)
                  ·
                    rfl

theorem cell21_1155591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_1155591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155591 prefixEnd_1155591 := by exact prefixLift 1155591
  have htrace : WordTrace (prefixWord ++ tailWord_1155591) baseStart_1155591 baseEnd_1155591 := by
    simpa [prefixWord, tailWord_1155591, baseEnd_1155591] using wordTrace_append hprefix tailTrace_1155591
  have hstable : (prefixWord ++ tailWord_1155591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155591).length < 2 ^ (prefixWord ++ tailWord_1155591).sum := by decide
  have hdescent : baseEnd_1155591 < baseStart_1155591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155633 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 6]
def baseStart_1155633 : Nat := 118140960795 + 1155633 * 2 ^ 59
def prefixEnd_1155633 : Nat := 4983230072969 + 3 ^ 40 * 1155633 * 2
def baseEnd_1155633 : Nat := 263731195198836584121265

theorem tailTrace_1155633 : CollatzResearch.WordTrace tailWord_1155633 prefixEnd_1155633 263731195198836584121265 := by
  unfold tailWord_1155633
  simp only [CollatzResearch.WordTrace]
  refine ⟨42149398222346482248367553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28099598814897654832245035 42149398222346482248367553)
  ·
    refine ⟨31612048666759861686275665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42149398222346482248367553 31612048666759861686275665)
    ·
      refine ⟨23709036500069896264706749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31612048666759861686275665 23709036500069896264706749)
      ·
        refine ⟨8890888687526211099265031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23709036500069896264706749 8890888687526211099265031)
        ·
          refine ⟨13336333031289316648897547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890888687526211099265031 13336333031289316648897547)
          ·
            refine ⟨20004499546933974973346321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13336333031289316648897547 20004499546933974973346321)
            ·
              refine ⟨15003374660200481230009741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20004499546933974973346321 15003374660200481230009741)
              ·
                refine ⟨5626265497575180461253653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15003374660200481230009741 5626265497575180461253653)
                ·
                  refine ⟨263731195198836584121265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5626265497575180461253653 263731195198836584121265)
                  ·
                    rfl

theorem cell21_1155633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_1155633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155633 prefixEnd_1155633 := by exact prefixLift 1155633
  have htrace : WordTrace (prefixWord ++ tailWord_1155633) baseStart_1155633 baseEnd_1155633 := by
    simpa [prefixWord, tailWord_1155633, baseEnd_1155633] using wordTrace_append hprefix tailTrace_1155633
  have hstable : (prefixWord ++ tailWord_1155633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155633).length < 2 ^ (prefixWord ++ tailWord_1155633).sum := by decide
  have hdescent : baseEnd_1155633 < baseStart_1155633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155740 : List Nat := [2, 2, 3, 2, 2, 1, 9]
def baseStart_1155740 : Nat := 118140960795 + 1155740 * 2 ^ 59
def prefixEnd_1155740 : Nat := 4983230072969 + 3 ^ 40 * 1155740 * 2
def baseEnd_1155740 : Nat := 29306179339625352870857

theorem tailTrace_1155740 : CollatzResearch.WordTrace tailWord_1155740 prefixEnd_1155740 29306179339625352870857 := by
  unfold tailWord_1155740
  simp only [CollatzResearch.WordTrace]
  refine ⟨21076650416479419761256337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28102200555305893015008449 21076650416479419761256337)
  ·
    refine ⟨15807487812359564820942253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21076650416479419761256337 15807487812359564820942253)
    ·
      refine ⟨5927807929634836807853345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15807487812359564820942253 5927807929634836807853345)
      ·
        refine ⟨4445855947226127605890009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5927807929634836807853345 4445855947226127605890009)
        ·
          refine ⟨3334391960419595704417507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4445855947226127605890009 3334391960419595704417507)
          ·
            refine ⟨5001587940629393556626261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334391960419595704417507 5001587940629393556626261)
            ·
              refine ⟨29306179339625352870857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5001587940629393556626261 29306179339625352870857)
              ·
                rfl

theorem cell21_1155740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 9].length) (baseStart_1155740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155740 prefixEnd_1155740 := by exact prefixLift 1155740
  have htrace : WordTrace (prefixWord ++ tailWord_1155740) baseStart_1155740 baseEnd_1155740 := by
    simpa [prefixWord, tailWord_1155740, baseEnd_1155740] using wordTrace_append hprefix tailTrace_1155740
  have hstable : (prefixWord ++ tailWord_1155740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155740).length < 2 ^ (prefixWord ++ tailWord_1155740).sum := by decide
  have hdescent : baseEnd_1155740 < baseStart_1155740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155757 : List Nat := [1, 5, 2, 1, 1, 3, 2, 6]
def baseStart_1155757 : Nat := 118140960795 + 1155757 * 2 ^ 59
def prefixEnd_1155757 : Nat := 4983230072969 + 3 ^ 40 * 1155757 * 2
def baseEnd_1155757 : Nat := 87919831229413308018115

theorem tailTrace_1155757 : CollatzResearch.WordTrace tailWord_1155757 prefixEnd_1155757 87919831229413308018115 := by
  unfold tailWord_1155757
  simp only [CollatzResearch.WordTrace]
  refine ⟨42153920873897251425881525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28102613915931500950587683 42153920873897251425881525)
  ·
    refine ⟨3951930081927867321176393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42153920873897251425881525 3951930081927867321176393)
    ·
      refine ⟨2963947561445900490882295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3951930081927867321176393 2963947561445900490882295)
      ·
        refine ⟨4445921342168850736323443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963947561445900490882295 4445921342168850736323443)
        ·
          refine ⟨6668882013253276104485165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445921342168850736323443 6668882013253276104485165)
          ·
            refine ⟨2500830754969978539181937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6668882013253276104485165 2500830754969978539181937)
            ·
              refine ⟨1875623066227483904386453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2500830754969978539181937 1875623066227483904386453)
              ·
                refine ⟨87919831229413308018115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1875623066227483904386453 87919831229413308018115)
                ·
                  rfl

theorem cell21_1155757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 6].length) (baseStart_1155757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155757 prefixEnd_1155757 := by exact prefixLift 1155757
  have htrace : WordTrace (prefixWord ++ tailWord_1155757) baseStart_1155757 baseEnd_1155757 := by
    simpa [prefixWord, tailWord_1155757, baseEnd_1155757] using wordTrace_append hprefix tailTrace_1155757
  have hstable : (prefixWord ++ tailWord_1155757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155757).length < 2 ^ (prefixWord ++ tailWord_1155757).sum := by decide
  have hdescent : baseEnd_1155757 < baseStart_1155757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155799 : List Nat := [1, 1, 3, 2, 1, 13]
def baseStart_1155799 : Nat := 118140960795 + 1155799 * 2 ^ 59
def prefixEnd_1155799 : Nat := 4983230072969 + 3 ^ 40 * 1155799 * 2
def baseEnd_1155799 : Nat := 9769225135572488309417

theorem tailTrace_1155799 : CollatzResearch.WordTrace tailWord_1155799 prefixEnd_1155799 9769225135572488309417 := by
  unfold tailWord_1155799
  simp only [CollatzResearch.WordTrace]
  refine ⟨42155452739745092598910451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28103635159830061732606967 42155452739745092598910451)
  ·
    refine ⟨63233179109617638898365677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42155452739745092598910451 63233179109617638898365677)
    ·
      refine ⟨23712442166106614586887129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63233179109617638898365677 23712442166106614586887129)
      ·
        refine ⟨17784331624579960940165347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23712442166106614586887129 17784331624579960940165347)
        ·
          refine ⟨26676497436869941410248021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17784331624579960940165347 26676497436869941410248021)
          ·
            refine ⟨9769225135572488309417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 26676497436869941410248021 9769225135572488309417)
            ·
              rfl

theorem cell21_1155799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 13].length) (baseStart_1155799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155799 prefixEnd_1155799 := by exact prefixLift 1155799
  have htrace : WordTrace (prefixWord ++ tailWord_1155799) baseStart_1155799 baseEnd_1155799 := by
    simpa [prefixWord, tailWord_1155799, baseEnd_1155799] using wordTrace_append hprefix tailTrace_1155799
  have hstable : (prefixWord ++ tailWord_1155799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155799).length < 2 ^ (prefixWord ++ tailWord_1155799).sum := by decide
  have hdescent : baseEnd_1155799 < baseStart_1155799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155802 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1155802 : Nat := 118140960795 + 1155802 * 2 ^ 59
def prefixEnd_1155802 : Nat := 4983230072969 + 3 ^ 40 * 1155802 * 2
def baseEnd_1155802 : Nat := 263769763301329845804253

theorem tailTrace_1155802 : CollatzResearch.WordTrace tailWord_1155802 prefixEnd_1155802 263769763301329845804253 := by
  unfold tailWord_1155802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538890539683556027817415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28103708105822816074179773 10538890539683556027817415)
  ·
    refine ⟨15808335809525334041726123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10538890539683556027817415 15808335809525334041726123)
    ·
      refine ⟨23712503714288001062589185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15808335809525334041726123 23712503714288001062589185)
      ·
        refine ⟨17784377785716000796941889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23712503714288001062589185 17784377785716000796941889)
        ·
          refine ⟨13338283339287000597706417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17784377785716000796941889 13338283339287000597706417)
          ·
            refine ⟨10003712504465250448279813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13338283339287000597706417 10003712504465250448279813)
            ·
              refine ⟨1875696094587234459052465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10003712504465250448279813 1875696094587234459052465)
              ·
                refine ⟨1406772070940425844289349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875696094587234459052465 1406772070940425844289349)
                ·
                  refine ⟨263769763301329845804253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406772070940425844289349 263769763301329845804253)
                  ·
                    rfl

theorem cell21_1155802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1155802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155802 prefixEnd_1155802 := by exact prefixLift 1155802
  have htrace : WordTrace (prefixWord ++ tailWord_1155802) baseStart_1155802 baseEnd_1155802 := by
    simpa [prefixWord, tailWord_1155802, baseEnd_1155802] using wordTrace_append hprefix tailTrace_1155802
  have hstable : (prefixWord ++ tailWord_1155802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155802).length < 2 ^ (prefixWord ++ tailWord_1155802).sum := by decide
  have hdescent : baseEnd_1155802 < baseStart_1155802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155861 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1155861 : Nat := 118140960795 + 1155861 * 2 ^ 59
def prefixEnd_1155861 : Nat := 4983230072969 + 3 ^ 40 * 1155861 * 2
def baseEnd_1155861 : Nat := 263783227905158854320799

theorem tailTrace_1155861 : CollatzResearch.WordTrace tailWord_1155861 prefixEnd_1155861 263783227905158854320799 := by
  unfold tailWord_1155861
  simp only [CollatzResearch.WordTrace]
  refine ⟨42157714065520477187667437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28105142710346984791778291 42157714065520477187667437)
  ·
    refine ⟨15809142774570178945375289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42157714065520477187667437 15809142774570178945375289)
    ·
      refine ⟨11856857080927634209031467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15809142774570178945375289 11856857080927634209031467)
      ·
        refine ⟨17785285621391451313547201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11856857080927634209031467 17785285621391451313547201)
        ·
          refine ⟨13338964216043588485160401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17785285621391451313547201 13338964216043588485160401)
          ·
            refine ⟨10004223162032691363870301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13338964216043588485160401 10004223162032691363870301)
            ·
              refine ⟨3751583685762259261451363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10004223162032691363870301 3751583685762259261451363)
              ·
                refine ⟨5627375528643388892177045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751583685762259261451363 5627375528643388892177045)
                ·
                  refine ⟨263783227905158854320799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5627375528643388892177045 263783227905158854320799)
                  ·
                    rfl

theorem cell21_1155861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1155861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155861 prefixEnd_1155861 := by exact prefixLift 1155861
  have htrace : WordTrace (prefixWord ++ tailWord_1155861) baseStart_1155861 baseEnd_1155861 := by
    simpa [prefixWord, tailWord_1155861, baseEnd_1155861] using wordTrace_append hprefix tailTrace_1155861
  have hstable : (prefixWord ++ tailWord_1155861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155861).length < 2 ^ (prefixWord ++ tailWord_1155861).sum := by decide
  have hdescent : baseEnd_1155861 < baseStart_1155861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155875 : List Nat := [1, 1, 1, 4, 2, 1, 1, 10]
def baseStart_1155875 : Nat := 118140960795 + 1155875 * 2 ^ 59
def prefixEnd_1155875 : Nat := 4983230072969 + 3 ^ 40 * 1155875 * 2
def baseEnd_1155875 : Nat := 87928807631965980362479

theorem tailTrace_1155875 : CollatzResearch.WordTrace tailWord_1155875 prefixEnd_1155875 87928807631965980362479 := by
  unfold tailWord_1155875
  simp only [CollatzResearch.WordTrace]
  refine ⟨42158224687469757578677079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28105483124979838385784719 42158224687469757578677079)
  ·
    refine ⟨63237337031204636368015619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42158224687469757578677079 63237337031204636368015619)
    ·
      refine ⟨94856005546806954552023429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63237337031204636368015619 94856005546806954552023429)
      ·
        refine ⟨17785501040026303978504393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94856005546806954552023429 17785501040026303978504393)
        ·
          refine ⟨13339125780019727983878295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17785501040026303978504393 13339125780019727983878295)
          ·
            refine ⟨20008688670029591975817443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13339125780019727983878295 20008688670029591975817443)
            ·
              refine ⟨30013033005044387963726165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20008688670029591975817443 30013033005044387963726165)
              ·
                refine ⟨87928807631965980362479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30013033005044387963726165 87928807631965980362479)
                ·
                  rfl

theorem cell21_1155875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_1155875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155875 prefixEnd_1155875 := by exact prefixLift 1155875
  have htrace : WordTrace (prefixWord ++ tailWord_1155875) baseStart_1155875 baseEnd_1155875 := by
    simpa [prefixWord, tailWord_1155875, baseEnd_1155875] using wordTrace_append hprefix tailTrace_1155875
  have hstable : (prefixWord ++ tailWord_1155875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155875).length < 2 ^ (prefixWord ++ tailWord_1155875).sum := by decide
  have hdescent : baseEnd_1155875 < baseStart_1155875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155898 : List Nat := [3, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_1155898 : Nat := 118140960795 + 1155898 * 2 ^ 59
def prefixEnd_1155898 : Nat := 4983230072969 + 3 ^ 40 * 1155898 * 2
def baseEnd_1155898 : Nat := 263791671809255012204057

theorem tailTrace_1155898 : CollatzResearch.WordTrace tailWord_1155898 prefixEnd_1155898 263791671809255012204057 := by
  unfold tailWord_1155898
  simp only [CollatzResearch.WordTrace]
  refine ⟨10539765891596608126691087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28106042377590955004509565 10539765891596608126691087)
  ·
    refine ⟨15809648837394912190036631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10539765891596608126691087 15809648837394912190036631)
    ·
      refine ⟨23714473256092368285054947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15809648837394912190036631 23714473256092368285054947)
      ·
        refine ⟨35571709884138552427582421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23714473256092368285054947 35571709884138552427582421)
        ·
          refine ⟨833711950409497322521463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35571709884138552427582421 833711950409497322521463)
          ·
            refine ⟨1250567925614245983782195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833711950409497322521463 1250567925614245983782195)
            ·
              refine ⟨1875851888421368975673293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250567925614245983782195 1875851888421368975673293)
              ·
                refine ⟨703444458158013365877485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1875851888421368975673293 703444458158013365877485)
                ·
                  refine ⟨263791671809255012204057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703444458158013365877485 263791671809255012204057)
                  ·
                    rfl

theorem cell21_1155898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_1155898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155898 prefixEnd_1155898 := by exact prefixLift 1155898
  have htrace : WordTrace (prefixWord ++ tailWord_1155898) baseStart_1155898 baseEnd_1155898 := by
    simpa [prefixWord, tailWord_1155898, baseEnd_1155898] using wordTrace_append hprefix tailTrace_1155898
  have hstable : (prefixWord ++ tailWord_1155898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155898).length < 2 ^ (prefixWord ++ tailWord_1155898).sum := by decide
  have hdescent : baseEnd_1155898 < baseStart_1155898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155923 : List Nat := [1, 1, 1, 2, 1, 1, 3, 8, 3]
def baseStart_1155923 : Nat := 118140960795 + 1155923 * 2 ^ 59
def prefixEnd_1155923 : Nat := 4983230072969 + 3 ^ 40 * 1155923 * 2
def baseEnd_1155923 : Nat := 263797377149860524287339

theorem tailTrace_1155923 : CollatzResearch.WordTrace tailWord_1155923 prefixEnd_1155923 263797377149860524287339 := by
  unfold tailWord_1155923
  simp only [CollatzResearch.WordTrace]
  refine ⟨42159975391295861776424423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28106650260863907850949615 42159975391295861776424423)
  ·
    refine ⟨63239963086943792664636635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42159975391295861776424423 63239963086943792664636635)
    ·
      refine ⟨94859944630415688996954953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63239963086943792664636635 94859944630415688996954953)
      ·
        refine ⟨71144958472811766747716215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94859944630415688996954953 71144958472811766747716215)
        ·
          refine ⟨106717437709217650121574323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71144958472811766747716215 106717437709217650121574323)
          ·
            refine ⟨160076156563826475182361485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106717437709217650121574323 160076156563826475182361485)
            ·
              refine ⟨60028558711434928193385557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160076156563826475182361485 60028558711434928193385557)
              ·
                refine ⟨703459672399628064766237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 60028558711434928193385557 703459672399628064766237)
                ·
                  refine ⟨263797377149860524287339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703459672399628064766237 263797377149860524287339)
                  ·
                    rfl

theorem cell21_1155923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 3].length) (baseStart_1155923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155923 prefixEnd_1155923 := by exact prefixLift 1155923
  have htrace : WordTrace (prefixWord ++ tailWord_1155923) baseStart_1155923 baseEnd_1155923 := by
    simpa [prefixWord, tailWord_1155923, baseEnd_1155923] using wordTrace_append hprefix tailTrace_1155923
  have hstable : (prefixWord ++ tailWord_1155923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155923).length < 2 ^ (prefixWord ++ tailWord_1155923).sum := by decide
  have hdescent : baseEnd_1155923 < baseStart_1155923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155999 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 5]
def baseStart_1155999 : Nat := 118140960795 + 1155999 * 2 ^ 59
def prefixEnd_1155999 : Nat := 4983230072969 + 3 ^ 40 * 1155999 * 2
def baseEnd_1155999 : Nat := 263814721385301281020517

theorem tailTrace_1155999 : CollatzResearch.WordTrace tailWord_1155999 prefixEnd_1155999 263814721385301281020517 := by
  unfold tailWord_1155999
  simp only [CollatzResearch.WordTrace]
  refine ⟨42162747339020526756191051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28108498226013684504127367 42162747339020526756191051)
  ·
    refine ⟨63244121008530790134286577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42162747339020526756191051 63244121008530790134286577)
    ·
      refine ⟨47433090756398092600714933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63244121008530790134286577 47433090756398092600714933)
      ·
        refine ⟨4446852258412321181317025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47433090756398092600714933 4446852258412321181317025)
        ·
          refine ⟨3335139193809240885987769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4446852258412321181317025 3335139193809240885987769)
          ·
            refine ⟨2501354395356930664490827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3335139193809240885987769 2501354395356930664490827)
            ·
              refine ⟨3752031593035395996736241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501354395356930664490827 3752031593035395996736241)
              ·
                refine ⟨2814023694776546997552181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3752031593035395996736241 2814023694776546997552181)
                ·
                  refine ⟨263814721385301281020517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2814023694776546997552181 263814721385301281020517)
                  ·
                    rfl

theorem cell21_1155999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_1155999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1155999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1155999 prefixEnd_1155999 := by exact prefixLift 1155999
  have htrace : WordTrace (prefixWord ++ tailWord_1155999) baseStart_1155999 baseEnd_1155999 := by
    simpa [prefixWord, tailWord_1155999, baseEnd_1155999] using wordTrace_append hprefix tailTrace_1155999
  have hstable : (prefixWord ++ tailWord_1155999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155999).length < 2 ^ (prefixWord ++ tailWord_1155999).sum := by decide
  have hdescent : baseEnd_1155999 < baseStart_1155999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156022 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1156022 : Nat := 118140960795 + 1156022 * 2 ^ 59
def prefixEnd_1156022 : Nat := 4983230072969 + 3 ^ 40 * 1156022 * 2
def baseEnd_1156022 : Nat := 263819970298658352137137

theorem tailTrace_1156022 : CollatzResearch.WordTrace tailWord_1156022 prefixEnd_1156022 263819970298658352137137 := by
  unfold tailWord_1156022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635224138621075105267395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28109057478624801122852213 2635224138621075105267395)
  ·
    refine ⟨3952836207931612657901093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635224138621075105267395 3952836207931612657901093)
    ·
      refine ⟨741156788987177373356455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3952836207931612657901093 741156788987177373356455)
      ·
        refine ⟨1111735183480766060034683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741156788987177373356455 1111735183480766060034683)
        ·
          refine ⟨1667602775221149090052025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111735183480766060034683 1667602775221149090052025)
          ·
            refine ⟨1250702081415861817539019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667602775221149090052025 1250702081415861817539019)
            ·
              refine ⟨1876053122123792726308529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250702081415861817539019 1876053122123792726308529)
              ·
                refine ⟨1407039841592844544731397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1876053122123792726308529 1407039841592844544731397)
                ·
                  refine ⟨263819970298658352137137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407039841592844544731397 263819970298658352137137)
                  ·
                    rfl

theorem cell21_1156022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1156022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156022 prefixEnd_1156022 := by exact prefixLift 1156022
  have htrace : WordTrace (prefixWord ++ tailWord_1156022) baseStart_1156022 baseEnd_1156022 := by
    simpa [prefixWord, tailWord_1156022, baseEnd_1156022] using wordTrace_append hprefix tailTrace_1156022
  have hstable : (prefixWord ++ tailWord_1156022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156022).length < 2 ^ (prefixWord ++ tailWord_1156022).sum := by decide
  have hdescent : baseEnd_1156022 < baseStart_1156022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156061 : List Nat := [1, 4, 3, 1, 2, 1, 4, 5]
def baseStart_1156061 : Nat := 118140960795 + 1156061 * 2 ^ 59
def prefixEnd_1156061 : Nat := 4983230072969 + 3 ^ 40 * 1156061 * 2
def baseEnd_1156061 : Nat := 87942956876667650329019

theorem tailTrace_1156061 : CollatzResearch.WordTrace tailWord_1156061 prefixEnd_1156061 87942956876667650329019 := by
  unfold tailWord_1156061
  simp only [CollatzResearch.WordTrace]
  refine ⟨42165008664795911344948037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28110005776530607563298691 42165008664795911344948037)
  ·
    refine ⟨7905939124649233377177757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42165008664795911344948037 7905939124649233377177757)
    ·
      refine ⟨2964727171743462516441659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7905939124649233377177757 2964727171743462516441659)
      ·
        refine ⟨4447090757615193774662489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964727171743462516441659 4447090757615193774662489)
        ·
          refine ⟨3335318068211395330996867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4447090757615193774662489 3335318068211395330996867)
          ·
            refine ⟨5002977102317092996495301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335318068211395330996867 5002977102317092996495301)
            ·
              refine ⟨938058206684454936842869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5002977102317092996495301 938058206684454936842869)
              ·
                refine ⟨87942956876667650329019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 938058206684454936842869 87942956876667650329019)
                ·
                  rfl

theorem cell21_1156061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 5].length) (baseStart_1156061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156061 prefixEnd_1156061 := by exact prefixLift 1156061
  have htrace : WordTrace (prefixWord ++ tailWord_1156061) baseStart_1156061 baseEnd_1156061 := by
    simpa [prefixWord, tailWord_1156061, baseEnd_1156061] using wordTrace_append hprefix tailTrace_1156061
  have hstable : (prefixWord ++ tailWord_1156061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156061).length < 2 ^ (prefixWord ++ tailWord_1156061).sum := by decide
  have hdescent : baseEnd_1156061 < baseStart_1156061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156084 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1156084 : Nat := 118140960795 + 1156084 * 2 ^ 59
def prefixEnd_1156084 : Nat := 4983230072969 + 3 ^ 40 * 1156084 * 2
def baseEnd_1156084 : Nat := 263834119543360022103677

theorem tailTrace_1156084 : CollatzResearch.WordTrace tailWord_1156084 prefixEnd_1156084 263834119543360022103677 := by
  unfold tailWord_1156084
  simp only [CollatzResearch.WordTrace]
  refine ⟨21082923771856293136517653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28110565029141724182023537 21082923771856293136517653)
  ·
    refine ⟨988262051805763740774265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21082923771856293136517653 988262051805763740774265)
    ·
      refine ⟨741196538854322805580699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 988262051805763740774265 741196538854322805580699)
      ·
        refine ⟨1111794808281484208371049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741196538854322805580699 1111794808281484208371049)
        ·
          refine ⟨833846106211113156278287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111794808281484208371049 833846106211113156278287)
          ·
            refine ⟨1250769159316669734417431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833846106211113156278287 1250769159316669734417431)
            ·
              refine ⟨1876153738975004601626147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250769159316669734417431 1876153738975004601626147)
              ·
                refine ⟨2814230608462506902439221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876153738975004601626147 2814230608462506902439221)
                ·
                  refine ⟨263834119543360022103677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2814230608462506902439221 263834119543360022103677)
                  ·
                    rfl

theorem cell21_1156084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1156084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156084 prefixEnd_1156084 := by exact prefixLift 1156084
  have htrace : WordTrace (prefixWord ++ tailWord_1156084) baseStart_1156084 baseEnd_1156084 := by
    simpa [prefixWord, tailWord_1156084, baseEnd_1156084] using wordTrace_append hprefix tailTrace_1156084
  have hstable : (prefixWord ++ tailWord_1156084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156084).length < 2 ^ (prefixWord ++ tailWord_1156084).sum := by decide
  have hdescent : baseEnd_1156084 < baseStart_1156084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156089 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 4]
def baseStart_1156089 : Nat := 118140960795 + 1156089 * 2 ^ 59
def prefixEnd_1156089 : Nat := 4983230072969 + 3 ^ 40 * 1156089 * 2
def baseEnd_1156089 : Nat := 263835260611481124520333

theorem tailTrace_1156089 : CollatzResearch.WordTrace tailWord_1156089 prefixEnd_1156089 263835260611481124520333 := by
  unfold tailWord_1156089
  simp only [CollatzResearch.WordTrace]
  refine ⟨42166029908694472126967321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28110686605796314751311547 42166029908694472126967321)
  ·
    refine ⟨31624522431520854095225491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42166029908694472126967321 31624522431520854095225491)
    ·
      refine ⟨47436783647281281142838237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31624522431520854095225491 47436783647281281142838237)
      ·
        refine ⟨17788793867730480428564339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47436783647281281142838237 17788793867730480428564339)
        ·
          refine ⟨26683190801595720642846509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17788793867730480428564339 26683190801595720642846509)
          ·
            refine ⟨10006196550598395241067441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26683190801595720642846509 10006196550598395241067441)
            ·
              refine ⟨7504647412948796430800581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10006196550598395241067441 7504647412948796430800581)
              ·
                refine ⟨1407121389927899330775109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7504647412948796430800581 1407121389927899330775109)
                ·
                  refine ⟨263835260611481124520333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407121389927899330775109 263835260611481124520333)
                  ·
                    rfl

theorem cell21_1156089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_1156089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156089 prefixEnd_1156089 := by exact prefixLift 1156089
  have htrace : WordTrace (prefixWord ++ tailWord_1156089) baseStart_1156089 baseEnd_1156089 := by
    simpa [prefixWord, tailWord_1156089, baseEnd_1156089] using wordTrace_append hprefix tailTrace_1156089
  have hstable : (prefixWord ++ tailWord_1156089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156089).length < 2 ^ (prefixWord ++ tailWord_1156089).sum := by decide
  have hdescent : baseEnd_1156089 < baseStart_1156089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156098 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1156098 : Nat := 118140960795 + 1156098 * 2 ^ 59
def prefixEnd_1156098 : Nat := 4983230072969 + 3 ^ 40 * 1156098 * 2
def baseEnd_1156098 : Nat := 263837314534099108870315

theorem tailTrace_1156098 : CollatzResearch.WordTrace tailWord_1156098 prefixEnd_1156098 263837314534099108870315 := by
  unfold tailWord_1156098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10541589541415466666011237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28110905443774577776029965 10541589541415466666011237)
  ·
    refine ⟨1976548039015399999877107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10541589541415466666011237 1976548039015399999877107)
    ·
      refine ⟨2964822058523099999815661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976548039015399999877107 2964822058523099999815661)
      ·
        refine ⟨1111808271946162499930873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2964822058523099999815661 1111808271946162499930873)
        ·
          refine ⟨833856203959621874948155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111808271946162499930873 833856203959621874948155)
          ·
            refine ⟨1250784305939432812422233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833856203959621874948155 1250784305939432812422233)
            ·
              refine ⟨938088229454574609316675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250784305939432812422233 938088229454574609316675)
              ·
                refine ⟨1407132344181861913975013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938088229454574609316675 1407132344181861913975013)
                ·
                  refine ⟨263837314534099108870315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407132344181861913975013 263837314534099108870315)
                  ·
                    rfl

theorem cell21_1156098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1156098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156098 prefixEnd_1156098 := by exact prefixLift 1156098
  have htrace : WordTrace (prefixWord ++ tailWord_1156098) baseStart_1156098 baseEnd_1156098 := by
    simpa [prefixWord, tailWord_1156098, baseEnd_1156098] using wordTrace_append hprefix tailTrace_1156098
  have hstable : (prefixWord ++ tailWord_1156098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156098).length < 2 ^ (prefixWord ++ tailWord_1156098).sum := by decide
  have hdescent : baseEnd_1156098 < baseStart_1156098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156106 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_1156106 : Nat := 118140960795 + 1156106 * 2 ^ 59
def prefixEnd_1156106 : Nat := 4983230072969 + 3 ^ 40 * 1156106 * 2
def baseEnd_1156106 : Nat := 263839140243092872736965

theorem tailTrace_1156106 : CollatzResearch.WordTrace tailWord_1156106 prefixEnd_1156106 263839140243092872736965 := by
  unfold tailWord_1156106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10541662487408221007584043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28111099966421922686890781 10541662487408221007584043)
  ·
    refine ⟨15812493731112331511376065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10541662487408221007584043 15812493731112331511376065)
    ·
      refine ⟨11859370298334248633532049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15812493731112331511376065 11859370298334248633532049)
      ·
        refine ⟨8894527723750686475149037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11859370298334248633532049 8894527723750686475149037)
        ·
          refine ⟨3335447896406507428180889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8894527723750686475149037 3335447896406507428180889)
          ·
            refine ⟨2501585922304880571135667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3335447896406507428180889 2501585922304880571135667)
            ·
              refine ⟨3752378883457320856703501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501585922304880571135667 3752378883457320856703501)
              ·
                refine ⟨1407142081296495321263813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3752378883457320856703501 1407142081296495321263813)
                ·
                  refine ⟨263839140243092872736965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407142081296495321263813 263839140243092872736965)
                  ·
                    rfl

theorem cell21_1156106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_1156106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156106 prefixEnd_1156106 := by exact prefixLift 1156106
  have htrace : WordTrace (prefixWord ++ tailWord_1156106) baseStart_1156106 baseEnd_1156106 := by
    simpa [prefixWord, tailWord_1156106, baseEnd_1156106] using wordTrace_append hprefix tailTrace_1156106
  have hstable : (prefixWord ++ tailWord_1156106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156106).length < 2 ^ (prefixWord ++ tailWord_1156106).sum := by decide
  have hdescent : baseEnd_1156106 < baseStart_1156106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156165 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 4]
def baseStart_1156165 : Nat := 118140960795 + 1156165 * 2 ^ 59
def prefixEnd_1156165 : Nat := 4983230072969 + 3 ^ 40 * 1156165 * 2
def baseEnd_1156165 : Nat := 263852604846921881253511

theorem tailTrace_1156165 : CollatzResearch.WordTrace tailWord_1156165 prefixEnd_1156165 263852604846921881253511 := by
  unfold tailWord_1156165
  simp only [CollatzResearch.WordTrace]
  refine ⟨42168801856419137106733949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28112534570946091404489299 42168801856419137106733949)
  ·
    refine ⟨15813300696157176415025231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42168801856419137106733949 15813300696157176415025231)
    ·
      refine ⟨23719951044235764622537847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15813300696157176415025231 23719951044235764622537847)
      ·
        refine ⟨35579926566353646933806771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23719951044235764622537847 35579926566353646933806771)
        ·
          refine ⟨53369889849530470400710157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35579926566353646933806771 53369889849530470400710157)
          ·
            refine ⟨20013708693573926400266309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53369889849530470400710157 20013708693573926400266309)
            ·
              refine ⟨3752570380045111200049933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20013708693573926400266309 3752570380045111200049933)
              ·
                refine ⟨1407213892516916700018725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3752570380045111200049933 1407213892516916700018725)
                ·
                  refine ⟨263852604846921881253511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407213892516916700018725 263852604846921881253511)
                  ·
                    rfl

theorem cell21_1156165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_1156165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156165 prefixEnd_1156165 := by exact prefixLift 1156165
  have htrace : WordTrace (prefixWord ++ tailWord_1156165) baseStart_1156165 baseEnd_1156165 := by
    simpa [prefixWord, tailWord_1156165, baseEnd_1156165] using wordTrace_append hprefix tailTrace_1156165
  have hstable : (prefixWord ++ tailWord_1156165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156165).length < 2 ^ (prefixWord ++ tailWord_1156165).sum := by decide
  have hdescent : baseEnd_1156165 < baseStart_1156165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156320 : List Nat := [2, 1, 1, 3, 1, 4, 4, 2, 3]
def baseStart_1156320 : Nat := 118140960795 + 1156320 * 2 ^ 59
def prefixEnd_1156320 : Nat := 4983230072969 + 3 ^ 40 * 1156320 * 2
def baseEnd_1156320 : Nat := 263887977958676056169861

theorem tailTrace_1156320 : CollatzResearch.WordTrace tailWord_1156320 prefixEnd_1156320 263887977958676056169861 := by
  unfold tailWord_1156320
  simp only [CollatzResearch.WordTrace]
  refine ⟨21087227585428799289313207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28116303447238399052417609 21087227585428799289313207)
  ·
    refine ⟨31630841378143198933969811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21087227585428799289313207 31630841378143198933969811)
    ·
      refine ⟨47446262067214798400954717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31630841378143198933969811 47446262067214798400954717)
      ·
        refine ⟨17792348275205549400358019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47446262067214798400954717 17792348275205549400358019)
        ·
          refine ⟨26688522412808324100537029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17792348275205549400358019 26688522412808324100537029)
          ·
            refine ⟨5004097952401560768850693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26688522412808324100537029 5004097952401560768850693)
            ·
              refine ⟨938268366075292644159505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5004097952401560768850693 938268366075292644159505)
              ·
                refine ⟨703701274556469483119629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938268366075292644159505 703701274556469483119629)
                ·
                  refine ⟨263887977958676056169861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703701274556469483119629 263887977958676056169861)
                  ·
                    rfl

theorem cell21_1156320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_1156320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156320 prefixEnd_1156320 := by exact prefixLift 1156320
  have htrace : WordTrace (prefixWord ++ tailWord_1156320) baseStart_1156320 baseEnd_1156320 := by
    simpa [prefixWord, tailWord_1156320, baseEnd_1156320] using wordTrace_append hprefix tailTrace_1156320
  have hstable : (prefixWord ++ tailWord_1156320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156320).length < 2 ^ (prefixWord ++ tailWord_1156320).sum := by decide
  have hdescent : baseEnd_1156320 < baseStart_1156320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156331 : List Nat := [1, 1, 1, 1, 2, 6, 3, 6]
def baseStart_1156331 : Nat := 118140960795 + 1156331 * 2 ^ 59
def prefixEnd_1156331 : Nat := 4983230072969 + 3 ^ 40 * 1156331 * 2
def baseEnd_1156331 : Nat := 87963496102847493828835

theorem tailTrace_1156331 : CollatzResearch.WordTrace tailWord_1156331 prefixEnd_1156331 87963496102847493828835 := by
  unfold tailWord_1156331
  simp only [CollatzResearch.WordTrace]
  refine ⟨42174856373817747457276847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28116570915878498304851231 42174856373817747457276847)
  ·
    refine ⟨63262284560726621185915271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42174856373817747457276847 63262284560726621185915271)
    ·
      refine ⟨94893426841089931778872907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63262284560726621185915271 94893426841089931778872907)
      ·
        refine ⟨142340140261634897668309361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94893426841089931778872907 142340140261634897668309361)
        ·
          refine ⟨106755105196226173251232021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142340140261634897668309361 106755105196226173251232021)
          ·
            refine ⟨5004145556073101871151501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106755105196226173251232021 5004145556073101871151501)
            ·
              refine ⟨1876554583527413201681813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5004145556073101871151501 1876554583527413201681813)
              ·
                refine ⟨87963496102847493828835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1876554583527413201681813 87963496102847493828835)
                ·
                  rfl

theorem cell21_1156331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 6].length) (baseStart_1156331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156331 prefixEnd_1156331 := by exact prefixLift 1156331
  have htrace : WordTrace (prefixWord ++ tailWord_1156331) baseStart_1156331 baseEnd_1156331 := by
    simpa [prefixWord, tailWord_1156331, baseEnd_1156331] using wordTrace_append hprefix tailTrace_1156331
  have hstable : (prefixWord ++ tailWord_1156331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156331).length < 2 ^ (prefixWord ++ tailWord_1156331).sum := by decide
  have hdescent : baseEnd_1156331 < baseStart_1156331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156421 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 7]
def baseStart_1156421 : Nat := 118140960795 + 1156421 * 2 ^ 59
def prefixEnd_1156421 : Nat := 4983230072969 + 3 ^ 40 * 1156421 * 2
def baseEnd_1156421 : Nat := 263911027534722324986321

theorem tailTrace_1156421 : CollatzResearch.WordTrace tailWord_1156421 prefixEnd_1156421 263911027534722324986321 := by
  unfold tailWord_1156421
  simp only [CollatzResearch.WordTrace]
  refine ⟨42178138943491692828053117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28118759295661128552035411 42178138943491692828053117)
  ·
    refine ⟨15816802103809384810519919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42178138943491692828053117 15816802103809384810519919)
    ·
      refine ⟨23725203155714077215779879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15816802103809384810519919 23725203155714077215779879)
      ·
        refine ⟨35587804733571115823669819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23725203155714077215779879 35587804733571115823669819)
        ·
          refine ⟨53381707100356673735504729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35587804733571115823669819 53381707100356673735504729)
          ·
            refine ⟨40036280325267505301628547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53381707100356673735504729 40036280325267505301628547)
            ·
              refine ⟨60054420487901257952442821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40036280325267505301628547 60054420487901257952442821)
              ·
                refine ⟨11260203841481485866083029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60054420487901257952442821 11260203841481485866083029)
                ·
                  refine ⟨263911027534722324986321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11260203841481485866083029 263911027534722324986321)
                  ·
                    rfl

theorem cell21_1156421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_1156421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156421 prefixEnd_1156421 := by exact prefixLift 1156421
  have htrace : WordTrace (prefixWord ++ tailWord_1156421) baseStart_1156421 baseEnd_1156421 := by
    simpa [prefixWord, tailWord_1156421, baseEnd_1156421] using wordTrace_append hprefix tailTrace_1156421
  have hstable : (prefixWord ++ tailWord_1156421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156421).length < 2 ^ (prefixWord ++ tailWord_1156421).sum := by decide
  have hdescent : baseEnd_1156421 < baseStart_1156421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156489 : List Nat := [1, 2, 1, 1, 7, 2, 2, 2, 3]
def baseStart_1156489 : Nat := 118140960795 + 1156489 * 2 ^ 59
def prefixEnd_1156489 : Nat := 4983230072969 + 3 ^ 40 * 1156489 * 2
def baseEnd_1156489 : Nat := 263926546061169317852849

theorem tailTrace_1156489 : CollatzResearch.WordTrace tailWord_1156489 prefixEnd_1156489 263926546061169317852849 := by
  unfold tailWord_1156489
  simp only [CollatzResearch.WordTrace]
  refine ⟨42180619107245340441528521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28120412738163560294352347 42180619107245340441528521)
  ·
    refine ⟨31635464330434005331146391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42180619107245340441528521 31635464330434005331146391)
    ·
      refine ⟨47453196495651007996719587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31635464330434005331146391 47453196495651007996719587)
      ·
        refine ⟨71179794743476511995079381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47453196495651007996719587 71179794743476511995079381)
        ·
          refine ⟨1668276439300230749884673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 71179794743476511995079381 1668276439300230749884673)
          ·
            refine ⟨1251207329475173062413505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1668276439300230749884673 1251207329475173062413505)
            ·
              refine ⟨938405497106379796810129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251207329475173062413505 938405497106379796810129)
              ·
                refine ⟨703804122829784847607597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938405497106379796810129 703804122829784847607597)
                ·
                  refine ⟨263926546061169317852849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703804122829784847607597 263926546061169317852849)
                  ·
                    rfl

theorem cell21_1156489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_1156489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156489 prefixEnd_1156489 := by exact prefixLift 1156489
  have htrace : WordTrace (prefixWord ++ tailWord_1156489) baseStart_1156489 baseEnd_1156489 := by
    simpa [prefixWord, tailWord_1156489, baseEnd_1156489] using wordTrace_append hprefix tailTrace_1156489
  have hstable : (prefixWord ++ tailWord_1156489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156489).length < 2 ^ (prefixWord ++ tailWord_1156489).sum := by decide
  have hdescent : baseEnd_1156489 < baseStart_1156489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156500 : List Nat := [2, 4, 2, 1, 2, 1, 3, 6]
def baseStart_1156500 : Nat := 118140960795 + 1156500 * 2 ^ 59
def prefixEnd_1156500 : Nat := 4983230072969 + 3 ^ 40 * 1156500 * 2
def baseEnd_1156500 : Nat := 87976352137011914389831

theorem tailTrace_1156500 : CollatzResearch.WordTrace tailWord_1156500 prefixEnd_1156500 87976352137011914389831 := by
  unfold tailWord_1156500
  simp only [CollatzResearch.WordTrace]
  refine ⟨21090510155102744660089477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28120680206803659546785969 21090510155102744660089477)
  ·
    refine ⟨3954470654081764623766777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21090510155102744660089477 3954470654081764623766777)
    ·
      refine ⟨2965852990561323467825083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3954470654081764623766777 2965852990561323467825083)
      ·
        refine ⟨4448779485841985201737625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2965852990561323467825083 4448779485841985201737625)
        ·
          refine ⟨3336584614381488901303219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4448779485841985201737625 3336584614381488901303219)
          ·
            refine ⟨5004876921572233351954829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336584614381488901303219 5004876921572233351954829)
            ·
              refine ⟨1876828845589587506983061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5004876921572233351954829 1876828845589587506983061)
              ·
                refine ⟨87976352137011914389831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1876828845589587506983061 87976352137011914389831)
                ·
                  rfl

theorem cell21_1156500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_1156500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156500 prefixEnd_1156500 := by exact prefixLift 1156500
  have htrace : WordTrace (prefixWord ++ tailWord_1156500) baseStart_1156500 baseEnd_1156500 := by
    simpa [prefixWord, tailWord_1156500, baseEnd_1156500] using wordTrace_append hprefix tailTrace_1156500
  have hstable : (prefixWord ++ tailWord_1156500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156500).length < 2 ^ (prefixWord ++ tailWord_1156500).sum := by decide
  have hdescent : baseEnd_1156500 < baseStart_1156500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156514 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1156514 : Nat := 118140960795 + 1156514 * 2 ^ 59
def prefixEnd_1156514 : Nat := 4983230072969 + 3 ^ 40 * 1156514 * 2
def baseEnd_1156514 : Nat := 263932251401774829936131

theorem tailTrace_1156514 : CollatzResearch.WordTrace tailWord_1156514 prefixEnd_1156514 263932251401774829936131 := by
  unfold tailWord_1156514
  simp only [CollatzResearch.WordTrace]
  refine ⟨10545382733038692427797149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28121020621436513140792397 10545382733038692427797149)
  ·
    refine ⟨3954518524889509660423931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10545382733038692427797149 3954518524889509660423931)
    ·
      refine ⟨5931777787334264490635897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3954518524889509660423931 5931777787334264490635897)
      ·
        refine ⟨4448833340500698367976923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5931777787334264490635897 4448833340500698367976923)
        ·
          refine ⟨6673250010751047551965385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448833340500698367976923 6673250010751047551965385)
          ·
            refine ⟨5004937508063285663974039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6673250010751047551965385 5004937508063285663974039)
            ·
              refine ⟨7507406262094928495961059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004937508063285663974039 7507406262094928495961059)
              ·
                refine ⟨11261109393142392743941589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7507406262094928495961059 11261109393142392743941589)
                ·
                  refine ⟨263932251401774829936131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11261109393142392743941589 263932251401774829936131)
                  ·
                    rfl

theorem cell21_1156514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1156514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156514 prefixEnd_1156514 := by exact prefixLift 1156514
  have htrace : WordTrace (prefixWord ++ tailWord_1156514) baseStart_1156514 baseEnd_1156514 := by
    simpa [prefixWord, tailWord_1156514, baseEnd_1156514] using wordTrace_append hprefix tailTrace_1156514
  have hstable : (prefixWord ++ tailWord_1156514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156514).length < 2 ^ (prefixWord ++ tailWord_1156514).sum := by decide
  have hdescent : baseEnd_1156514 < baseStart_1156514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156548 : List Nat := [2, 3, 3, 2, 1, 1, 2, 4, 3]
def baseStart_1156548 : Nat := 118140960795 + 1156548 * 2 ^ 59
def prefixEnd_1156548 : Nat := 4983230072969 + 3 ^ 40 * 1156548 * 2
def baseEnd_1156548 : Nat := 263940010664998326369395

theorem tailTrace_1156548 : CollatzResearch.WordTrace tailWord_1156548 prefixEnd_1156548 263940010664998326369395 := by
  unfold tailWord_1156548
  simp only [CollatzResearch.WordTrace]
  refine ⟨21091385507015796758963149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28121847342687729011950865 21091385507015796758963149)
  ·
    refine ⟨7909269565130923784611181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21091385507015796758963149 7909269565130923784611181)
    ·
      refine ⟨2965976086924096419229193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7909269565130923784611181 2965976086924096419229193)
      ·
        refine ⟨2224482065193072314421895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2965976086924096419229193 2224482065193072314421895)
        ·
          refine ⟨3336723097789608471632843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224482065193072314421895 3336723097789608471632843)
          ·
            refine ⟨5005084646684412707449265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336723097789608471632843 5005084646684412707449265)
            ·
              refine ⟨3753813485013309530586949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005084646684412707449265 3753813485013309530586949)
              ·
                refine ⟨703840028439995536985053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3753813485013309530586949 703840028439995536985053)
                ·
                  refine ⟨263940010664998326369395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703840028439995536985053 263940010664998326369395)
                  ·
                    rfl

theorem cell21_1156548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_1156548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156548 prefixEnd_1156548 := by exact prefixLift 1156548
  have htrace : WordTrace (prefixWord ++ tailWord_1156548) baseStart_1156548 baseEnd_1156548 := by
    simpa [prefixWord, tailWord_1156548, baseEnd_1156548] using wordTrace_append hprefix tailTrace_1156548
  have hstable : (prefixWord ++ tailWord_1156548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156548).length < 2 ^ (prefixWord ++ tailWord_1156548).sum := by decide
  have hdescent : baseEnd_1156548 < baseStart_1156548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156604 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_1156604 : Nat := 118140960795 + 1156604 * 2 ^ 59
def prefixEnd_1156604 : Nat := 4983230072969 + 3 ^ 40 * 1156604 * 2
def baseEnd_1156604 : Nat := 263952790627954673435947

theorem tailTrace_1156604 : CollatzResearch.WordTrace tailWord_1156604 prefixEnd_1156604 263952790627954673435947 := by
  unfold tailWord_1156604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21092406750914357540982433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28123209001219143387976577 21092406750914357540982433)
  ·
    refine ⟨15819305063185768155736825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21092406750914357540982433 15819305063185768155736825)
    ·
      refine ⟨11864478797389326116802619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15819305063185768155736825 11864478797389326116802619)
      ·
        refine ⟨17796718196083989175203929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11864478797389326116802619 17796718196083989175203929)
        ·
          refine ⟨13347538647062991881402947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17796718196083989175203929 13347538647062991881402947)
          ·
            refine ⟨20021307970594487822104421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13347538647062991881402947 20021307970594487822104421)
            ·
              refine ⟨3753995244486466466644579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20021307970594487822104421 3753995244486466466644579)
              ·
                refine ⟨5630992866729699699966869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753995244486466466644579 5630992866729699699966869)
                ·
                  refine ⟨263952790627954673435947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5630992866729699699966869 263952790627954673435947)
                  ·
                    rfl

theorem cell21_1156604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_1156604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156604 prefixEnd_1156604 := by exact prefixLift 1156604
  have htrace : WordTrace (prefixWord ++ tailWord_1156604) baseStart_1156604 baseEnd_1156604 := by
    simpa [prefixWord, tailWord_1156604, baseEnd_1156604] using wordTrace_append hprefix tailTrace_1156604
  have hstable : (prefixWord ++ tailWord_1156604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156604).length < 2 ^ (prefixWord ++ tailWord_1156604).sum := by decide
  have hdescent : baseEnd_1156604 < baseStart_1156604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156669 : List Nat := [1, 4, 1, 3, 4, 1, 1, 6]
def baseStart_1156669 : Nat := 118140960795 + 1156669 * 2 ^ 59
def prefixEnd_1156669 : Nat := 4983230072969 + 3 ^ 40 * 1156669 * 2
def baseEnd_1156669 : Nat := 87989208171176334950827

theorem tailTrace_1156669 : CollatzResearch.WordTrace tailWord_1156669 prefixEnd_1156669 87989208171176334950827 := by
  unfold tailWord_1156669
  simp only [CollatzResearch.WordTrace]
  refine ⟨42187184246593231183081061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28124789497728820788720707 42187184246593231183081061)
  ·
    refine ⟨7910097046236230846827699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42187184246593231183081061 7910097046236230846827699)
    ·
      refine ⟨11865145569354346270241549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7910097046236230846827699 11865145569354346270241549)
      ·
        refine ⟨4449429588507879851340581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11865145569354346270241549 4449429588507879851340581)
        ·
          refine ⟨834268047845227472126359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4449429588507879851340581 834268047845227472126359)
          ·
            refine ⟨1251402071767841208189539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834268047845227472126359 1251402071767841208189539)
            ·
              refine ⟨1877103107651761812284309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251402071767841208189539 1877103107651761812284309)
              ·
                refine ⟨87989208171176334950827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1877103107651761812284309 87989208171176334950827)
                ·
                  rfl

theorem cell21_1156669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 6].length) (baseStart_1156669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156669 prefixEnd_1156669 := by exact prefixLift 1156669
  have htrace : WordTrace (prefixWord ++ tailWord_1156669) baseStart_1156669 baseEnd_1156669 := by
    simpa [prefixWord, tailWord_1156669, baseEnd_1156669] using wordTrace_append hprefix tailTrace_1156669
  have hstable : (prefixWord ++ tailWord_1156669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156669).length < 2 ^ (prefixWord ++ tailWord_1156669).sum := by decide
  have hdescent : baseEnd_1156669 < baseStart_1156669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156700 : List Nat := [2, 2, 4, 1, 2, 2, 2, 3, 3]
def baseStart_1156700 : Nat := 118140960795 + 1156700 * 2 ^ 59
def prefixEnd_1156700 : Nat := 4983230072969 + 3 ^ 40 * 1156700 * 2
def baseEnd_1156700 : Nat := 263974699135879839835751

theorem tailTrace_1156700 : CollatzResearch.WordTrace tailWord_1156700 prefixEnd_1156700 263974699135879839835751 := by
  unfold tailWord_1156700
  simp only [CollatzResearch.WordTrace]
  refine ⟨21094157454740461738729777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28125543272987282318306369 21094157454740461738729777)
  ·
    refine ⟨15820618091055346304047333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21094157454740461738729777 15820618091055346304047333)
    ·
      refine ⟨2966365892072877432008875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15820618091055346304047333 2966365892072877432008875)
      ·
        refine ⟨4449548838109316148013313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2966365892072877432008875 4449548838109316148013313)
        ·
          refine ⟨3337161628581987111009985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4449548838109316148013313 3337161628581987111009985)
          ·
            refine ⟨2502871221436490333257489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337161628581987111009985 2502871221436490333257489)
            ·
              refine ⟨1877153416077367749943117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2502871221436490333257489 1877153416077367749943117)
              ·
                refine ⟨703932531029012906228669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1877153416077367749943117 703932531029012906228669)
                ·
                  refine ⟨263974699135879839835751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703932531029012906228669 263974699135879839835751)
                  ·
                    rfl

theorem cell21_1156700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_1156700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156700 prefixEnd_1156700 := by exact prefixLift 1156700
  have htrace : WordTrace (prefixWord ++ tailWord_1156700) baseStart_1156700 baseEnd_1156700 := by
    simpa [prefixWord, tailWord_1156700, baseEnd_1156700] using wordTrace_append hprefix tailTrace_1156700
  have hstable : (prefixWord ++ tailWord_1156700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156700).length < 2 ^ (prefixWord ++ tailWord_1156700).sum := by decide
  have hdescent : baseEnd_1156700 < baseStart_1156700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156714 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_1156714 : Nat := 118140960795 + 1156714 * 2 ^ 59
def prefixEnd_1156714 : Nat := 4983230072969 + 3 ^ 40 * 1156714 * 2
def baseEnd_1156714 : Nat := 263977894126618926602389

theorem tailTrace_1156714 : CollatzResearch.WordTrace tailWord_1156714 prefixEnd_1156714 263977894126618926602389 := by
  unfold tailWord_1156714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547206382857550967117299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28125883687620135912312797 10547206382857550967117299)
  ·
    refine ⟨15820809574286326450675949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10547206382857550967117299 15820809574286326450675949)
    ·
      refine ⟨5932803590357372419003481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15820809574286326450675949 5932803590357372419003481)
      ·
        refine ⟨4449602692768029314252611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5932803590357372419003481 4449602692768029314252611)
        ·
          refine ⟨6674404039152043971378917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4449602692768029314252611 6674404039152043971378917)
          ·
            refine ⟨1251450757341008244633547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6674404039152043971378917 1251450757341008244633547)
            ·
              refine ⟨1877176136011512366950321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251450757341008244633547 1877176136011512366950321)
              ·
                refine ⟨1407882102008634275212741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877176136011512366950321 1407882102008634275212741)
                ·
                  refine ⟨263977894126618926602389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407882102008634275212741 263977894126618926602389)
                  ·
                    rfl

theorem cell21_1156714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_1156714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156714 prefixEnd_1156714 := by exact prefixLift 1156714
  have htrace : WordTrace (prefixWord ++ tailWord_1156714) baseStart_1156714 baseEnd_1156714 := by
    simpa [prefixWord, tailWord_1156714, baseEnd_1156714] using wordTrace_append hprefix tailTrace_1156714
  have hstable : (prefixWord ++ tailWord_1156714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156714).length < 2 ^ (prefixWord ++ tailWord_1156714).sum := by decide
  have hdescent : baseEnd_1156714 < baseStart_1156714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156759 : List Nat := [1, 1, 3, 3, 2, 2, 3, 3, 3]
def baseStart_1156759 : Nat := 118140960795 + 1156759 * 2 ^ 59
def prefixEnd_1156759 : Nat := 4983230072969 + 3 ^ 40 * 1156759 * 2
def baseEnd_1156759 : Nat := 263988163739708848352297

theorem tailTrace_1156759 : CollatzResearch.WordTrace tailWord_1156759 prefixEnd_1156759 263988163739708848352297 := by
  unfold tailWord_1156759
  simp only [CollatzResearch.WordTrace]
  refine ⟨42190466816267176553857331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28126977877511451035904887 42190466816267176553857331)
  ·
    refine ⟨63285700224400764830785997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42190466816267176553857331 63285700224400764830785997)
    ·
      refine ⟨23732137584150286811544749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63285700224400764830785997 23732137584150286811544749)
      ·
        refine ⟨8899551594056357554329281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23732137584150286811544749 8899551594056357554329281)
        ·
          refine ⟨6674663695542268165746961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8899551594056357554329281 6674663695542268165746961)
          ·
            refine ⟨5005997771656701124310221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6674663695542268165746961 5005997771656701124310221)
            ·
              refine ⟨1877249164371262921616333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5005997771656701124310221 1877249164371262921616333)
              ·
                refine ⟨703968436639223595606125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1877249164371262921616333 703968436639223595606125)
                ·
                  refine ⟨263988163739708848352297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703968436639223595606125 263988163739708848352297)
                  ·
                    rfl

theorem cell21_1156759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 3].length) (baseStart_1156759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156759 prefixEnd_1156759 := by exact prefixLift 1156759
  have htrace : WordTrace (prefixWord ++ tailWord_1156759) baseStart_1156759 baseEnd_1156759 := by
    simpa [prefixWord, tailWord_1156759, baseEnd_1156759] using wordTrace_append hprefix tailTrace_1156759
  have hstable : (prefixWord ++ tailWord_1156759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156759).length < 2 ^ (prefixWord ++ tailWord_1156759).sum := by decide
  have hdescent : baseEnd_1156759 < baseStart_1156759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156815 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 8]
def baseStart_1156815 : Nat := 118140960795 + 1156815 * 2 ^ 59
def prefixEnd_1156815 : Nat := 4983230072969 + 3 ^ 40 * 1156815 * 2
def baseEnd_1156815 : Nat := 264000943702665195418849

theorem tailTrace_1156815 : CollatzResearch.WordTrace tailWord_1156815 prefixEnd_1156815 264000943702665195418849 := by
  unfold tailWord_1156815
  simp only [CollatzResearch.WordTrace]
  refine ⟨42192509304064298117895899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28128339536042865411930599 42192509304064298117895899)
  ·
    refine ⟨63288763956096447176843849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42192509304064298117895899 63288763956096447176843849)
    ·
      refine ⟨47466572967072335382632887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63288763956096447176843849 47466572967072335382632887)
      ·
        refine ⟨71199859450608503073949331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47466572967072335382632887 71199859450608503073949331)
        ·
          refine ⟨106799789175912754610923997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71199859450608503073949331 106799789175912754610923997)
          ·
            refine ⟨40049920940967282979096499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106799789175912754610923997 40049920940967282979096499)
            ·
              refine ⟨60074881411450924468644749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40049920940967282979096499 60074881411450924468644749)
              ·
                refine ⟨22528080529294096675741781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60074881411450924468644749 22528080529294096675741781)
                ·
                  refine ⟨264000943702665195418849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22528080529294096675741781 264000943702665195418849)
                  ·
                    rfl

theorem cell21_1156815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_1156815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156815 prefixEnd_1156815 := by exact prefixLift 1156815
  have htrace : WordTrace (prefixWord ++ tailWord_1156815) baseStart_1156815 baseEnd_1156815 := by
    simpa [prefixWord, tailWord_1156815, baseEnd_1156815] using wordTrace_append hprefix tailTrace_1156815
  have hstable : (prefixWord ++ tailWord_1156815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156815).length < 2 ^ (prefixWord ++ tailWord_1156815).sum := by decide
  have hdescent : baseEnd_1156815 < baseStart_1156815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156832 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_1156832 : Nat := 118140960795 + 1156832 * 2 ^ 59
def prefixEnd_1156832 : Nat := 4983230072969 + 3 ^ 40 * 1156832 * 2
def baseEnd_1156832 : Nat := 264004823334276943635481

theorem tailTrace_1156832 : CollatzResearch.WordTrace tailWord_1156832 prefixEnd_1156832 264004823334276943635481 := by
  unfold tailWord_1156832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21096564672501355010632375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28128752896668473347509833 21096564672501355010632375)
  ·
    refine ⟨31644847008752032515948563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21096564672501355010632375 31644847008752032515948563)
    ·
      refine ⟨47467270513128048773922845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31644847008752032515948563 47467270513128048773922845)
      ·
        refine ⟨17800226442423018290221067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47467270513128048773922845 17800226442423018290221067)
        ·
          refine ⟨26700339663634527435331601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17800226442423018290221067 26700339663634527435331601)
          ·
            refine ⟨20025254747725895576498701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26700339663634527435331601 20025254747725895576498701)
            ·
              refine ⟨7509470530397210841187013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20025254747725895576498701 7509470530397210841187013)
              ·
                refine ⟨1408025724449477032722565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7509470530397210841187013 1408025724449477032722565)
                ·
                  refine ⟨264004823334276943635481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408025724449477032722565 264004823334276943635481)
                  ·
                    rfl

theorem cell21_1156832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_1156832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156832 prefixEnd_1156832 := by exact prefixLift 1156832
  have htrace : WordTrace (prefixWord ++ tailWord_1156832) baseStart_1156832 baseEnd_1156832 := by
    simpa [prefixWord, tailWord_1156832, baseEnd_1156832] using wordTrace_append hprefix tailTrace_1156832
  have hstable : (prefixWord ++ tailWord_1156832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156832).length < 2 ^ (prefixWord ++ tailWord_1156832).sum := by decide
  have hdescent : baseEnd_1156832 < baseStart_1156832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156852 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1156852 : Nat := 118140960795 + 1156852 * 2 ^ 59
def prefixEnd_1156852 : Nat := 4983230072969 + 3 ^ 40 * 1156852 * 2
def baseEnd_1156852 : Nat := 264009387606761353302107

theorem tailTrace_1156852 : CollatzResearch.WordTrace tailWord_1156852 prefixEnd_1156852 264009387606761353302107 := by
  unfold tailWord_1156852
  simp only [CollatzResearch.WordTrace]
  refine ⟨21096929402465126718496405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28129239203286835624661873 21096929402465126718496405)
  ·
    refine ⟨988918565740552814929519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21096929402465126718496405 988918565740552814929519)
    ·
      refine ⟨1483377848610829222394279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988918565740552814929519 1483377848610829222394279)
      ·
        refine ⟨2225066772916243833591419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483377848610829222394279 2225066772916243833591419)
        ·
          refine ⟨3337600159374365750387129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225066772916243833591419 3337600159374365750387129)
          ·
            refine ⟨2503200119530774312790347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337600159374365750387129 2503200119530774312790347)
            ·
              refine ⟨3754800179296161469185521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503200119530774312790347 3754800179296161469185521)
              ·
                refine ⟨2816100134472121101889141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3754800179296161469185521 2816100134472121101889141)
                ·
                  refine ⟨264009387606761353302107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2816100134472121101889141 264009387606761353302107)
                  ·
                    rfl

theorem cell21_1156852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1156852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156852 prefixEnd_1156852 := by exact prefixLift 1156852
  have htrace : WordTrace (prefixWord ++ tailWord_1156852) baseStart_1156852 baseEnd_1156852 := by
    simpa [prefixWord, tailWord_1156852, baseEnd_1156852] using wordTrace_append hprefix tailTrace_1156852
  have hstable : (prefixWord ++ tailWord_1156852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156852).length < 2 ^ (prefixWord ++ tailWord_1156852).sum := by decide
  have hdescent : baseEnd_1156852 < baseStart_1156852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156891 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 6]
def baseStart_1156891 : Nat := 118140960795 + 1156891 * 2 ^ 59
def prefixEnd_1156891 : Nat := 4983230072969 + 3 ^ 40 * 1156891 * 2
def baseEnd_1156891 : Nat := 264018287938105952152027

theorem tailTrace_1156891 : CollatzResearch.WordTrace tailWord_1156891 prefixEnd_1156891 264018287938105952152027 := by
  unfold tailWord_1156891
  simp only [CollatzResearch.WordTrace]
  refine ⟨42195281251788963097662527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28130187501192642065108351 42195281251788963097662527)
  ·
    refine ⟨63292921877683444646493791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42195281251788963097662527 63292921877683444646493791)
    ·
      refine ⟨94939382816525166969740687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63292921877683444646493791 94939382816525166969740687)
      ·
        refine ⟨142409074224787750454611031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94939382816525166969740687 142409074224787750454611031)
        ·
          refine ⟨213613611337181625681916547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142409074224787750454611031 213613611337181625681916547)
          ·
            refine ⟨320420417005772438522874821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213613611337181625681916547 320420417005772438522874821)
            ·
              refine ⟨60078828188582332223039029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320420417005772438522874821 60078828188582332223039029)
              ·
                refine ⟨5632390142679593645909909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60078828188582332223039029 5632390142679593645909909)
                ·
                  refine ⟨264018287938105952152027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5632390142679593645909909 264018287938105952152027)
                  ·
                    rfl

theorem cell21_1156891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_1156891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156891 prefixEnd_1156891 := by exact prefixLift 1156891
  have htrace : WordTrace (prefixWord ++ tailWord_1156891) baseStart_1156891 baseEnd_1156891 := by
    simpa [prefixWord, tailWord_1156891, baseEnd_1156891] using wordTrace_append hprefix tailTrace_1156891
  have hstable : (prefixWord ++ tailWord_1156891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156891).length < 2 ^ (prefixWord ++ tailWord_1156891).sum := by decide
  have hdescent : baseEnd_1156891 < baseStart_1156891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156956 : List Nat := [2, 2, 4, 2, 2, 1, 2, 6]
def baseStart_1156956 : Nat := 118140960795 + 1156956 * 2 ^ 59
def prefixEnd_1156956 : Nat := 4983230072969 + 3 ^ 40 * 1156956 * 2
def baseEnd_1156956 : Nat := 88011040607893427856187

theorem tailTrace_1156956 : CollatzResearch.WordTrace tailWord_1156956 prefixEnd_1156956 88011040607893427856187 := by
  unfold tailWord_1156956
  simp only [CollatzResearch.WordTrace]
  refine ⟨21098825998276739599389361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28131767997702319465852481 21098825998276739599389361)
  ·
    refine ⟨15824119498707554699542021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21098825998276739599389361 15824119498707554699542021)
    ·
      refine ⟨2967022406007666506164129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15824119498707554699542021 2967022406007666506164129)
      ·
        refine ⟨2225266804505749879623097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2967022406007666506164129 2225266804505749879623097)
        ·
          refine ⟨1668950103379312409717323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2225266804505749879623097 1668950103379312409717323)
          ·
            refine ⟨2503425155068968614575985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668950103379312409717323 2503425155068968614575985)
            ·
              refine ⟨1877568866301726460931989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503425155068968614575985 1877568866301726460931989)
              ·
                refine ⟨88011040607893427856187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1877568866301726460931989 88011040607893427856187)
                ·
                  rfl

theorem cell21_1156956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_1156956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1156956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1156956 prefixEnd_1156956 := by exact prefixLift 1156956
  have htrace : WordTrace (prefixWord ++ tailWord_1156956) baseStart_1156956 baseEnd_1156956 := by
    simpa [prefixWord, tailWord_1156956, baseEnd_1156956] using wordTrace_append hprefix tailTrace_1156956
  have hstable : (prefixWord ++ tailWord_1156956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156956).length < 2 ^ (prefixWord ++ tailWord_1156956).sum := by decide
  have hdescent : baseEnd_1156956 < baseStart_1156956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157015 : List Nat := [1, 1, 3, 3, 1, 5, 1, 6]
def baseStart_1157015 : Nat := 118140960795 + 1157015 * 2 ^ 59
def prefixEnd_1157015 : Nat := 4983230072969 + 3 ^ 40 * 1157015 * 2
def baseEnd_1157015 : Nat := 88015528809169764028369

theorem tailTrace_1157015 : CollatzResearch.WordTrace tailWord_1157015 prefixEnd_1157015 88015528809169764028369 := by
  unfold tailWord_1157015
  simp only [CollatzResearch.WordTrace]
  refine ⟨42199803903339732275176499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28133202602226488183450999 42199803903339732275176499)
  ·
    refine ⟨63299705855009598412764749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42199803903339732275176499 63299705855009598412764749)
    ·
      refine ⟨23737389695628599404786781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63299705855009598412764749 23737389695628599404786781)
      ·
        refine ⟨8901521135860724776795043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23737389695628599404786781 8901521135860724776795043)
        ·
          refine ⟨13352281703791087165192565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8901521135860724776795043 13352281703791087165192565)
          ·
            refine ⟨1251776409730414421736803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13352281703791087165192565 1251776409730414421736803)
            ·
              refine ⟨1877664614595621632605205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251776409730414421736803 1877664614595621632605205)
              ·
                refine ⟨88015528809169764028369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1877664614595621632605205 88015528809169764028369)
                ·
                  rfl

theorem cell21_1157015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 6].length) (baseStart_1157015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157015 prefixEnd_1157015 := by exact prefixLift 1157015
  have htrace : WordTrace (prefixWord ++ tailWord_1157015) baseStart_1157015 baseEnd_1157015 := by
    simpa [prefixWord, tailWord_1157015, baseEnd_1157015] using wordTrace_append hprefix tailTrace_1157015
  have hstable : (prefixWord ++ tailWord_1157015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157015).length < 2 ^ (prefixWord ++ tailWord_1157015).sum := by decide
  have hdescent : baseEnd_1157015 < baseStart_1157015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157038 : List Nat := [4, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_1157038 : Nat := 118140960795 + 1157038 * 2 ^ 59
def prefixEnd_1157038 : Nat := 4983230072969 + 3 ^ 40 * 1157038 * 2
def baseEnd_1157038 : Nat := 264051835340866363201727

theorem tailTrace_1157038 : CollatzResearch.WordTrace tailWord_1157038 prefixEnd_1157038 264051835340866363201727 := by
  unfold tailWord_1157038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275080347782050900407971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28133761854837604802175845 5275080347782050900407971)
  ·
    refine ⟨7912620521673076350611957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5275080347782050900407971 7912620521673076350611957)
    ·
      refine ⟨741808173906850907869871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7912620521673076350611957 741808173906850907869871)
      ·
        refine ⟨1112712260860276361804807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741808173906850907869871 1112712260860276361804807)
        ·
          refine ⟨1669068391290414542707211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112712260860276361804807 1669068391290414542707211)
          ·
            refine ⟨2503602586935621814060817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669068391290414542707211 2503602586935621814060817)
            ·
              refine ⟨1877701940201716360545613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503602586935621814060817 1877701940201716360545613)
              ·
                refine ⟨704138227575643635204605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1877701940201716360545613 704138227575643635204605)
                ·
                  refine ⟨264051835340866363201727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704138227575643635204605 264051835340866363201727)
                  ·
                    rfl

theorem cell21_1157038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_1157038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157038 prefixEnd_1157038 := by exact prefixLift 1157038
  have htrace : WordTrace (prefixWord ++ tailWord_1157038) baseStart_1157038 baseEnd_1157038 := by
    simpa [prefixWord, tailWord_1157038, baseEnd_1157038] using wordTrace_append hprefix tailTrace_1157038
  have hstable : (prefixWord ++ tailWord_1157038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157038).length < 2 ^ (prefixWord ++ tailWord_1157038).sum := by decide
  have hdescent : baseEnd_1157038 < baseStart_1157038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157043 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 6]
def baseStart_1157043 : Nat := 118140960795 + 1157043 * 2 ^ 59
def prefixEnd_1157043 : Nat := 4983230072969 + 3 ^ 40 * 1157043 * 2
def baseEnd_1157043 : Nat := 264052976408987465618383

theorem tailTrace_1157043 : CollatzResearch.WordTrace tailWord_1157043 prefixEnd_1157043 264052976408987465618383 := by
  unfold tailWord_1157043
  simp only [CollatzResearch.WordTrace]
  refine ⟨42200825147238293057195783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28133883431492195371463855 42200825147238293057195783)
  ·
    refine ⟨63301237720857439585793675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42200825147238293057195783 63301237720857439585793675)
    ·
      refine ⟨94951856581286159378690513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63301237720857439585793675 94951856581286159378690513)
      ·
        refine ⟨71213892435964619534017885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94951856581286159378690513 71213892435964619534017885)
        ·
          refine ⟨26705209663486732325256707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71213892435964619534017885 26705209663486732325256707)
          ·
            refine ⟨40057814495230098487885061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26705209663486732325256707 40057814495230098487885061)
            ·
              refine ⟨7510840217855643466478449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40057814495230098487885061 7510840217855643466478449)
              ·
                refine ⟨5633130163391732599858837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7510840217855643466478449 5633130163391732599858837)
                ·
                  refine ⟨264052976408987465618383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5633130163391732599858837 264052976408987465618383)
                  ·
                    rfl

theorem cell21_1157043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_1157043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157043 prefixEnd_1157043 := by exact prefixLift 1157043
  have htrace : WordTrace (prefixWord ++ tailWord_1157043) baseStart_1157043 baseEnd_1157043 := by
    simpa [prefixWord, tailWord_1157043, baseEnd_1157043] using wordTrace_append hprefix tailTrace_1157043
  have hstable : (prefixWord ++ tailWord_1157043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157043).length < 2 ^ (prefixWord ++ tailWord_1157043).sum := by decide
  have hdescent : baseEnd_1157043 < baseStart_1157043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157091 : List Nat := [1, 1, 1, 6, 1, 2, 4, 5]
def baseStart_1157091 : Nat := 118140960795 + 1157091 * 2 ^ 59
def prefixEnd_1157091 : Nat := 4983230072969 + 3 ^ 40 * 1157091 * 2
def baseEnd_1157091 : Nat := 88021310220983349606095

theorem tailTrace_1157091 : CollatzResearch.WordTrace tailWord_1157091 prefixEnd_1157091 88021310220983349606095 := by
  unfold tailWord_1157091
  simp only [CollatzResearch.WordTrace]
  refine ⟨42202575851064397254943127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28135050567376264836628751 42202575851064397254943127)
  ·
    refine ⟨63303863776596595882414691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42202575851064397254943127 63303863776596595882414691)
    ·
      refine ⟨94955795664894893823622037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63303863776596595882414691 94955795664894893823622037)
      ·
        refine ⟨4451052921791948147982283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94955795664894893823622037 4451052921791948147982283)
        ·
          refine ⟨6676579382687922221973425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4451052921791948147982283 6676579382687922221973425)
          ·
            refine ⟨5007434537015941666480069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6676579382687922221973425 5007434537015941666480069)
            ·
              refine ⟨938893975690489062465013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5007434537015941666480069 938893975690489062465013)
              ·
                refine ⟨88021310220983349606095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 938893975690489062465013 88021310220983349606095)
                ·
                  rfl

theorem cell21_1157091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 5].length) (baseStart_1157091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157091 prefixEnd_1157091 := by exact prefixLift 1157091
  have htrace : WordTrace (prefixWord ++ tailWord_1157091) baseStart_1157091 baseEnd_1157091 := by
    simpa [prefixWord, tailWord_1157091, baseEnd_1157091] using wordTrace_append hprefix tailTrace_1157091
  have hstable : (prefixWord ++ tailWord_1157091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157091).length < 2 ^ (prefixWord ++ tailWord_1157091).sum := by decide
  have hdescent : baseEnd_1157091 < baseStart_1157091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157164 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1157164 : Nat := 118140960795 + 1157164 * 2 ^ 59
def prefixEnd_1157164 : Nat := 4983230072969 + 3 ^ 40 * 1157164 * 2
def baseEnd_1157164 : Nat := 264080590257518144101469

theorem tailTrace_1157164 : CollatzResearch.WordTrace tailWord_1157164 prefixEnd_1157164 264080590257518144101469 := by
  unfold tailWord_1157164
  simp only [CollatzResearch.WordTrace]
  refine ⟨21102619189899965361175273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28136825586533287148233697 21102619189899965361175273)
  ·
    refine ⟨15826964392424974020881455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21102619189899965361175273 15826964392424974020881455)
    ·
      refine ⟨23740446588637461031322183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15826964392424974020881455 23740446588637461031322183)
      ·
        refine ⟨35610669882956191546983275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23740446588637461031322183 35610669882956191546983275)
        ·
          refine ⟨53416004824434287320474913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35610669882956191546983275 53416004824434287320474913)
          ·
            refine ⟨40062003618325715490356185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53416004824434287320474913 40062003618325715490356185)
            ·
              refine ⟨30046502713744286617767139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40062003618325715490356185 30046502713744286617767139)
              ·
                refine ⟨45069754070616429926650709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30046502713744286617767139 45069754070616429926650709)
                ·
                  refine ⟨264080590257518144101469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45069754070616429926650709 264080590257518144101469)
                  ·
                    rfl

theorem cell21_1157164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1157164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157164 prefixEnd_1157164 := by exact prefixLift 1157164
  have htrace : WordTrace (prefixWord ++ tailWord_1157164) baseStart_1157164 baseEnd_1157164 := by
    simpa [prefixWord, tailWord_1157164, baseEnd_1157164] using wordTrace_append hprefix tailTrace_1157164
  have hstable : (prefixWord ++ tailWord_1157164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157164).length < 2 ^ (prefixWord ++ tailWord_1157164).sum := by decide
  have hdescent : baseEnd_1157164 < baseStart_1157164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157181 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1157181 : Nat := 118140960795 + 1157181 * 2 ^ 59
def prefixEnd_1157181 : Nat := 4983230072969 + 3 ^ 40 * 1157181 * 2
def baseEnd_1157181 : Nat := 264084469889129892318101

theorem tailTrace_1157181 : CollatzResearch.WordTrace tailWord_1157181 prefixEnd_1157181 264084469889129892318101 := by
  unfold tailWord_1157181
  simp only [CollatzResearch.WordTrace]
  refine ⟨42205858420738342625719397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28137238947158895083812931 42205858420738342625719397)
  ·
    refine ⟨7913598453888439242322387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42205858420738342625719397 7913598453888439242322387)
    ·
      refine ⟨11870397680832658863483581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7913598453888439242322387 11870397680832658863483581)
      ·
        refine ⟨4451399130312247073806343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11870397680832658863483581 4451399130312247073806343)
        ·
          refine ⟨6677098695468370610709515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4451399130312247073806343 6677098695468370610709515)
          ·
            refine ⟨10015648043202555916064273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6677098695468370610709515 10015648043202555916064273)
            ·
              refine ⟨7511736032401916937048205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10015648043202555916064273 7511736032401916937048205)
              ·
                refine ⟨2816901012150718851393077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7511736032401916937048205 2816901012150718851393077)
                ·
                  refine ⟨264084469889129892318101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2816901012150718851393077 264084469889129892318101)
                  ·
                    rfl

theorem cell21_1157181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1157181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157181 prefixEnd_1157181 := by exact prefixLift 1157181
  have htrace : WordTrace (prefixWord ++ tailWord_1157181) baseStart_1157181 baseEnd_1157181 := by
    simpa [prefixWord, tailWord_1157181, baseEnd_1157181] using wordTrace_append hprefix tailTrace_1157181
  have hstable : (prefixWord ++ tailWord_1157181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157181).length < 2 ^ (prefixWord ++ tailWord_1157181).sum := by decide
  have hdescent : baseEnd_1157181 < baseStart_1157181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157423 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 4]
def baseStart_1157423 : Nat := 118140960795 + 1157423 * 2 ^ 59
def prefixEnd_1157423 : Nat := 4983230072969 + 3 ^ 40 * 1157423 * 2
def baseEnd_1157423 : Nat := 264139697586191249284273

theorem tailTrace_1157423 : CollatzResearch.WordTrace tailWord_1157423 prefixEnd_1157423 264139697586191249284273 := by
  unfold tailWord_1157423
  simp only [CollatzResearch.WordTrace]
  refine ⟨42214684885861617956028923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28143123257241078637352615 42214684885861617956028923)
  ·
    refine ⟨63322027328792426934043385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42214684885861617956028923 63322027328792426934043385)
    ·
      refine ⟨47491520496594320200532539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63322027328792426934043385 47491520496594320200532539)
      ·
        refine ⟨71237280744891480300798809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47491520496594320200532539 71237280744891480300798809)
        ·
          refine ⟨53427960558668610225599107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71237280744891480300798809 53427960558668610225599107)
          ·
            refine ⟨80141940838002915338398661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53427960558668610225599107 80141940838002915338398661)
            ·
              refine ⟨15026613907125546625949749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80141940838002915338398661 15026613907125546625949749)
              ·
                refine ⟨1408745053793019996182789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15026613907125546625949749 1408745053793019996182789)
                ·
                  refine ⟨264139697586191249284273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408745053793019996182789 264139697586191249284273)
                  ·
                    rfl

theorem cell21_1157423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_1157423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157423 prefixEnd_1157423 := by exact prefixLift 1157423
  have htrace : WordTrace (prefixWord ++ tailWord_1157423) baseStart_1157423 baseEnd_1157423 := by
    simpa [prefixWord, tailWord_1157423, baseEnd_1157423] using wordTrace_append hprefix tailTrace_1157423
  have hstable : (prefixWord ++ tailWord_1157423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157423).length < 2 ^ (prefixWord ++ tailWord_1157423).sum := by decide
  have hdescent : baseEnd_1157423 < baseStart_1157423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157474 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1157474 : Nat := 118140960795 + 1157474 * 2 ^ 59
def prefixEnd_1157474 : Nat := 4983230072969 + 3 ^ 40 * 1157474 * 2
def baseEnd_1157474 : Nat := 264151336481026493934169

theorem tailTrace_1157474 : CollatzResearch.WordTrace tailWord_1157474 prefixEnd_1157474 264151336481026493934169 := by
  unfold tailWord_1157474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10554136252169213416533869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28144363339117902444090317 10554136252169213416533869)
  ·
    refine ⟨3957801094563455031200201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10554136252169213416533869 3957801094563455031200201)
    ·
      refine ⟨2968350820922591273400151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3957801094563455031200201 2968350820922591273400151)
      ·
        refine ⟨4452526231383886910100227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968350820922591273400151 4452526231383886910100227)
        ·
          refine ⟨6678789347075830365150341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4452526231383886910100227 6678789347075830365150341)
          ·
            refine ⟨1252273002576718193465689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6678789347075830365150341 1252273002576718193465689)
            ·
              refine ⟨939204751932538645099267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252273002576718193465689 939204751932538645099267)
              ·
                refine ⟨1408807127898807967648901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939204751932538645099267 1408807127898807967648901)
                ·
                  refine ⟨264151336481026493934169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408807127898807967648901 264151336481026493934169)
                  ·
                    rfl

theorem cell21_1157474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1157474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157474 prefixEnd_1157474 := by exact prefixLift 1157474
  have htrace : WordTrace (prefixWord ++ tailWord_1157474) baseStart_1157474 baseEnd_1157474 := by
    simpa [prefixWord, tailWord_1157474, baseEnd_1157474] using wordTrace_append hprefix tailTrace_1157474
  have hstable : (prefixWord ++ tailWord_1157474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157474).length < 2 ^ (prefixWord ++ tailWord_1157474).sum := by decide
  have hdescent : baseEnd_1157474 < baseStart_1157474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157513 : List Nat := [1, 2, 1, 1, 6, 10]
def baseStart_1157513 : Nat := 118140960795 + 1157513 * 2 ^ 59
def prefixEnd_1157513 : Nat := 4983230072969 + 3 ^ 40 * 1157513 * 2
def baseEnd_1157513 : Nat := 9783712474532262695707

theorem tailTrace_1157513 : CollatzResearch.WordTrace tailWord_1157513 prefixEnd_1157513 9783712474532262695707 := by
  unfold tailWord_1157513
  simp only [CollatzResearch.WordTrace]
  refine ⟨42217967455535563326805193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28145311637023708884536795 42217967455535563326805193)
  ·
    refine ⟨31663475591651672495103895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42217967455535563326805193 31663475591651672495103895)
    ·
      refine ⟨47495213387477508742655843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31663475591651672495103895 47495213387477508742655843)
      ·
        refine ⟨71242820081216263113983765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47495213387477508742655843 71242820081216263113983765)
        ·
          refine ⟨3339507191307012333467989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71242820081216263113983765 3339507191307012333467989)
          ·
            refine ⟨9783712474532262695707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3339507191307012333467989 9783712474532262695707)
            ·
              rfl

theorem cell21_1157513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 10].length) (baseStart_1157513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157513 prefixEnd_1157513 := by exact prefixLift 1157513
  have htrace : WordTrace (prefixWord ++ tailWord_1157513) baseStart_1157513 baseEnd_1157513 := by
    simpa [prefixWord, tailWord_1157513, baseEnd_1157513] using wordTrace_append hprefix tailTrace_1157513
  have hstable : (prefixWord ++ tailWord_1157513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157513).length < 2 ^ (prefixWord ++ tailWord_1157513).sum := by decide
  have hdescent : baseEnd_1157513 < baseStart_1157513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157516 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_1157516 : Nat := 118140960795 + 1157516 * 2 ^ 59
def prefixEnd_1157516 : Nat := 4983230072969 + 3 ^ 40 * 1157516 * 2
def baseEnd_1157516 : Nat := 264160921453243754234083

theorem tailTrace_1157516 : CollatzResearch.WordTrace tailWord_1157516 prefixEnd_1157516 264160921453243754234083 := by
  unfold tailWord_1157516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21109038437262347419582201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28145384583016463226109601 21109038437262347419582201)
  ·
    refine ⟨15831778827946760564686651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21109038437262347419582201 15831778827946760564686651)
    ·
      refine ⟨23747668241920140847029977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15831778827946760564686651 23747668241920140847029977)
      ·
        refine ⟨17810751181440105635272483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23747668241920140847029977 17810751181440105635272483)
        ·
          refine ⟨26716126772160158452908725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17810751181440105635272483 26716126772160158452908725)
          ·
            refine ⟨2504636884890014854960193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26716126772160158452908725 2504636884890014854960193)
            ·
              refine ⟨1878477663667511141220145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2504636884890014854960193 1878477663667511141220145)
              ·
                refine ⟨1408858247750633355915109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878477663667511141220145 1408858247750633355915109)
                ·
                  refine ⟨264160921453243754234083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408858247750633355915109 264160921453243754234083)
                  ·
                    rfl

theorem cell21_1157516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_1157516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157516 prefixEnd_1157516 := by exact prefixLift 1157516
  have htrace : WordTrace (prefixWord ++ tailWord_1157516) baseStart_1157516 baseEnd_1157516 := by
    simpa [prefixWord, tailWord_1157516, baseEnd_1157516] using wordTrace_append hprefix tailTrace_1157516
  have hstable : (prefixWord ++ tailWord_1157516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157516).length < 2 ^ (prefixWord ++ tailWord_1157516).sum := by decide
  have hdescent : baseEnd_1157516 < baseStart_1157516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157530 : List Nat := [3, 1, 1, 4, 1, 2, 3, 6]
def baseStart_1157530 : Nat := 118140960795 + 1157530 * 2 ^ 59
def prefixEnd_1157530 : Nat := 4983230072969 + 3 ^ 40 * 1157530 * 2
def baseEnd_1157530 : Nat := 88054705481327613666907

theorem tailTrace_1157530 : CollatzResearch.WordTrace tailWord_1157530 prefixEnd_1157530 88054705481327613666907 := by
  unfold tailWord_1157530
  simp only [CollatzResearch.WordTrace]
  refine ⟨10554646874118493807543511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28145724997649316820116029 10554646874118493807543511)
  ·
    refine ⟨15831970311177740711315267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10554646874118493807543511 15831970311177740711315267)
    ·
      refine ⟨23747955466766611066972901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15831970311177740711315267 23747955466766611066972901)
      ·
        refine ⟨4452741650018739575057419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23747955466766611066972901 4452741650018739575057419)
        ·
          refine ⟨6679112475028109362586129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4452741650018739575057419 6679112475028109362586129)
          ·
            refine ⟨5009334356271082021939597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679112475028109362586129 5009334356271082021939597)
            ·
              refine ⟨1878500383601655758227349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5009334356271082021939597 1878500383601655758227349)
              ·
                refine ⟨88054705481327613666907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1878500383601655758227349 88054705481327613666907)
                ·
                  rfl

theorem cell21_1157530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_1157530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157530 prefixEnd_1157530 := by exact prefixLift 1157530
  have htrace : WordTrace (prefixWord ++ tailWord_1157530) baseStart_1157530 baseEnd_1157530 := by
    simpa [prefixWord, tailWord_1157530, baseEnd_1157530] using wordTrace_append hprefix tailTrace_1157530
  have hstable : (prefixWord ++ tailWord_1157530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157530).length < 2 ^ (prefixWord ++ tailWord_1157530).sum := by decide
  have hdescent : baseEnd_1157530 < baseStart_1157530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157575 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 6]
def baseStart_1157575 : Nat := 118140960795 + 1157575 * 2 ^ 59
def prefixEnd_1157575 : Nat := 4983230072969 + 3 ^ 40 * 1157575 * 2
def baseEnd_1157575 : Nat := 264174386057072762750629

theorem tailTrace_1157575 : CollatzResearch.WordTrace tailWord_1157575 prefixEnd_1157575 264174386057072762750629 := by
  unfold tailWord_1157575
  simp only [CollatzResearch.WordTrace]
  refine ⟨42220228781310947915562179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28146819187540631943708119 42220228781310947915562179)
  ·
    refine ⟨63330343171966421873343269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42220228781310947915562179 63330343171966421873343269)
    ·
      refine ⟨11874439344743704101251863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63330343171966421873343269 11874439344743704101251863)
      ·
        refine ⟨17811659017115556151877795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11874439344743704101251863 17811659017115556151877795)
        ·
          refine ⟨26717488525673334227816693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17811659017115556151877795 26717488525673334227816693)
          ·
            refine ⟨2504764549281875083857815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26717488525673334227816693 2504764549281875083857815)
            ·
              refine ⟨3757146823922812625786723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504764549281875083857815 3757146823922812625786723)
              ·
                refine ⟨5635720235884218938680085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757146823922812625786723 5635720235884218938680085)
                ·
                  refine ⟨264174386057072762750629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5635720235884218938680085 264174386057072762750629)
                  ·
                    rfl

theorem cell21_1157575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_1157575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157575 prefixEnd_1157575 := by exact prefixLift 1157575
  have htrace : WordTrace (prefixWord ++ tailWord_1157575) baseStart_1157575 baseEnd_1157575 := by
    simpa [prefixWord, tailWord_1157575, baseEnd_1157575] using wordTrace_append hprefix tailTrace_1157575
  have hstable : (prefixWord ++ tailWord_1157575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157575).length < 2 ^ (prefixWord ++ tailWord_1157575).sum := by decide
  have hdescent : baseEnd_1157575 < baseStart_1157575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157637 : List Nat := [1, 3, 1, 1, 2, 2, 2, 6, 3]
def baseStart_1157637 : Nat := 118140960795 + 1157637 * 2 ^ 59
def prefixEnd_1157637 : Nat := 4983230072969 + 3 ^ 40 * 1157637 * 2
def baseEnd_1157637 : Nat := 264188535301774432717169

theorem tailTrace_1157637 : CollatzResearch.WordTrace tailWord_1157637 prefixEnd_1157637 264188535301774432717169 := by
  unfold tailWord_1157637
  simp only [CollatzResearch.WordTrace]
  refine ⟨42222490107086332504319165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28148326738057555002879443 42222490107086332504319165)
  ·
    refine ⟨15833433790157374689119687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42222490107086332504319165 15833433790157374689119687)
    ·
      refine ⟨23750150685236062033679531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15833433790157374689119687 23750150685236062033679531)
      ·
        refine ⟨35625226027854093050519297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23750150685236062033679531 35625226027854093050519297)
        ·
          refine ⟨26718919520890569787889473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35625226027854093050519297 26718919520890569787889473)
          ·
            refine ⟨20039189640667927340917105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26718919520890569787889473 20039189640667927340917105)
            ·
              refine ⟨15029392230500945505687829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20039189640667927340917105 15029392230500945505687829)
              ·
                refine ⟨704502760804731820579117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15029392230500945505687829 704502760804731820579117)
                ·
                  refine ⟨264188535301774432717169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704502760804731820579117 264188535301774432717169)
                  ·
                    rfl

theorem cell21_1157637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_1157637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157637 prefixEnd_1157637 := by exact prefixLift 1157637
  have htrace : WordTrace (prefixWord ++ tailWord_1157637) baseStart_1157637 baseEnd_1157637 := by
    simpa [prefixWord, tailWord_1157637, baseEnd_1157637] using wordTrace_append hprefix tailTrace_1157637
  have hstable : (prefixWord ++ tailWord_1157637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157637).length < 2 ^ (prefixWord ++ tailWord_1157637).sum := by decide
  have hdescent : baseEnd_1157637 < baseStart_1157637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157651 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 4]
def baseStart_1157651 : Nat := 118140960795 + 1157651 * 2 ^ 59
def prefixEnd_1157651 : Nat := 4983230072969 + 3 ^ 40 * 1157651 * 2
def baseEnd_1157651 : Nat := 264191730292513519483807

theorem tailTrace_1157651 : CollatzResearch.WordTrace tailWord_1157651 prefixEnd_1157651 264191730292513519483807 := by
  unfold tailWord_1157651
  simp only [CollatzResearch.WordTrace]
  refine ⟨42223000729035612895328807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28148667152690408596885871 42223000729035612895328807)
  ·
    refine ⟨63334501093553419342993211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42223000729035612895328807 63334501093553419342993211)
    ·
      refine ⟨95001751640330129014489817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63334501093553419342993211 95001751640330129014489817)
      ·
        refine ⟨71251313730247596760867363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95001751640330129014489817 71251313730247596760867363)
        ·
          refine ⟨106876970595371395141301045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71251313730247596760867363 106876970595371395141301045)
          ·
            refine ⟨10019715993316068294496973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106876970595371395141301045 10019715993316068294496973)
            ·
              refine ⟨3757393497493525610436365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10019715993316068294496973 3757393497493525610436365)
              ·
                refine ⟨1409022561560072103913637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3757393497493525610436365 1409022561560072103913637)
                ·
                  refine ⟨264191730292513519483807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409022561560072103913637 264191730292513519483807)
                  ·
                    rfl

theorem cell21_1157651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_1157651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157651 prefixEnd_1157651 := by exact prefixLift 1157651
  have htrace : WordTrace (prefixWord ++ tailWord_1157651) baseStart_1157651 baseEnd_1157651 := by
    simpa [prefixWord, tailWord_1157651, baseEnd_1157651] using wordTrace_append hprefix tailTrace_1157651
  have hstable : (prefixWord ++ tailWord_1157651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157651).length < 2 ^ (prefixWord ++ tailWord_1157651).sum := by decide
  have hdescent : baseEnd_1157651 < baseStart_1157651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157665 : List Nat := [1, 2, 3, 2, 2, 1, 1, 9]
def baseStart_1157665 : Nat := 118140960795 + 1157665 * 2 ^ 59
def prefixEnd_1157665 : Nat := 4983230072969 + 3 ^ 40 * 1157665 * 2
def baseEnd_1157665 : Nat := 88064975094417535416815

theorem tailTrace_1157665 : CollatzResearch.WordTrace tailWord_1157665 prefixEnd_1157665 88064975094417535416815 := by
  unfold tailWord_1157665
  simp only [CollatzResearch.WordTrace]
  refine ⟨42223511350984893286338449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28149007567323262190892299 42223511350984893286338449)
  ·
    refine ⟨31667633513238669964753837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42223511350984893286338449 31667633513238669964753837)
    ·
      refine ⟨11875362567464501236782689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31667633513238669964753837 11875362567464501236782689)
      ·
        refine ⟨8906521925598375927587017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11875362567464501236782689 8906521925598375927587017)
        ·
          refine ⟨6679891444198781945690263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8906521925598375927587017 6679891444198781945690263)
          ·
            refine ⟨10019837166298172918535395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6679891444198781945690263 10019837166298172918535395)
            ·
              refine ⟨15029755749447259377803093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10019837166298172918535395 15029755749447259377803093)
              ·
                refine ⟨88064975094417535416815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15029755749447259377803093 88064975094417535416815)
                ·
                  rfl

theorem cell21_1157665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 9].length) (baseStart_1157665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157665 prefixEnd_1157665 := by exact prefixLift 1157665
  have htrace : WordTrace (prefixWord ++ tailWord_1157665) baseStart_1157665 baseEnd_1157665 := by
    simpa [prefixWord, tailWord_1157665, baseEnd_1157665] using wordTrace_append hprefix tailTrace_1157665
  have hstable : (prefixWord ++ tailWord_1157665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157665).length < 2 ^ (prefixWord ++ tailWord_1157665).sum := by decide
  have hdescent : baseEnd_1157665 < baseStart_1157665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157806 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1157806 : Nat := 118140960795 + 1157806 * 2 ^ 59
def prefixEnd_1157806 : Nat := 4983230072969 + 3 ^ 40 * 1157806 * 2
def baseEnd_1157806 : Nat := 264227103404267694400157

theorem tailTrace_1157806 : CollatzResearch.WordTrace tailWord_1157806 prefixEnd_1157806 264227103404267694400157 := by
  unfold tailWord_1157806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5278581755434259295902659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28152436028982716244814181 5278581755434259295902659)
  ·
    refine ⟨7917872633151388943853989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5278581755434259295902659 7917872633151388943853989)
    ·
      refine ⟨1484601118715885426972623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7917872633151388943853989 1484601118715885426972623)
      ·
        refine ⟨2226901678073828140458935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484601118715885426972623 2226901678073828140458935)
        ·
          refine ⟨3340352517110742210688403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226901678073828140458935 3340352517110742210688403)
          ·
            refine ⟨5010528775666113316032605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340352517110742210688403 5010528775666113316032605)
            ·
              refine ⟨1878948290874792493512227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5010528775666113316032605 1878948290874792493512227)
              ·
                refine ⟨2818422436312188740268341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878948290874792493512227 2818422436312188740268341)
                ·
                  refine ⟨264227103404267694400157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2818422436312188740268341 264227103404267694400157)
                  ·
                    rfl

theorem cell21_1157806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1157806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157806 prefixEnd_1157806 := by exact prefixLift 1157806
  have htrace : WordTrace (prefixWord ++ tailWord_1157806) baseStart_1157806 baseEnd_1157806 := by
    simpa [prefixWord, tailWord_1157806, baseEnd_1157806] using wordTrace_append hprefix tailTrace_1157806
  have hstable : (prefixWord ++ tailWord_1157806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157806).length < 2 ^ (prefixWord ++ tailWord_1157806).sum := by decide
  have hdescent : baseEnd_1157806 < baseStart_1157806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157907 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 7]
def baseStart_1157907 : Nat := 118140960795 + 1157907 * 2 ^ 59
def prefixEnd_1157907 : Nat := 4983230072969 + 3 ^ 40 * 1157907 * 2
def baseEnd_1157907 : Nat := 264250152980313963216617

theorem tailTrace_1157907 : CollatzResearch.WordTrace tailWord_1157907 prefixEnd_1157907 264250152980313963216617 := by
  unfold tailWord_1157907
  simp only [CollatzResearch.WordTrace]
  refine ⟨42232337816108168616647975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28154891877405445744431983 42232337816108168616647975)
  ·
    refine ⟨63348506724162252924971963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42232337816108168616647975 63348506724162252924971963)
    ·
      refine ⟨95022760086243379387457945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63348506724162252924971963 95022760086243379387457945)
      ·
        refine ⟨71267070064682534540593459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95022760086243379387457945 71267070064682534540593459)
        ·
          refine ⟨106900605097023801810890189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71267070064682534540593459 106900605097023801810890189)
          ·
            refine ⟨40087726911383925679083821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106900605097023801810890189 40087726911383925679083821)
            ·
              refine ⟨15032897591768972129656433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40087726911383925679083821 15032897591768972129656433)
              ·
                refine ⟨11274673193826729097242325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15032897591768972129656433 11274673193826729097242325)
                ·
                  refine ⟨264250152980313963216617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11274673193826729097242325 264250152980313963216617)
                  ·
                    rfl

theorem cell21_1157907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_1157907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157907 prefixEnd_1157907 := by exact prefixLift 1157907
  have htrace : WordTrace (prefixWord ++ tailWord_1157907) baseStart_1157907 baseEnd_1157907 := by
    simpa [prefixWord, tailWord_1157907, baseEnd_1157907] using wordTrace_append hprefix tailTrace_1157907
  have hstable : (prefixWord ++ tailWord_1157907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157907).length < 2 ^ (prefixWord ++ tailWord_1157907).sum := by decide
  have hdescent : baseEnd_1157907 < baseStart_1157907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157930 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_1157930 : Nat := 118140960795 + 1157930 * 2 ^ 59
def prefixEnd_1157930 : Nat := 4983230072969 + 3 ^ 40 * 1157930 * 2
def baseEnd_1157930 : Nat := 264255401893671034333237

theorem tailTrace_1157930 : CollatzResearch.WordTrace tailWord_1157930 prefixEnd_1157930 264255401893671034333237 := by
  unfold tailWord_1157930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10558294173756210886183811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28155451130016562363156829 10558294173756210886183811)
  ·
    refine ⟨15837441260634316329275717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10558294173756210886183811 15837441260634316329275717)
    ·
      refine ⟨2969520236368934311739197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15837441260634316329275717 2969520236368934311739197)
      ·
        refine ⟨1113570088638350366902199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2969520236368934311739197 1113570088638350366902199)
        ·
          refine ⟨1670355132957525550353299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113570088638350366902199 1670355132957525550353299)
          ·
            refine ⟨2505532699436288325529949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670355132957525550353299 2505532699436288325529949)
            ·
              refine ⟨939574762288608122073731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2505532699436288325529949 939574762288608122073731)
              ·
                refine ⟨1409362143432912183110597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939574762288608122073731 1409362143432912183110597)
                ·
                  refine ⟨264255401893671034333237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409362143432912183110597 264255401893671034333237)
                  ·
                    rfl

theorem cell21_1157930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_1157930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1157930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1157930 prefixEnd_1157930 := by exact prefixLift 1157930
  have htrace : WordTrace (prefixWord ++ tailWord_1157930) baseStart_1157930 baseEnd_1157930 := by
    simpa [prefixWord, tailWord_1157930, baseEnd_1157930] using wordTrace_append hprefix tailTrace_1157930
  have hstable : (prefixWord ++ tailWord_1157930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157930).length < 2 ^ (prefixWord ++ tailWord_1157930).sum := by decide
  have hdescent : baseEnd_1157930 < baseStart_1157930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158059 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 5]
def baseStart_1158059 : Nat := 118140960795 + 1158059 * 2 ^ 59
def prefixEnd_1158059 : Nat := 4983230072969 + 3 ^ 40 * 1158059 * 2
def baseEnd_1158059 : Nat := 264284841451195476682973

theorem tailTrace_1158059 : CollatzResearch.WordTrace tailWord_1158059 prefixEnd_1158059 264284841451195476682973 := by
  unfold tailWord_1158059
  simp only [CollatzResearch.WordTrace]
  refine ⟨42237881711557498576181231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28158587807704999050787487 42237881711557498576181231)
  ·
    refine ⟨63356822567336247864271847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42237881711557498576181231 63356822567336247864271847)
    ·
      refine ⟨95035233851004371796407771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63356822567336247864271847 95035233851004371796407771)
      ·
        refine ⟨142552850776506557694611657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95035233851004371796407771 142552850776506557694611657)
        ·
          refine ⟨106914638082379918270958743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142552850776506557694611657 106914638082379918270958743)
          ·
            refine ⟨160371957123569877406438115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106914638082379918270958743 160371957123569877406438115)
            ·
              refine ⟨240557935685354816109657173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160371957123569877406438115 240557935685354816109657173)
              ·
                refine ⟨2819038308812751751285045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 240557935685354816109657173 2819038308812751751285045)
                ·
                  refine ⟨264284841451195476682973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819038308812751751285045 264284841451195476682973)
                  ·
                    rfl

theorem cell21_1158059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_1158059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158059 prefixEnd_1158059 := by exact prefixLift 1158059
  have htrace : WordTrace (prefixWord ++ tailWord_1158059) baseStart_1158059 baseEnd_1158059 := by
    simpa [prefixWord, tailWord_1158059, baseEnd_1158059] using wordTrace_append hprefix tailTrace_1158059
  have hstable : (prefixWord ++ tailWord_1158059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158059).length < 2 ^ (prefixWord ++ tailWord_1158059).sum := by decide
  have hdescent : baseEnd_1158059 < baseStart_1158059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158152 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_1158152 : Nat := 118140960795 + 1158152 * 2 ^ 59
def prefixEnd_1158152 : Nat := 4983230072969 + 3 ^ 40 * 1158152 * 2
def baseEnd_1158152 : Nat := 264306065318247981632783

theorem tailTrace_1158152 : CollatzResearch.WordTrace tailWord_1158152 prefixEnd_1158152 264306065318247981632783 := by
  unfold tailWord_1158152
  simp only [CollatzResearch.WordTrace]
  refine ⟨21120636850110287729658355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28160849133480383639544473 21120636850110287729658355)
  ·
    refine ⟨31680955275165431594487533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21120636850110287729658355 31680955275165431594487533)
    ·
      refine ⟨11880358228187036847932825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31680955275165431594487533 11880358228187036847932825)
      ·
        refine ⟨8910268671140277635949619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11880358228187036847932825 8910268671140277635949619)
        ·
          refine ⟨13365403006710416453924429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8910268671140277635949619 13365403006710416453924429)
          ·
            refine ⟨5012026127516406170221661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13365403006710416453924429 5012026127516406170221661)
            ·
              refine ⟨1879509797818652313833123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5012026127516406170221661 1879509797818652313833123)
              ·
                refine ⟨2819264696727978470749685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879509797818652313833123 2819264696727978470749685)
                ·
                  refine ⟨264306065318247981632783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819264696727978470749685 264306065318247981632783)
                  ·
                    rfl

theorem cell21_1158152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_1158152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158152 prefixEnd_1158152 := by exact prefixLift 1158152
  have htrace : WordTrace (prefixWord ++ tailWord_1158152) baseStart_1158152 baseEnd_1158152 := by
    simpa [prefixWord, tailWord_1158152, baseEnd_1158152] using wordTrace_append hprefix tailTrace_1158152
  have hstable : (prefixWord ++ tailWord_1158152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158152).length < 2 ^ (prefixWord ++ tailWord_1158152).sum := by decide
  have hdescent : baseEnd_1158152 < baseStart_1158152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158211 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 5]
def baseStart_1158211 : Nat := 118140960795 + 1158211 * 2 ^ 59
def prefixEnd_1158211 : Nat := 4983230072969 + 3 ^ 40 * 1158211 * 2
def baseEnd_1158211 : Nat := 264319529922076990149329

theorem tailTrace_1158211 : CollatzResearch.WordTrace tailWord_1158211 prefixEnd_1158211 264319529922076990149329 := by
  unfold tailWord_1158211
  simp only [CollatzResearch.WordTrace]
  refine ⟨42243425607006828535714487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28162283738004552357142991 42243425607006828535714487)
  ·
    refine ⟨63365138410510242803571731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42243425607006828535714487 63365138410510242803571731)
    ·
      refine ⟨95047707615765364205357597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63365138410510242803571731 95047707615765364205357597)
      ·
        refine ⟨35642890355912011577009099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95047707615765364205357597 35642890355912011577009099)
        ·
          refine ⟨53464335533868017365513649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35642890355912011577009099 53464335533868017365513649)
          ·
            refine ⟨40098251650401013024135237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53464335533868017365513649 40098251650401013024135237)
            ·
              refine ⟨7518422184450189942025357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40098251650401013024135237 7518422184450189942025357)
              ·
                refine ⟨2819408319168821228259509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7518422184450189942025357 2819408319168821228259509)
                ·
                  refine ⟨264319529922076990149329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819408319168821228259509 264319529922076990149329)
                  ·
                    rfl

theorem cell21_1158211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_1158211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158211 prefixEnd_1158211 := by exact prefixLift 1158211
  have htrace : WordTrace (prefixWord ++ tailWord_1158211) baseStart_1158211 baseEnd_1158211 := by
    simpa [prefixWord, tailWord_1158211, baseEnd_1158211] using wordTrace_append hprefix tailTrace_1158211
  have hstable : (prefixWord ++ tailWord_1158211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158211).length < 2 ^ (prefixWord ++ tailWord_1158211).sum := by decide
  have hdescent : baseEnd_1158211 < baseStart_1158211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158245 : List Nat := [1, 3, 1, 3, 2, 1, 4, 3, 3]
def baseStart_1158245 : Nat := 118140960795 + 1158245 * 2 ^ 59
def prefixEnd_1158245 : Nat := 4983230072969 + 3 ^ 40 * 1158245 * 2
def baseEnd_1158245 : Nat := 264327289185300486582593

theorem tailTrace_1158245 : CollatzResearch.WordTrace tailWord_1158245 prefixEnd_1158245 264327289185300486582593 := by
  unfold tailWord_1158245
  simp only [CollatzResearch.WordTrace]
  refine ⟨42244665688883652342452189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28163110459255768228301459 42244665688883652342452189)
  ·
    refine ⟨15841749633331369628419571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42244665688883652342452189 15841749633331369628419571)
    ·
      refine ⟨23762624449997054442629357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15841749633331369628419571 23762624449997054442629357)
      ·
        refine ⟨8910984168748895415986009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23762624449997054442629357 8910984168748895415986009)
        ·
          refine ⟨6683238126561671561989507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8910984168748895415986009 6683238126561671561989507)
          ·
            refine ⟨10024857189842507342984261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6683238126561671561989507 10024857189842507342984261)
            ·
              refine ⟨1879660723095470126809549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10024857189842507342984261 1879660723095470126809549)
              ·
                refine ⟨704872771160801297553581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1879660723095470126809549 704872771160801297553581)
                ·
                  refine ⟨264327289185300486582593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 704872771160801297553581 264327289185300486582593)
                  ·
                    rfl

theorem cell21_1158245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_1158245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158245 prefixEnd_1158245 := by exact prefixLift 1158245
  have htrace : WordTrace (prefixWord ++ tailWord_1158245) baseStart_1158245 baseEnd_1158245 := by
    simpa [prefixWord, tailWord_1158245, baseEnd_1158245] using wordTrace_append hprefix tailTrace_1158245
  have hstable : (prefixWord ++ tailWord_1158245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158245).length < 2 ^ (prefixWord ++ tailWord_1158245).sum := by decide
  have hdescent : baseEnd_1158245 < baseStart_1158245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158256 : List Nat := [2, 1, 1, 1, 5, 1, 10]
def baseStart_1158256 : Nat := 118140960795 + 1158256 * 2 ^ 59
def prefixEnd_1158256 : Nat := 4983230072969 + 3 ^ 40 * 1158256 * 2
def baseEnd_1158256 : Nat := 29369977726129656877693

theorem tailTrace_1158256 : CollatzResearch.WordTrace tailWord_1158256 prefixEnd_1158256 29369977726129656877693 := by
  unfold tailWord_1158256
  simp only [CollatzResearch.WordTrace]
  refine ⟨21122533445921900610551311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28163377927895867480735081 21122533445921900610551311)
  ·
    refine ⟨31683800168882850915826967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21122533445921900610551311 31683800168882850915826967)
    ·
      refine ⟨47525700253324276373740451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31683800168882850915826967 47525700253324276373740451)
      ·
        refine ⟨71288550379986414560610677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47525700253324276373740451 71288550379986414560610677)
        ·
          refine ⟨6683301598123726365057251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71288550379986414560610677 6683301598123726365057251)
          ·
            refine ⟨10024952397185589547585877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6683301598123726365057251 10024952397185589547585877)
            ·
              refine ⟨29369977726129656877693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10024952397185589547585877 29369977726129656877693)
              ·
                rfl

theorem cell21_1158256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 10].length) (baseStart_1158256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158256 prefixEnd_1158256 := by exact prefixLift 1158256
  have htrace : WordTrace (prefixWord ++ tailWord_1158256) baseStart_1158256 baseEnd_1158256 := by
    simpa [prefixWord, tailWord_1158256, baseEnd_1158256] using wordTrace_append hprefix tailTrace_1158256
  have hstable : (prefixWord ++ tailWord_1158256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158256).length < 2 ^ (prefixWord ++ tailWord_1158256).sum := by decide
  have hdescent : baseEnd_1158256 < baseStart_1158256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158276 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1158276 : Nat := 118140960795 + 1158276 * 2 ^ 59
def prefixEnd_1158276 : Nat := 4983230072969 + 3 ^ 40 * 1158276 * 2
def baseEnd_1158276 : Nat := 264334363807651321565863

theorem tailTrace_1158276 : CollatzResearch.WordTrace tailWord_1158276 prefixEnd_1158276 264334363807651321565863 := by
  unfold tailWord_1158276
  simp only [CollatzResearch.WordTrace]
  refine ⟨21122898175885672318415341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28163864234514229757887121 21122898175885672318415341)
  ·
    refine ⟨7921086815957127119405753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21122898175885672318415341 7921086815957127119405753)
    ·
      refine ⟨5940815111967845339554315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7921086815957127119405753 5940815111967845339554315)
      ·
        refine ⟨8911222667951768009331473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5940815111967845339554315 8911222667951768009331473)
        ·
          refine ⟨6683417000963826006998605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8911222667951768009331473 6683417000963826006998605)
          ·
            refine ⟨2506281375361434752624477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6683417000963826006998605 2506281375361434752624477)
            ·
              refine ⟨939855515760538032234179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2506281375361434752624477 939855515760538032234179)
              ·
                refine ⟨1409783273640807048351269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939855515760538032234179 1409783273640807048351269)
                ·
                  refine ⟨264334363807651321565863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409783273640807048351269 264334363807651321565863)
                  ·
                    rfl

theorem cell21_1158276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1158276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158276 prefixEnd_1158276 := by exact prefixLift 1158276
  have htrace : WordTrace (prefixWord ++ tailWord_1158276) baseStart_1158276 baseEnd_1158276 := by
    simpa [prefixWord, tailWord_1158276, baseEnd_1158276] using wordTrace_append hprefix tailTrace_1158276
  have hstable : (prefixWord ++ tailWord_1158276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158276).length < 2 ^ (prefixWord ++ tailWord_1158276).sum := by decide
  have hdescent : baseEnd_1158276 < baseStart_1158276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158290 : List Nat := [3, 2, 3, 1, 1, 2, 4, 5]
def baseStart_1158290 : Nat := 118140960795 + 1158290 * 2 ^ 59
def prefixEnd_1158290 : Nat := 4983230072969 + 3 ^ 40 * 1158290 * 2
def baseEnd_1158290 : Nat := 88112519599463469444167

theorem tailTrace_1158290 : CollatzResearch.WordTrace tailWord_1158290 prefixEnd_1158290 88112519599463469444167 := by
  unfold tailWord_1158290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561576743430156256960081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28164204649147083351893549 10561576743430156256960081)
  ·
    refine ⟨7921182557572617192720061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10561576743430156256960081 7921182557572617192720061)
    ·
      refine ⟨2970443459089731447270023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7921182557572617192720061 2970443459089731447270023)
      ·
        refine ⟨4455665188634597170905035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970443459089731447270023 4455665188634597170905035)
        ·
          refine ⟨6683497782951895756357553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455665188634597170905035 6683497782951895756357553)
          ·
            refine ⟨5012623337213921817268165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6683497782951895756357553 5012623337213921817268165)
            ·
              refine ⟨939866875727610340737781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5012623337213921817268165 939866875727610340737781)
              ·
                refine ⟨88112519599463469444167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 939866875727610340737781 88112519599463469444167)
                ·
                  rfl

theorem cell21_1158290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_1158290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158290 prefixEnd_1158290 := by exact prefixLift 1158290
  have htrace : WordTrace (prefixWord ++ tailWord_1158290) baseStart_1158290 baseEnd_1158290 := by
    simpa [prefixWord, tailWord_1158290, baseEnd_1158290] using wordTrace_append hprefix tailTrace_1158290
  have hstable : (prefixWord ++ tailWord_1158290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158290).length < 2 ^ (prefixWord ++ tailWord_1158290).sum := by decide
  have hdescent : baseEnd_1158290 < baseStart_1158290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158321 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 5]
def baseStart_1158321 : Nat := 118140960795 + 1158321 * 2 ^ 59
def prefixEnd_1158321 : Nat := 4983230072969 + 3 ^ 40 * 1158321 * 2
def baseEnd_1158321 : Nat := 264344633420741243315771

theorem tailTrace_1158321 : CollatzResearch.WordTrace tailWord_1158321 prefixEnd_1158321 264344633420741243315771 := by
  unfold tailWord_1158321
  simp only [CollatzResearch.WordTrace]
  refine ⟨42247437636608317322218817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28164958424405544881479211 42247437636608317322218817)
  ·
    refine ⟨31685578227456237991664113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42247437636608317322218817 31685578227456237991664113)
    ·
      refine ⟨23764183670592178493748085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31685578227456237991664113 23764183670592178493748085)
      ·
        refine ⟨2227892219118016733788883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23764183670592178493748085 2227892219118016733788883)
        ·
          refine ⟨3341838328677025100683325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227892219118016733788883 3341838328677025100683325)
          ·
            refine ⟨1253189373253884412756247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3341838328677025100683325 1253189373253884412756247)
            ·
              refine ⟨1879784059880826619134371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253189373253884412756247 1879784059880826619134371)
              ·
                refine ⟨2819676089821239928701557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879784059880826619134371 2819676089821239928701557)
                ·
                  refine ⟨264344633420741243315771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819676089821239928701557 264344633420741243315771)
                  ·
                    rfl

theorem cell21_1158321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_1158321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158321 prefixEnd_1158321 := by exact prefixLift 1158321
  have htrace : WordTrace (prefixWord ++ tailWord_1158321) baseStart_1158321 baseEnd_1158321 := by
    simpa [prefixWord, tailWord_1158321, baseEnd_1158321] using wordTrace_append hprefix tailTrace_1158321
  have hstable : (prefixWord ++ tailWord_1158321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158321).length < 2 ^ (prefixWord ++ tailWord_1158321).sum := by decide
  have hdescent : baseEnd_1158321 < baseStart_1158321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158335 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 4]
def baseStart_1158335 : Nat := 118140960795 + 1158335 * 2 ^ 59
def prefixEnd_1158335 : Nat := 4983230072969 + 3 ^ 40 * 1158335 * 2
def baseEnd_1158335 : Nat := 264347828411480330082409

theorem tailTrace_1158335 : CollatzResearch.WordTrace tailWord_1158335 prefixEnd_1158335 264347828411480330082409 := by
  unfold tailWord_1158335
  simp only [CollatzResearch.WordTrace]
  refine ⟨42247948258557597713228459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28165298839038398475485639 42247948258557597713228459)
  ·
    refine ⟨63371922387836396569842689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42247948258557597713228459 63371922387836396569842689)
    ·
      refine ⟨47528941790877297427382017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63371922387836396569842689 47528941790877297427382017)
      ·
        refine ⟨35646706343157973070536513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47528941790877297427382017 35646706343157973070536513)
        ·
          refine ⟨26735029757368479802902385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35646706343157973070536513 26735029757368479802902385)
          ·
            refine ⟨20051272318026359852176789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26735029757368479802902385 20051272318026359852176789)
            ·
              refine ⟨939903389907485618070787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20051272318026359852176789 939903389907485618070787)
              ·
                refine ⟨1409855084861228427106181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939903389907485618070787 1409855084861228427106181)
                ·
                  refine ⟨264347828411480330082409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409855084861228427106181 264347828411480330082409)
                  ·
                    rfl

theorem cell21_1158335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 4].length) (baseStart_1158335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158335 prefixEnd_1158335 := by exact prefixLift 1158335
  have htrace : WordTrace (prefixWord ++ tailWord_1158335) baseStart_1158335 baseEnd_1158335 := by
    simpa [prefixWord, tailWord_1158335, baseEnd_1158335] using wordTrace_append hprefix tailTrace_1158335
  have hstable : (prefixWord ++ tailWord_1158335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158335).length < 2 ^ (prefixWord ++ tailWord_1158335).sum := by decide
  have hdescent : baseEnd_1158335 < baseStart_1158335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158394 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1158394 : Nat := 118140960795 + 1158394 * 2 ^ 59
def prefixEnd_1158394 : Nat := 4983230072969 + 3 ^ 40 * 1158394 * 2
def baseEnd_1158394 : Nat := 264361293015309338598955

theorem tailTrace_1158394 : CollatzResearch.WordTrace tailWord_1158394 prefixEnd_1158394 264361293015309338598955 := by
  unfold tailWord_1158394
  simp only [CollatzResearch.WordTrace]
  refine ⟨10562525041335962697406559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28166733443562567193084157 10562525041335962697406559)
  ·
    refine ⟨15843787562003944046109839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10562525041335962697406559 15843787562003944046109839)
    ·
      refine ⟨23765681343005916069164759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15843787562003944046109839 23765681343005916069164759)
      ·
        refine ⟨35648522014508874103747139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23765681343005916069164759 35648522014508874103747139)
        ·
          refine ⟨53472783021763311155620709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35648522014508874103747139 53472783021763311155620709)
          ·
            refine ⟨10026146816580620841678883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53472783021763311155620709 10026146816580620841678883)
            ·
              refine ⟨15039220224870931262518325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10026146816580620841678883 15039220224870931262518325)
              ·
                refine ⟨1409926896081649805861093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15039220224870931262518325 1409926896081649805861093)
                ·
                  refine ⟨264361293015309338598955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409926896081649805861093 264361293015309338598955)
                  ·
                    rfl

theorem cell21_1158394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1158394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158394 prefixEnd_1158394 := by exact prefixLift 1158394
  have htrace : WordTrace (prefixWord ++ tailWord_1158394) baseStart_1158394 baseEnd_1158394 := by
    simpa [prefixWord, tailWord_1158394, baseEnd_1158394] using wordTrace_append hprefix tailTrace_1158394
  have hstable : (prefixWord ++ tailWord_1158394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158394).length < 2 ^ (prefixWord ++ tailWord_1158394).sum := by decide
  have hdescent : baseEnd_1158394 < baseStart_1158394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158445 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1158445 : Nat := 118140960795 + 1158445 * 2 ^ 59
def prefixEnd_1158445 : Nat := 4983230072969 + 3 ^ 40 * 1158445 * 2
def baseEnd_1158445 : Nat := 264372931910144583248851

theorem tailTrace_1158445 : CollatzResearch.WordTrace tailWord_1158445 prefixEnd_1158445 264372931910144583248851 := by
  unfold tailWord_1158445
  simp only [CollatzResearch.WordTrace]
  refine ⟨42251960288159086499732789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28167973525439390999821859 42251960288159086499732789)
  ·
    refine ⟨3961121277014914359349949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42251960288159086499732789 3961121277014914359349949)
    ·
      refine ⟨1485420478880592884756231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3961121277014914359349949 1485420478880592884756231)
      ·
        refine ⟨2228130718320889327134347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485420478880592884756231 2228130718320889327134347)
        ·
          refine ⟨3342196077481333990701521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228130718320889327134347 3342196077481333990701521)
          ·
            refine ⟨2506647058111000493026141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342196077481333990701521 2506647058111000493026141)
            ·
              refine ⟨939992646791625184884803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2506647058111000493026141 939992646791625184884803)
              ·
                refine ⟨1409988970187437777327205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939992646791625184884803 1409988970187437777327205)
                ·
                  refine ⟨264372931910144583248851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409988970187437777327205 264372931910144583248851)
                  ·
                    rfl

theorem cell21_1158445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1158445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158445 prefixEnd_1158445 := by exact prefixLift 1158445
  have htrace : WordTrace (prefixWord ++ tailWord_1158445) baseStart_1158445 baseEnd_1158445 := by
    simpa [prefixWord, tailWord_1158445, baseEnd_1158445] using wordTrace_append hprefix tailTrace_1158445
  have hstable : (prefixWord ++ tailWord_1158445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158445).length < 2 ^ (prefixWord ++ tailWord_1158445).sum := by decide
  have hdescent : baseEnd_1158445 < baseStart_1158445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158549 : List Nat := [1, 3, 2, 1, 1, 2, 6, 2, 3]
def baseStart_1158549 : Nat := 118140960795 + 1158549 * 2 ^ 59
def prefixEnd_1158549 : Nat := 4983230072969 + 3 ^ 40 * 1158549 * 2
def baseEnd_1158549 : Nat := 264396666127063513515305

theorem tailTrace_1158549 : CollatzResearch.WordTrace tailWord_1158549 prefixEnd_1158549 264396666127063513515305 := by
  unfold tailWord_1158549
  simp only [CollatzResearch.WordTrace]
  refine ⟨42255753479782312261518701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28170502319854874841012467 42255753479782312261518701)
  ·
    refine ⟨15845907554918367098069513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42255753479782312261518701 15845907554918367098069513)
    ·
      refine ⟨11884430666188775323552135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15845907554918367098069513 11884430666188775323552135)
      ·
        refine ⟨17826645999283162985328203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11884430666188775323552135 17826645999283162985328203)
        ·
          refine ⟨26739968998924744477992305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17826645999283162985328203 26739968998924744477992305)
          ·
            refine ⟨20054976749193558358494229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26739968998924744477992305 20054976749193558358494229)
            ·
              refine ⟨940077035118448048054417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20054976749193558358494229 940077035118448048054417)
              ·
                refine ⟨705057776338836036040813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940077035118448048054417 705057776338836036040813)
                ·
                  refine ⟨264396666127063513515305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705057776338836036040813 264396666127063513515305)
                  ·
                    rfl

theorem cell21_1158549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_1158549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158549 prefixEnd_1158549 := by exact prefixLift 1158549
  have htrace : WordTrace (prefixWord ++ tailWord_1158549) baseStart_1158549 baseEnd_1158549 := by
    simpa [prefixWord, tailWord_1158549, baseEnd_1158549] using wordTrace_append hprefix tailTrace_1158549
  have hstable : (prefixWord ++ tailWord_1158549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158549).length < 2 ^ (prefixWord ++ tailWord_1158549).sum := by decide
  have hdescent : baseEnd_1158549 < baseStart_1158549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158577 : List Nat := [1, 2, 2, 4, 1, 1, 5, 5]
def baseStart_1158577 : Nat := 118140960795 + 1158577 * 2 ^ 59
def prefixEnd_1158577 : Nat := 4983230072969 + 3 ^ 40 * 1158577 * 2
def baseEnd_1158577 : Nat := 88134352036180562349527

theorem tailTrace_1158577 : CollatzResearch.WordTrace tailWord_1158577 prefixEnd_1158577 88134352036180562349527 := by
  unfold tailWord_1158577
  simp only [CollatzResearch.WordTrace]
  refine ⟨42256774723680873043537985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28171183149120582029025323 42256774723680873043537985)
  ·
    refine ⟨31692581042760654782653489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42256774723680873043537985 31692581042760654782653489)
    ·
      refine ⟨23769435782070491086990117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31692581042760654782653489 23769435782070491086990117)
      ·
        refine ⟨4456769209138217078810647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23769435782070491086990117 4456769209138217078810647)
        ·
          refine ⟨6685153813707325618215971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456769209138217078810647 6685153813707325618215971)
          ·
            refine ⟨10027730720560988427323957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6685153813707325618215971 10027730720560988427323957)
            ·
              refine ⟨940099755052592665061621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10027730720560988427323957 940099755052592665061621)
              ·
                refine ⟨88134352036180562349527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 940099755052592665061621 88134352036180562349527)
                ·
                  rfl

theorem cell21_1158577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 5].length) (baseStart_1158577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158577 prefixEnd_1158577 := by exact prefixLift 1158577
  have htrace : WordTrace (prefixWord ++ tailWord_1158577) baseStart_1158577 baseEnd_1158577 := by
    simpa [prefixWord, tailWord_1158577, baseEnd_1158577] using wordTrace_append hprefix tailTrace_1158577
  have hstable : (prefixWord ++ tailWord_1158577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158577).length < 2 ^ (prefixWord ++ tailWord_1158577).sum := by decide
  have hdescent : baseEnd_1158577 < baseStart_1158577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158642 : List Nat := [3, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_1158642 : Nat := 118140960795 + 1158642 * 2 ^ 59
def prefixEnd_1158642 : Nat := 4983230072969 + 3 ^ 40 * 1158642 * 2
def baseEnd_1158642 : Nat := 264417889994116018465115

theorem tailTrace_1158642 : CollatzResearch.WordTrace tailWord_1158642 prefixEnd_1158642 264417889994116018465115 := by
  unfold tailWord_1158642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10564786367111347286163545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28172763645630259429769453 10564786367111347286163545)
  ·
    refine ⟨7923589775333510464622659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10564786367111347286163545 7923589775333510464622659)
    ·
      refine ⟨11885384663000265696933989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7923589775333510464622659 11885384663000265696933989)
      ·
        refine ⟨2228509624312549818175123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11885384663000265696933989 2228509624312549818175123)
        ·
          refine ⟨3342764436468824727262685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228509624312549818175123 3342764436468824727262685)
          ·
            refine ⟨1253536663675809272723507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3342764436468824727262685 1253536663675809272723507)
            ·
              refine ⟨1880304995513713909085261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253536663675809272723507 1880304995513713909085261)
              ·
                refine ⟨705114373317642715906973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1880304995513713909085261 705114373317642715906973)
                ·
                  refine ⟨264417889994116018465115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705114373317642715906973 264417889994116018465115)
                  ·
                    rfl

theorem cell21_1158642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_1158642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158642 prefixEnd_1158642 := by exact prefixLift 1158642
  have htrace : WordTrace (prefixWord ++ tailWord_1158642) baseStart_1158642 baseEnd_1158642 := by
    simpa [prefixWord, tailWord_1158642, baseEnd_1158642] using wordTrace_append hprefix tailTrace_1158642
  have hstable : (prefixWord ++ tailWord_1158642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158642).length < 2 ^ (prefixWord ++ tailWord_1158642).sum := by decide
  have hdescent : baseEnd_1158642 < baseStart_1158642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158743 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 5]
def baseStart_1158743 : Nat := 118140960795 + 1158743 * 2 ^ 59
def prefixEnd_1158743 : Nat := 4983230072969 + 3 ^ 40 * 1158743 * 2
def baseEnd_1158743 : Nat := 264440939570162287281575

theorem tailTrace_1158743 : CollatzResearch.WordTrace tailWord_1158743 prefixEnd_1158743 264440939570162287281575 := by
  unfold tailWord_1158743
  simp only [CollatzResearch.WordTrace]
  refine ⟨42262829241079483394080883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28175219494052988929387255 42262829241079483394080883)
  ·
    refine ⟨63394243861619225091121325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42262829241079483394080883 63394243861619225091121325)
    ·
      refine ⟨23772841448107209409170497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63394243861619225091121325 23772841448107209409170497)
      ·
        refine ⟨17829631086080407056877873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23772841448107209409170497 17829631086080407056877873)
        ·
          refine ⟨13372223314560305292658405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17829631086080407056877873 13372223314560305292658405)
          ·
            refine ⟨2507291871480057242373451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13372223314560305292658405 2507291871480057242373451)
            ·
              refine ⟨3760937807220085863560177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507291871480057242373451 3760937807220085863560177)
              ·
                refine ⟨2820703355415064397670133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3760937807220085863560177 2820703355415064397670133)
                ·
                  refine ⟨264440939570162287281575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820703355415064397670133 264440939570162287281575)
                  ·
                    rfl

theorem cell21_1158743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_1158743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158743 prefixEnd_1158743 := by exact prefixLift 1158743
  have htrace : WordTrace (prefixWord ++ tailWord_1158743) baseStart_1158743 baseEnd_1158743 := by
    simpa [prefixWord, tailWord_1158743, baseEnd_1158743] using wordTrace_append hprefix tailTrace_1158743
  have hstable : (prefixWord ++ tailWord_1158743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158743).length < 2 ^ (prefixWord ++ tailWord_1158743).sum := by decide
  have hdescent : baseEnd_1158743 < baseStart_1158743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158791 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 4]
def baseStart_1158791 : Nat := 118140960795 + 1158791 * 2 ^ 59
def prefixEnd_1158791 : Nat := 4983230072969 + 3 ^ 40 * 1158791 * 2
def baseEnd_1158791 : Nat := 264451893824124870481477

theorem tailTrace_1158791 : CollatzResearch.WordTrace tailWord_1158791 prefixEnd_1158791 264451893824124870481477 := by
  unfold tailWord_1158791
  simp only [CollatzResearch.WordTrace]
  refine ⟨42264579944905587591828227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28176386629937058394552151 42264579944905587591828227)
  ·
    refine ⟨63396869917358381387742341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42264579944905587591828227 63396869917358381387742341)
    ·
      refine ⟨11886913109504696510201689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63396869917358381387742341 11886913109504696510201689)
      ·
        refine ⟨8915184832128522382651267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11886913109504696510201689 8915184832128522382651267)
        ·
          refine ⟨13372777248192783573976901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8915184832128522382651267 13372777248192783573976901)
          ·
            refine ⟨2507395734036146920120669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13372777248192783573976901 2507395734036146920120669)
            ·
              refine ⟨940273400263555095045251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2507395734036146920120669 940273400263555095045251)
              ·
                refine ⟨1410410100395332642567877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940273400263555095045251 1410410100395332642567877)
                ·
                  refine ⟨264451893824124870481477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410410100395332642567877 264451893824124870481477)
                  ·
                    rfl

theorem cell21_1158791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 4].length) (baseStart_1158791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158791 prefixEnd_1158791 := by exact prefixLift 1158791
  have htrace : WordTrace (prefixWord ++ tailWord_1158791) baseStart_1158791 baseEnd_1158791 := by
    simpa [prefixWord, tailWord_1158791, baseEnd_1158791] using wordTrace_append hprefix tailTrace_1158791
  have hstable : (prefixWord ++ tailWord_1158791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158791).length < 2 ^ (prefixWord ++ tailWord_1158791).sum := by decide
  have hdescent : baseEnd_1158791 < baseStart_1158791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158887 : List Nat := [1, 1, 5, 4, 1, 2, 2, 2, 3]
def baseStart_1158887 : Nat := 118140960795 + 1158887 * 2 ^ 59
def prefixEnd_1158887 : Nat := 4983230072969 + 3 ^ 40 * 1158887 * 2
def baseEnd_1158887 : Nat := 264473802332050036881281

theorem tailTrace_1158887 : CollatzResearch.WordTrace tailWord_1158887 prefixEnd_1158887 264473802332050036881281 := by
  unfold tailWord_1158887
  simp only [CollatzResearch.WordTrace]
  refine ⟨42268081352557795987322915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28178720901705197324881943 42268081352557795987322915)
  ·
    refine ⟨63402122028836693980984373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42268081352557795987322915 63402122028836693980984373)
    ·
      refine ⟨5943948940203440060717285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63402122028836693980984373 5943948940203440060717285)
      ·
        refine ⟨1114490426288145011384491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5943948940203440060717285 1114490426288145011384491)
        ·
          refine ⟨1671735639432217517076737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114490426288145011384491 1671735639432217517076737)
          ·
            refine ⟨1253801729574163137807553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1671735639432217517076737 1253801729574163137807553)
            ·
              refine ⟨940351297180622353355665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253801729574163137807553 940351297180622353355665)
              ·
                refine ⟨705263472885466765016749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940351297180622353355665 705263472885466765016749)
                ·
                  refine ⟨264473802332050036881281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705263472885466765016749 264473802332050036881281)
                  ·
                    rfl

theorem cell21_1158887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 3].length) (baseStart_1158887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158887 prefixEnd_1158887 := by exact prefixLift 1158887
  have htrace : WordTrace (prefixWord ++ tailWord_1158887) baseStart_1158887 baseEnd_1158887 := by
    simpa [prefixWord, tailWord_1158887, baseEnd_1158887] using wordTrace_append hprefix tailTrace_1158887
  have hstable : (prefixWord ++ tailWord_1158887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158887).length < 2 ^ (prefixWord ++ tailWord_1158887).sum := by decide
  have hdescent : baseEnd_1158887 < baseStart_1158887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158923 : List Nat := [1, 1, 1, 1, 5, 1, 2, 9]
def baseStart_1158923 : Nat := 118140960795 + 1158923 * 2 ^ 59
def prefixEnd_1158923 : Nat := 4983230072969 + 3 ^ 40 * 1158923 * 2
def baseEnd_1158923 : Nat := 88160672674173991427069

theorem tailTrace_1158923 : CollatzResearch.WordTrace tailWord_1158923 prefixEnd_1158923 88160672674173991427069 := by
  unfold tailWord_1158923
  simp only [CollatzResearch.WordTrace]
  refine ⟨42269394380427374135633423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28179596253618249423755615 42269394380427374135633423)
  ·
    refine ⟨63404091570641061203450135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42269394380427374135633423 63404091570641061203450135)
    ·
      refine ⟨95106137355961591805175203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63404091570641061203450135 95106137355961591805175203)
      ·
        refine ⟨142659206033942387707762805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95106137355961591805175203 142659206033942387707762805)
        ·
          refine ⟨13374300565682098847602763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142659206033942387707762805 13374300565682098847602763)
          ·
            refine ⟨20061450848523148271404145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13374300565682098847602763 20061450848523148271404145)
            ·
              refine ⟨15046088136392361203553109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20061450848523148271404145 15046088136392361203553109)
              ·
                refine ⟨88160672674173991427069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15046088136392361203553109 88160672674173991427069)
                ·
                  rfl

theorem cell21_1158923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_1158923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158923 prefixEnd_1158923 := by exact prefixLift 1158923
  have htrace : WordTrace (prefixWord ++ tailWord_1158923) baseStart_1158923 baseEnd_1158923 := by
    simpa [prefixWord, tailWord_1158923, baseEnd_1158923] using wordTrace_append hprefix tailTrace_1158923
  have hstable : (prefixWord ++ tailWord_1158923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158923).length < 2 ^ (prefixWord ++ tailWord_1158923).sum := by decide
  have hdescent : baseEnd_1158923 < baseStart_1158923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158974 : List Nat := [4, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1158974 : Nat := 118140960795 + 1158974 * 2 ^ 59
def prefixEnd_1158974 : Nat := 4983230072969 + 3 ^ 40 * 1158974 * 2
def baseEnd_1158974 : Nat := 88164552305785739643701

theorem tailTrace_1158974 : CollatzResearch.WordTrace tailWord_1158974 prefixEnd_1158974 88164552305785739643701 := by
  unfold tailWord_1158974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283906812905326230717497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28180836335495073230493317 5283906812905326230717497)
  ·
    refine ⟨3962930109678994673038123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5283906812905326230717497 3962930109678994673038123)
    ·
      refine ⟨5944395164518492009557185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962930109678994673038123 5944395164518492009557185)
      ·
        refine ⟨4458296373388869007167889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5944395164518492009557185 4458296373388869007167889)
        ·
          refine ⟨3343722280041651755375917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4458296373388869007167889 3343722280041651755375917)
          ·
            refine ⟨1253895855015619408265969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3343722280041651755375917 1253895855015619408265969)
            ·
              refine ⟨940421891261714556199477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253895855015619408265969 940421891261714556199477)
              ·
                refine ⟨88164552305785739643701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 940421891261714556199477 88164552305785739643701)
                ·
                  rfl

theorem cell21_1158974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1158974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1158974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1158974 prefixEnd_1158974 := by exact prefixLift 1158974
  have htrace : WordTrace (prefixWord ++ tailWord_1158974) baseStart_1158974 baseEnd_1158974 := by
    simpa [prefixWord, tailWord_1158974, baseEnd_1158974] using wordTrace_append hprefix tailTrace_1158974
  have hstable : (prefixWord ++ tailWord_1158974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158974).length < 2 ^ (prefixWord ++ tailWord_1158974).sum := by decide
  have hdescent : baseEnd_1158974 < baseStart_1158974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159016 : List Nat := [2, 1, 4, 2, 1, 1, 4, 6]
def baseStart_1159016 : Nat := 118140960795 + 1159016 * 2 ^ 59
def prefixEnd_1159016 : Nat := 4983230072969 + 3 ^ 40 * 1159016 * 2
def baseEnd_1159016 : Nat := 88167747296524826410339

theorem tailTrace_1159016 : CollatzResearch.WordTrace tailWord_1159016 prefixEnd_1159016 88167747296524826410339 := by
  unfold tailWord_1159016
  simp only [CollatzResearch.WordTrace]
  refine ⟨21136393184545225509384451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28181857579393634012512601 21136393184545225509384451)
  ·
    refine ⟨31704589776817838264076677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21136393184545225509384451 31704589776817838264076677)
    ·
      refine ⟨5944610583153344674514377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31704589776817838264076677 5944610583153344674514377)
      ·
        refine ⟨4458457937365008505885783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5944610583153344674514377 4458457937365008505885783)
        ·
          refine ⟨6687686906047512758828675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458457937365008505885783 6687686906047512758828675)
          ·
            refine ⟨10031530359071269138243013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6687686906047512758828675 10031530359071269138243013)
            ·
              refine ⟨1880911942325862963420565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10031530359071269138243013 1880911942325862963420565)
              ·
                refine ⟨88167747296524826410339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1880911942325862963420565 88167747296524826410339)
                ·
                  rfl

theorem cell21_1159016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_1159016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159016 prefixEnd_1159016 := by exact prefixLift 1159016
  have htrace : WordTrace (prefixWord ++ tailWord_1159016) baseStart_1159016 baseEnd_1159016 := by
    simpa [prefixWord, tailWord_1159016, baseEnd_1159016] using wordTrace_append hprefix tailTrace_1159016
  have hstable : (prefixWord ++ tailWord_1159016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159016).length < 2 ^ (prefixWord ++ tailWord_1159016).sum := by decide
  have hdescent : baseEnd_1159016 < baseStart_1159016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159137 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 4]
def baseStart_1159137 : Nat := 118140960795 + 1159137 * 2 ^ 59
def prefixEnd_1159137 : Nat := 4983230072969 + 3 ^ 40 * 1159137 * 2
def baseEnd_1159137 : Nat := 264530855738105157714103

theorem tailTrace_1159137 : CollatzResearch.WordTrace tailWord_1159137 prefixEnd_1159137 264530855738105157714103 := by
  unfold tailWord_1159137
  simp only [CollatzResearch.WordTrace]
  refine ⟨42277199601652088683923665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28184799734434725789282443 42277199601652088683923665)
  ·
    refine ⟨31707899701239066512942749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42277199601652088683923665 31707899701239066512942749)
    ·
      refine ⟨11890462387964649942353531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31707899701239066512942749 11890462387964649942353531)
      ·
        refine ⟨17835693581946974913530297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11890462387964649942353531 17835693581946974913530297)
        ·
          refine ⟨13376770186460231185147723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17835693581946974913530297 13376770186460231185147723)
          ·
            refine ⟨20065155279690346777721585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13376770186460231185147723 20065155279690346777721585)
            ·
              refine ⟨15048866459767760083291189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20065155279690346777721585 15048866459767760083291189)
              ·
                refine ⟨1410831230603227507808549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15048866459767760083291189 1410831230603227507808549)
                ·
                  refine ⟨264530855738105157714103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410831230603227507808549 264530855738105157714103)
                  ·
                    rfl

theorem cell21_1159137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_1159137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159137 prefixEnd_1159137 := by exact prefixLift 1159137
  have htrace : WordTrace (prefixWord ++ tailWord_1159137) baseStart_1159137 baseEnd_1159137 := by
    simpa [prefixWord, tailWord_1159137, baseEnd_1159137] using wordTrace_append hprefix tailTrace_1159137
  have hstable : (prefixWord ++ tailWord_1159137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159137).length < 2 ^ (prefixWord ++ tailWord_1159137).sum := by decide
  have hdescent : baseEnd_1159137 < baseStart_1159137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159151 : List Nat := [1, 1, 2, 1, 4, 2, 3, 7]
def baseStart_1159151 : Nat := 118140960795 + 1159151 * 2 ^ 59
def prefixEnd_1159151 : Nat := 4983230072969 + 3 ^ 40 * 1159151 * 2
def baseEnd_1159151 : Nat := 88178016909614748160247

theorem tailTrace_1159151 : CollatzResearch.WordTrace tailWord_1159151 prefixEnd_1159151 88178016909614748160247 := by
  unfold tailWord_1159151
  simp only [CollatzResearch.WordTrace]
  refine ⟨42277710223601369074933307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28185140149067579383288871 42277710223601369074933307)
  ·
    refine ⟨63416565335402053612399961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42277710223601369074933307 63416565335402053612399961)
    ·
      refine ⟨47562424001551540209299971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63416565335402053612399961 47562424001551540209299971)
      ·
        refine ⟨71343636002327310313949957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47562424001551540209299971 71343636002327310313949957)
        ·
          refine ⟨13376931750436370683865617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71343636002327310313949957 13376931750436370683865617)
          ·
            refine ⟨10032698812827278012899213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13376931750436370683865617 10032698812827278012899213)
            ·
              refine ⟨3762262054810229254837205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10032698812827278012899213 3762262054810229254837205)
              ·
                refine ⟨88178016909614748160247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3762262054810229254837205 88178016909614748160247)
                ·
                  rfl

theorem cell21_1159151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_1159151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159151 prefixEnd_1159151 := by exact prefixLift 1159151
  have htrace : WordTrace (prefixWord ++ tailWord_1159151) baseStart_1159151 baseEnd_1159151 := by
    simpa [prefixWord, tailWord_1159151, baseEnd_1159151] using wordTrace_append hprefix tailTrace_1159151
  have hstable : (prefixWord ++ tailWord_1159151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159151).length < 2 ^ (prefixWord ++ tailWord_1159151).sum := by decide
  have hdescent : baseEnd_1159151 < baseStart_1159151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159188 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1159188 : Nat := 118140960795 + 1159188 * 2 ^ 59
def prefixEnd_1159188 : Nat := 4983230072969 + 3 ^ 40 * 1159188 * 2
def baseEnd_1159188 : Nat := 264542494632940402363999

theorem tailTrace_1159188 : CollatzResearch.WordTrace tailWord_1159188 prefixEnd_1159188 264542494632940402363999 := by
  unfold tailWord_1159188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21139529862233662197015109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28186039816311549596020145 21139529862233662197015109)
  ·
    refine ⟨3963661849168811661940333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21139529862233662197015109 3963661849168811661940333)
    ·
      refine ⟨1486373193438304373227625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3963661849168811661940333 1486373193438304373227625)
      ·
        refine ⟨1114779895078728279920719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1486373193438304373227625 1114779895078728279920719)
        ·
          refine ⟨1672169842618092419881079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114779895078728279920719 1672169842618092419881079)
          ·
            refine ⟨2508254763927138629821619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672169842618092419881079 2508254763927138629821619)
            ·
              refine ⟨3762382145890707944732429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508254763927138629821619 3762382145890707944732429)
              ·
                refine ⟨1410893304709015479274661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3762382145890707944732429 1410893304709015479274661)
                ·
                  refine ⟨264542494632940402363999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410893304709015479274661 264542494632940402363999)
                  ·
                    rfl

theorem cell21_1159188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1159188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159188 prefixEnd_1159188 := by exact prefixLift 1159188
  have htrace : WordTrace (prefixWord ++ tailWord_1159188) baseStart_1159188 baseEnd_1159188 := by
    simpa [prefixWord, tailWord_1159188, baseEnd_1159188] using wordTrace_append hprefix tailTrace_1159188
  have hstable : (prefixWord ++ tailWord_1159188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159188).length < 2 ^ (prefixWord ++ tailWord_1159188).sum := by decide
  have hdescent : baseEnd_1159188 < baseStart_1159188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159233 : List Nat := [1, 2, 5, 1, 2, 1, 4, 2, 3]
def baseStart_1159233 : Nat := 118140960795 + 1159233 * 2 ^ 59
def prefixEnd_1159233 : Nat := 4983230072969 + 3 ^ 40 * 1159233 * 2
def baseEnd_1159233 : Nat := 264552764246030324113907

theorem tailTrace_1159233 : CollatzResearch.WordTrace tailWord_1159233 prefixEnd_1159233 264552764246030324113907 := by
  unfold tailWord_1159233
  simp only [CollatzResearch.WordTrace]
  refine ⟨42280701009304297079418353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28187134006202864719612235 42280701009304297079418353)
  ·
    refine ⟨31710525756978222809563765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42280701009304297079418353 31710525756978222809563765)
    ·
      refine ⟨2972861789716708388396603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31710525756978222809563765 2972861789716708388396603)
      ·
        refine ⟨4459292684575062582594905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972861789716708388396603 4459292684575062582594905)
        ·
          refine ⟨3344469513431296936946179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4459292684575062582594905 3344469513431296936946179)
          ·
            refine ⟨5016704270146945405419269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344469513431296936946179 5016704270146945405419269)
            ·
              refine ⟨940632050652552263516113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5016704270146945405419269 940632050652552263516113)
              ·
                refine ⟨705474037989414197637085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940632050652552263516113 705474037989414197637085)
                ·
                  refine ⟨264552764246030324113907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705474037989414197637085 264552764246030324113907)
                  ·
                    rfl

theorem cell21_1159233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_1159233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159233 prefixEnd_1159233 := by exact prefixLift 1159233
  have htrace : WordTrace (prefixWord ++ tailWord_1159233) baseStart_1159233 baseEnd_1159233 := by
    simpa [prefixWord, tailWord_1159233, baseEnd_1159233] using wordTrace_append hprefix tailTrace_1159233
  have hstable : (prefixWord ++ tailWord_1159233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159233).length < 2 ^ (prefixWord ++ tailWord_1159233).sum := by decide
  have hdescent : baseEnd_1159233 < baseStart_1159233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159258 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1159258 : Nat := 118140960795 + 1159258 * 2 ^ 59
def prefixEnd_1159258 : Nat := 4983230072969 + 3 ^ 40 * 1159258 * 2
def baseEnd_1159258 : Nat := 264558469586635836197189

theorem tailTrace_1159258 : CollatzResearch.WordTrace tailWord_1159258 prefixEnd_1159258 264558469586635836197189 := by
  unfold tailWord_1159258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10570403208553431587269607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28187741889475817566052285 10570403208553431587269607)
  ·
    refine ⟨15855604812830147380904411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10570403208553431587269607 15855604812830147380904411)
    ·
      refine ⟨23783407219245221071356617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15855604812830147380904411 23783407219245221071356617)
      ·
        refine ⟨17837555414433915803517463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23783407219245221071356617 17837555414433915803517463)
        ·
          refine ⟨26756333121650873705276195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17837555414433915803517463 26756333121650873705276195)
          ·
            refine ⟨40134499682476310557914293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26756333121650873705276195 40134499682476310557914293)
            ·
              refine ⟨3762609345232154114804465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40134499682476310557914293 3762609345232154114804465)
              ·
                refine ⟨2821957008924115586103349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3762609345232154114804465 2821957008924115586103349)
                ·
                  refine ⟨264558469586635836197189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2821957008924115586103349 264558469586635836197189)
                  ·
                    rfl

theorem cell21_1159258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1159258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159258 prefixEnd_1159258 := by exact prefixLift 1159258
  have htrace : WordTrace (prefixWord ++ tailWord_1159258) baseStart_1159258 baseEnd_1159258 := by
    simpa [prefixWord, tailWord_1159258, baseEnd_1159258] using wordTrace_append hprefix tailTrace_1159258
  have hstable : (prefixWord ++ tailWord_1159258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159258).length < 2 ^ (prefixWord ++ tailWord_1159258).sum := by decide
  have hdescent : baseEnd_1159258 < baseStart_1159258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159289 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 6]
def baseStart_1159289 : Nat := 118140960795 + 1159289 * 2 ^ 59
def prefixEnd_1159289 : Nat := 4983230072969 + 3 ^ 40 * 1159289 * 2
def baseEnd_1159289 : Nat := 264565544208986671180459

theorem tailTrace_1159289 : CollatzResearch.WordTrace tailWord_1159289 prefixEnd_1159289 264565544208986671180459 := by
  unfold tailWord_1159289
  simp only [CollatzResearch.WordTrace]
  refine ⟨42282743497101418643456921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28188495664734279095637947 42282743497101418643456921)
  ·
    refine ⟨31712057622826063982592691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42282743497101418643456921 31712057622826063982592691)
    ·
      refine ⟨47568086434239095973889037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31712057622826063982592691 47568086434239095973889037)
      ·
        refine ⟨17838032412839660990208389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47568086434239095973889037 17838032412839660990208389)
        ·
          refine ⟨3344631077407436435664073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17838032412839660990208389 3344631077407436435664073)
          ·
            refine ⟨2508473308055577326748055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3344631077407436435664073 2508473308055577326748055)
            ·
              refine ⟨3762709962083365990122083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508473308055577326748055 3762709962083365990122083)
              ·
                refine ⟨5644064943125048985183125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762709962083365990122083 5644064943125048985183125)
                ·
                  refine ⟨264565544208986671180459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5644064943125048985183125 264565544208986671180459)
                  ·
                    rfl

theorem cell21_1159289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_1159289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159289 prefixEnd_1159289 := by exact prefixLift 1159289
  have htrace : WordTrace (prefixWord ++ tailWord_1159289) baseStart_1159289 baseEnd_1159289 := by
    simpa [prefixWord, tailWord_1159289, baseEnd_1159289] using wordTrace_append hprefix tailTrace_1159289
  have hstable : (prefixWord ++ tailWord_1159289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159289).length < 2 ^ (prefixWord ++ tailWord_1159289).sum := by decide
  have hdescent : baseEnd_1159289 < baseStart_1159289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159320 : List Nat := [2, 1, 2, 4, 3, 1, 1, 7]
def baseStart_1159320 : Nat := 118140960795 + 1159320 * 2 ^ 59
def prefixEnd_1159320 : Nat := 4983230072969 + 3 ^ 40 * 1159320 * 2
def baseEnd_1159320 : Nat := 88190872943779168721243

theorem tailTrace_1159320 : CollatzResearch.WordTrace tailWord_1159320 prefixEnd_1159320 88190872943779168721243 := by
  unfold tailWord_1159320
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141937079994555468917707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28189249439992740625223609 21141937079994555468917707)
  ·
    refine ⟨31712905619991833203376561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21141937079994555468917707 31712905619991833203376561)
    ·
      refine ⟨23784679214993874902532421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31712905619991833203376561 23784679214993874902532421)
      ·
        refine ⟨4459627352811351544224829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23784679214993874902532421 4459627352811351544224829)
        ·
          refine ⟨1672360257304256829084311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4459627352811351544224829 1672360257304256829084311)
          ·
            refine ⟨2508540385956385243626467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672360257304256829084311 2508540385956385243626467)
            ·
              refine ⟨3762810578934577865439701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508540385956385243626467 3762810578934577865439701)
              ·
                refine ⟨88190872943779168721243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3762810578934577865439701 88190872943779168721243)
                ·
                  rfl

theorem cell21_1159320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_1159320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159320 prefixEnd_1159320 := by exact prefixLift 1159320
  have htrace : WordTrace (prefixWord ++ tailWord_1159320) baseStart_1159320 baseEnd_1159320 := by
    simpa [prefixWord, tailWord_1159320, baseEnd_1159320] using wordTrace_append hprefix tailTrace_1159320
  have hstable : (prefixWord ++ tailWord_1159320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159320).length < 2 ^ (prefixWord ++ tailWord_1159320).sum := by decide
  have hdescent : baseEnd_1159320 < baseStart_1159320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159326 : List Nat := [4, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1159326 : Nat := 118140960795 + 1159326 * 2 ^ 59
def prefixEnd_1159326 : Nat := 4983230072969 + 3 ^ 40 * 1159326 * 2
def baseEnd_1159326 : Nat := 264573988113082829063717

theorem tailTrace_1159326 : CollatzResearch.WordTrace tailWord_1159326 prefixEnd_1159326 264573988113082829063717 := by
  unfold tailWord_1159326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5285511624745921745319229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28189395331978249308369221 5285511624745921745319229)
  ·
    refine ⟨1982066859279720654494711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5285511624745921745319229 1982066859279720654494711)
    ·
      refine ⟨2973100288919580981742067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982066859279720654494711 2973100288919580981742067)
      ·
        refine ⟨4459650433379371472613101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973100288919580981742067 4459650433379371472613101)
        ·
          refine ⟨1672368912517264302229913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4459650433379371472613101 1672368912517264302229913)
          ·
            refine ⟨1254276684387948226672435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672368912517264302229913 1254276684387948226672435)
            ·
              refine ⟨1881415026581922340008653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254276684387948226672435 1881415026581922340008653)
              ·
                refine ⟨705530634968220877503245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1881415026581922340008653 705530634968220877503245)
                ·
                  refine ⟨264573988113082829063717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705530634968220877503245 264573988113082829063717)
                  ·
                    rfl

theorem cell21_1159326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1159326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159326 prefixEnd_1159326 := by exact prefixLift 1159326
  have htrace : WordTrace (prefixWord ++ tailWord_1159326) baseStart_1159326 baseEnd_1159326 := by
    simpa [prefixWord, tailWord_1159326, baseEnd_1159326] using wordTrace_append hprefix tailTrace_1159326
  have hstable : (prefixWord ++ tailWord_1159326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159326).length < 2 ^ (prefixWord ++ tailWord_1159326).sum := by decide
  have hdescent : baseEnd_1159326 < baseStart_1159326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159351 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 5]
def baseStart_1159351 : Nat := 118140960795 + 1159351 * 2 ^ 59
def prefixEnd_1159351 : Nat := 4983230072969 + 3 ^ 40 * 1159351 * 2
def baseEnd_1159351 : Nat := 264579693453688341146999

theorem tailTrace_1159351 : CollatzResearch.WordTrace tailWord_1159351 prefixEnd_1159351 264579693453688341146999 := by
  unfold tailWord_1159351
  simp only [CollatzResearch.WordTrace]
  refine ⟨42285004822876803232213907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28190003215251202154809271 42285004822876803232213907)
  ·
    refine ⟨63427507234315204848320861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42285004822876803232213907 63427507234315204848320861)
    ·
      refine ⟨23785315212868201818120323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63427507234315204848320861 23785315212868201818120323)
      ·
        refine ⟨35677972819302302727180485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23785315212868201818120323 35677972819302302727180485)
        ·
          refine ⟨6689619903619181761346341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35677972819302302727180485 6689619903619181761346341)
          ·
            refine ⟨1254303731928596580252439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6689619903619181761346341 1254303731928596580252439)
            ·
              refine ⟨1881455597892894870378659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254303731928596580252439 1881455597892894870378659)
              ·
                refine ⟨2822183396839342305567989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881455597892894870378659 2822183396839342305567989)
                ·
                  refine ⟨264579693453688341146999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2822183396839342305567989 264579693453688341146999)
                  ·
                    rfl

theorem cell21_1159351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5].length) (baseStart_1159351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159351 prefixEnd_1159351 := by exact prefixLift 1159351
  have htrace : WordTrace (prefixWord ++ tailWord_1159351) baseStart_1159351 baseEnd_1159351 := by
    simpa [prefixWord, tailWord_1159351, baseEnd_1159351] using wordTrace_append hprefix tailTrace_1159351
  have hstable : (prefixWord ++ tailWord_1159351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159351).length < 2 ^ (prefixWord ++ tailWord_1159351).sum := by decide
  have hdescent : baseEnd_1159351 < baseStart_1159351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159455 : List Nat := [1, 1, 2, 4, 3, 2, 8]
def baseStart_1159455 : Nat := 118140960795 + 1159455 * 2 ^ 59
def prefixEnd_1159455 : Nat := 4983230072969 + 3 ^ 40 * 1159455 * 2
def baseEnd_1159455 : Nat := 29400380852289696823717

theorem tailTrace_1159455 : CollatzResearch.WordTrace tailWord_1159455 prefixEnd_1159455 29400380852289696823717 := by
  unfold tailWord_1159455
  simp only [CollatzResearch.WordTrace]
  refine ⟨42288798014500028993999819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28192532009666685995999879 42288798014500028993999819)
  ·
    refine ⟨63433197021750043490999729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42288798014500028993999819 63433197021750043490999729)
    ·
      refine ⟨47574897766312532618249797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63433197021750043490999729 47574897766312532618249797)
      ·
        refine ⟨8920293331183599865921837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47574897766312532618249797 8920293331183599865921837)
        ·
          refine ⟨3345109999193849949720689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8920293331183599865921837 3345109999193849949720689)
          ·
            refine ⟨2508832499395387462290517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3345109999193849949720689 2508832499395387462290517)
            ·
              refine ⟨29400380852289696823717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2508832499395387462290517 29400380852289696823717)
              ·
                rfl

theorem cell21_1159455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 8].length) (baseStart_1159455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159455 prefixEnd_1159455 := by exact prefixLift 1159455
  have htrace : WordTrace (prefixWord ++ tailWord_1159455) baseStart_1159455 baseEnd_1159455 := by
    simpa [prefixWord, tailWord_1159455, baseEnd_1159455] using wordTrace_append hprefix tailTrace_1159455
  have hstable : (prefixWord ++ tailWord_1159455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159455).length < 2 ^ (prefixWord ++ tailWord_1159455).sum := by decide
  have hdescent : baseEnd_1159455 < baseStart_1159455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159458 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1159458 : Nat := 118140960795 + 1159458 * 2 ^ 59
def prefixEnd_1159458 : Nat := 4983230072969 + 3 ^ 40 * 1159458 * 2
def baseEnd_1159458 : Nat := 264604112311479932863447

theorem tailTrace_1159458 : CollatzResearch.WordTrace tailWord_1159458 prefixEnd_1159458 264604112311479932863447 := by
  unfold tailWord_1159458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10572226858372290126589757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28192604955659440337572685 10572226858372290126589757)
  ·
    refine ⟨3964585071889608797471159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10572226858372290126589757 3964585071889608797471159)
    ·
      refine ⟨5946877607834413196206739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964585071889608797471159 5946877607834413196206739)
      ·
        refine ⟨8920316411751619794310109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946877607834413196206739 8920316411751619794310109)
        ·
          refine ⟨3345118654406857422866291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8920316411751619794310109 3345118654406857422866291)
          ·
            refine ⟨5017677981610286134299437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345118654406857422866291 5017677981610286134299437)
            ·
              refine ⟨1881629243103857300362289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5017677981610286134299437 1881629243103857300362289)
              ·
                refine ⟨1411221932327892975271717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881629243103857300362289 1411221932327892975271717)
                ·
                  refine ⟨264604112311479932863447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411221932327892975271717 264604112311479932863447)
                  ·
                    rfl

theorem cell21_1159458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1159458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159458 prefixEnd_1159458 := by exact prefixLift 1159458
  have htrace : WordTrace (prefixWord ++ tailWord_1159458) baseStart_1159458 baseEnd_1159458 := by
    simpa [prefixWord, tailWord_1159458, baseEnd_1159458] using wordTrace_append hprefix tailTrace_1159458
  have hstable : (prefixWord ++ tailWord_1159458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159458).length < 2 ^ (prefixWord ++ tailWord_1159458).sum := by decide
  have hdescent : baseEnd_1159458 < baseStart_1159458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159500 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1159500 : Nat := 118140960795 + 1159500 * 2 ^ 59
def prefixEnd_1159500 : Nat := 4983230072969 + 3 ^ 40 * 1159500 * 2
def baseEnd_1159500 : Nat := 264613697283697193163361

theorem tailTrace_1159500 : CollatzResearch.WordTrace tailWord_1159500 prefixEnd_1159500 264613697283697193163361 := by
  unfold tailWord_1159500
  simp only [CollatzResearch.WordTrace]
  refine ⟨21145219649668500839693977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28193626199558001119591969 21145219649668500839693977)
  ·
    refine ⟨15858914737251375629770483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21145219649668500839693977 15858914737251375629770483)
    ·
      refine ⟨23788372105877063444655725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15858914737251375629770483 23788372105877063444655725)
      ·
        refine ⟨8920639539703898791745897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23788372105877063444655725 8920639539703898791745897)
        ·
          refine ⟨6690479654777924093809423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8920639539703898791745897 6690479654777924093809423)
          ·
            refine ⟨10035719482166886140714135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6690479654777924093809423 10035719482166886140714135)
            ·
              refine ⟨15053579223250329211071203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10035719482166886140714135 15053579223250329211071203)
              ·
                refine ⟨22580368834875493816606805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15053579223250329211071203 22580368834875493816606805)
                ·
                  refine ⟨264613697283697193163361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22580368834875493816606805 264613697283697193163361)
                  ·
                    rfl

theorem cell21_1159500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1159500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159500 prefixEnd_1159500 := by exact prefixLift 1159500
  have htrace : WordTrace (prefixWord ++ tailWord_1159500) baseStart_1159500 baseEnd_1159500 := by
    simpa [prefixWord, tailWord_1159500, baseEnd_1159500] using wordTrace_append hprefix tailTrace_1159500
  have hstable : (prefixWord ++ tailWord_1159500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159500).length < 2 ^ (prefixWord ++ tailWord_1159500).sum := by decide
  have hdescent : baseEnd_1159500 < baseStart_1159500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159520 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 5]
def baseStart_1159520 : Nat := 118140960795 + 1159520 * 2 ^ 59
def prefixEnd_1159520 : Nat := 4983230072969 + 3 ^ 40 * 1159520 * 2
def baseEnd_1159520 : Nat := 264618261556181602829987

theorem tailTrace_1159520 : CollatzResearch.WordTrace tailWord_1159520 prefixEnd_1159520 264618261556181602829987 := by
  unfold tailWord_1159520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21145584379632272547558007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28194112506176363396744009 21145584379632272547558007)
  ·
    refine ⟨31718376569448408821337011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21145584379632272547558007 31718376569448408821337011)
    ·
      refine ⟨47577564854172613232005517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31718376569448408821337011 47577564854172613232005517)
      ·
        refine ⟨17841586820314729962002069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47577564854172613232005517 17841586820314729962002069)
        ·
          refine ⟨836324382202252966968847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17841586820314729962002069 836324382202252966968847)
          ·
            refine ⟨1254486573303379450453271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836324382202252966968847 1254486573303379450453271)
            ·
              refine ⟨1881729859955069175679907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254486573303379450453271 1881729859955069175679907)
              ·
                refine ⟨2822594789932603763519861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881729859955069175679907 2822594789932603763519861)
                ·
                  refine ⟨264618261556181602829987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2822594789932603763519861 264618261556181602829987)
                  ·
                    rfl

theorem cell21_1159520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_1159520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159520 prefixEnd_1159520 := by exact prefixLift 1159520
  have htrace : WordTrace (prefixWord ++ tailWord_1159520) baseStart_1159520 baseEnd_1159520 := by
    simpa [prefixWord, tailWord_1159520, baseEnd_1159520] using wordTrace_append hprefix tailTrace_1159520
  have hstable : (prefixWord ++ tailWord_1159520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159520).length < 2 ^ (prefixWord ++ tailWord_1159520).sum := by decide
  have hdescent : baseEnd_1159520 < baseStart_1159520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159545 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 7]
def baseStart_1159545 : Nat := 118140960795 + 1159545 * 2 ^ 59
def prefixEnd_1159545 : Nat := 4983230072969 + 3 ^ 40 * 1159545 * 2
def baseEnd_1159545 : Nat := 264623966896787114913269

theorem tailTrace_1159545 : CollatzResearch.WordTrace tailWord_1159545 prefixEnd_1159545 264623966896787114913269 := by
  unfold tailWord_1159545
  simp only [CollatzResearch.WordTrace]
  refine ⟨42292080584173974364776089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28194720389449316243184059 42292080584173974364776089)
  ·
    refine ⟨31719060438130480773582067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42292080584173974364776089 31719060438130480773582067)
    ·
      refine ⟨47578590657195721160373101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31719060438130480773582067 47578590657195721160373101)
      ·
        refine ⟨17841971496448395435139913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47578590657195721160373101 17841971496448395435139913)
        ·
          refine ⟨13381478622336296576354935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17841971496448395435139913 13381478622336296576354935)
          ·
            refine ⟨20072217933504444864532403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13381478622336296576354935 20072217933504444864532403)
            ·
              refine ⟨30108326900256667296798605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20072217933504444864532403 30108326900256667296798605)
              ·
                refine ⟨11290622587596250236299477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30108326900256667296798605 11290622587596250236299477)
                ·
                  refine ⟨264623966896787114913269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11290622587596250236299477 264623966896787114913269)
                  ·
                    rfl

theorem cell21_1159545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_1159545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159545 prefixEnd_1159545 := by exact prefixLift 1159545
  have htrace : WordTrace (prefixWord ++ tailWord_1159545) baseStart_1159545 baseEnd_1159545 := by
    simpa [prefixWord, tailWord_1159545, baseEnd_1159545] using wordTrace_append hprefix tailTrace_1159545
  have hstable : (prefixWord ++ tailWord_1159545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159545).length < 2 ^ (prefixWord ++ tailWord_1159545).sum := by decide
  have hdescent : baseEnd_1159545 < baseStart_1159545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159697 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 5]
def baseStart_1159697 : Nat := 118140960795 + 1159697 * 2 ^ 59
def prefixEnd_1159697 : Nat := 4983230072969 + 3 ^ 40 * 1159697 * 2
def baseEnd_1159697 : Nat := 264658655367668628379625

theorem tailTrace_1159697 : CollatzResearch.WordTrace tailWord_1159697 prefixEnd_1159697 264658655367668628379625 := by
  unfold tailWord_1159697
  simp only [CollatzResearch.WordTrace]
  refine ⟨42297624479623304324309345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28198416319748869549539563 42297624479623304324309345)
  ·
    refine ⟨31723218359717478243232009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42297624479623304324309345 31723218359717478243232009)
    ·
      refine ⟨23792413769788108682424007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31723218359717478243232009 23792413769788108682424007)
      ·
        refine ⟨35688620654682163023636011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23792413769788108682424007 35688620654682163023636011)
        ·
          refine ⟨53532930982023244535454017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35688620654682163023636011 53532930982023244535454017)
          ·
            refine ⟨40149698236517433401590513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53532930982023244535454017 40149698236517433401590513)
            ·
              refine ⟨30112273677388075051192885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40149698236517433401590513 30112273677388075051192885)
              ·
                refine ⟨2823025657255132036049333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30112273677388075051192885 2823025657255132036049333)
                ·
                  refine ⟨264658655367668628379625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2823025657255132036049333 264658655367668628379625)
                  ·
                    rfl

theorem cell21_1159697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_1159697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159697 prefixEnd_1159697 := by exact prefixLift 1159697
  have htrace : WordTrace (prefixWord ++ tailWord_1159697) baseStart_1159697 baseEnd_1159697 := by
    simpa [prefixWord, tailWord_1159697, baseEnd_1159697] using wordTrace_append hprefix tailTrace_1159697
  have hstable : (prefixWord ++ tailWord_1159697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159697).length < 2 ^ (prefixWord ++ tailWord_1159697).sum := by decide
  have hdescent : baseEnd_1159697 < baseStart_1159697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159700 : List Nat := [2, 4, 3, 1, 1, 1, 1, 8]
def baseStart_1159700 : Nat := 118140960795 + 1159700 * 2 ^ 59
def prefixEnd_1159700 : Nat := 4983230072969 + 3 ^ 40 * 1159700 * 2
def baseEnd_1159700 : Nat := 88219780002847096609873

theorem tailTrace_1159700 : CollatzResearch.WordTrace tailWord_1159700 prefixEnd_1159700 88219780002847096609873 := by
  unfold tailWord_1159700
  simp only [CollatzResearch.WordTrace]
  refine ⟨21148866949306217918334277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28198489265741623891112369 21148866949306217918334277)
  ·
    refine ⟨3965412552994915859687677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21148866949306217918334277 3965412552994915859687677)
    ·
      refine ⟨1487029707373093447382879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3965412552994915859687677 1487029707373093447382879)
      ·
        refine ⟨2230544561059640171074319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487029707373093447382879 2230544561059640171074319)
        ·
          refine ⟨3345816841589460256611479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2230544561059640171074319 3345816841589460256611479)
          ·
            refine ⟨5018725262384190384917219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345816841589460256611479 5018725262384190384917219)
            ·
              refine ⟨7528087893576285577375829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5018725262384190384917219 7528087893576285577375829)
              ·
                refine ⟨88219780002847096609873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7528087893576285577375829 88219780002847096609873)
                ·
                  rfl

theorem cell21_1159700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_1159700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159700 prefixEnd_1159700 := by exact prefixLift 1159700
  have htrace : WordTrace (prefixWord ++ tailWord_1159700) baseStart_1159700 baseEnd_1159700 := by
    simpa [prefixWord, tailWord_1159700, baseEnd_1159700] using wordTrace_append hprefix tailTrace_1159700
  have hstable : (prefixWord ++ tailWord_1159700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159700).length < 2 ^ (prefixWord ++ tailWord_1159700).sum := by decide
  have hdescent : baseEnd_1159700 < baseStart_1159700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159745 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 4]
def baseStart_1159745 : Nat := 118140960795 + 1159745 * 2 ^ 59
def prefixEnd_1159745 : Nat := 4983230072969 + 3 ^ 40 * 1159745 * 2
def baseEnd_1159745 : Nat := 264669609621631211579527

theorem tailTrace_1159745 : CollatzResearch.WordTrace tailWord_1159745 prefixEnd_1159745 264669609621631211579527 := by
  unfold tailWord_1159745
  simp only [CollatzResearch.WordTrace]
  refine ⟨42299375183449408522056689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28199583455632939014704459 42299375183449408522056689)
  ·
    refine ⟨31724531387587056391542517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42299375183449408522056689 31724531387587056391542517)
    ·
      refine ⟨2974174817586286536707111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31724531387587056391542517 2974174817586286536707111)
      ·
        refine ⟨4461262226379429805060667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974174817586286536707111 4461262226379429805060667)
        ·
          refine ⟨6691893339569144707591001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4461262226379429805060667 6691893339569144707591001)
          ·
            refine ⟨5018920004676858530693251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6691893339569144707591001 5018920004676858530693251)
            ·
              refine ⟨7528380007015287796039877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5018920004676858530693251 7528380007015287796039877)
              ·
                refine ⟨1411571251315366461757477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7528380007015287796039877 1411571251315366461757477)
                ·
                  refine ⟨264669609621631211579527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411571251315366461757477 264669609621631211579527)
                  ·
                    rfl

theorem cell21_1159745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_1159745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159745 prefixEnd_1159745 := by exact prefixLift 1159745
  have htrace : WordTrace (prefixWord ++ tailWord_1159745) baseStart_1159745 baseEnd_1159745 := by
    simpa [prefixWord, tailWord_1159745, baseEnd_1159745] using wordTrace_append hprefix tailTrace_1159745
  have hstable : (prefixWord ++ tailWord_1159745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159745).length < 2 ^ (prefixWord ++ tailWord_1159745).sum := by decide
  have hdescent : baseEnd_1159745 < baseStart_1159745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159841 : List Nat := [1, 2, 3, 3, 4, 1, 1, 3, 3]
def baseStart_1159841 : Nat := 118140960795 + 1159841 * 2 ^ 59
def prefixEnd_1159841 : Nat := 4983230072969 + 3 ^ 40 * 1159841 * 2
def baseEnd_1159841 : Nat := 264691518129556377979331

theorem tailTrace_1159841 : CollatzResearch.WordTrace tailWord_1159841 prefixEnd_1159841 264691518129556377979331 := by
  unfold tailWord_1159841
  simp only [CollatzResearch.WordTrace]
  refine ⟨42302876591101616917551377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28201917727401077945034251 42302876591101616917551377)
  ·
    refine ⟨31727157443326212688163533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42302876591101616917551377 31727157443326212688163533)
    ·
      refine ⟨11897684041247329758061325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31727157443326212688163533 11897684041247329758061325)
      ·
        refine ⟨4461631515467748659272997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11897684041247329758061325 4461631515467748659272997)
        ·
          refine ⟨836555909150202873613687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4461631515467748659272997 836555909150202873613687)
          ·
            refine ⟨1254833863725304310420531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836555909150202873613687 1254833863725304310420531)
            ·
              refine ⟨1882250795587956465630797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254833863725304310420531 1882250795587956465630797)
              ·
                refine ⟨705844048345483674611549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1882250795587956465630797 705844048345483674611549)
                ·
                  refine ⟨264691518129556377979331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705844048345483674611549 264691518129556377979331)
                  ·
                    rfl

theorem cell21_1159841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_1159841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159841 prefixEnd_1159841 := by exact prefixLift 1159841
  have htrace : WordTrace (prefixWord ++ tailWord_1159841) baseStart_1159841 baseEnd_1159841 := by
    simpa [prefixWord, tailWord_1159841, baseEnd_1159841] using wordTrace_append hprefix tailTrace_1159841
  have hstable : (prefixWord ++ tailWord_1159841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159841).length < 2 ^ (prefixWord ++ tailWord_1159841).sum := by decide
  have hdescent : baseEnd_1159841 < baseStart_1159841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159939 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 8]
def baseStart_1159939 : Nat := 118140960795 + 1159939 * 2 ^ 59
def prefixEnd_1159939 : Nat := 4983230072969 + 3 ^ 40 * 1159939 * 2
def baseEnd_1159939 : Nat := 264713883064729985345797

theorem tailTrace_1159939 : CollatzResearch.WordTrace tailWord_1159939 prefixEnd_1159939 264713883064729985345797 := by
  unfold tailWord_1159939
  simp only [CollatzResearch.WordTrace]
  refine ⟨42306450944746579654618871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28204300629831053103079247 42306450944746579654618871)
  ·
    refine ⟨63459676417119869481928307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42306450944746579654618871 63459676417119869481928307)
    ·
      refine ⟨95189514625679804222892461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63459676417119869481928307 95189514625679804222892461)
      ·
        refine ⟨35696067984629926583584673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95189514625679804222892461 35696067984629926583584673)
        ·
          refine ⟨26772050988472444937688505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35696067984629926583584673 26772050988472444937688505)
          ·
            refine ⟨20079038241354333703266379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26772050988472444937688505 20079038241354333703266379)
            ·
              refine ⟨30118557362031500554899569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20079038241354333703266379 30118557362031500554899569)
              ·
                refine ⟨22588918021523625416174677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30118557362031500554899569 22588918021523625416174677)
                ·
                  refine ⟨264713883064729985345797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22588918021523625416174677 264713883064729985345797)
                  ·
                    rfl

theorem cell21_1159939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_1159939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1159939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1159939 prefixEnd_1159939 := by exact prefixLift 1159939
  have htrace : WordTrace (prefixWord ++ tailWord_1159939) baseStart_1159939 baseEnd_1159939 := by
    simpa [prefixWord, tailWord_1159939, baseEnd_1159939] using wordTrace_append hprefix tailTrace_1159939
  have hstable : (prefixWord ++ tailWord_1159939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159939).length < 2 ^ (prefixWord ++ tailWord_1159939).sum := by decide
  have hdescent : baseEnd_1159939 < baseStart_1159939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160032 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_1160032 : Nat := 118140960795 + 1160032 * 2 ^ 59
def prefixEnd_1160032 : Nat := 4983230072969 + 3 ^ 40 * 1160032 * 2
def baseEnd_1160032 : Nat := 264735106931782490295607

theorem tailTrace_1160032 : CollatzResearch.WordTrace tailWord_1160032 prefixEnd_1160032 264735106931782490295607 := by
  unfold tailWord_1160032
  simp only [CollatzResearch.WordTrace]
  refine ⟨21154921466704828268877175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28206561955606437691836233 21154921466704828268877175)
  ·
    refine ⟨31732382200057242403315763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21154921466704828268877175 31732382200057242403315763)
    ·
      refine ⟨47598573300085863604973645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31732382200057242403315763 47598573300085863604973645)
      ·
        refine ⟨17849464987532198851865117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47598573300085863604973645 17849464987532198851865117)
        ·
          refine ⟨6693549370324574569449419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17849464987532198851865117 6693549370324574569449419)
          ·
            refine ⟨10040324055486861854174129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6693549370324574569449419 10040324055486861854174129)
            ·
              refine ⟨7530243041615146390630597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10040324055486861854174129 7530243041615146390630597)
              ·
                refine ⟨1411920570302839948243237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7530243041615146390630597 1411920570302839948243237)
                ·
                  refine ⟨264735106931782490295607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411920570302839948243237 264735106931782490295607)
                  ·
                    rfl

theorem cell21_1160032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_1160032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160032 prefixEnd_1160032 := by exact prefixLift 1160032
  have htrace : WordTrace (prefixWord ++ tailWord_1160032) baseStart_1160032 baseEnd_1160032 := by
    simpa [prefixWord, tailWord_1160032, baseEnd_1160032] using wordTrace_append hprefix tailTrace_1160032
  have hstable : (prefixWord ++ tailWord_1160032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160032).length < 2 ^ (prefixWord ++ tailWord_1160032).sum := by decide
  have hdescent : baseEnd_1160032 < baseStart_1160032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160049 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 4]
def baseStart_1160049 : Nat := 118140960795 + 1160049 * 2 ^ 59
def prefixEnd_1160049 : Nat := 4983230072969 + 3 ^ 40 * 1160049 * 2
def baseEnd_1160049 : Nat := 264738986563394238512239

theorem tailTrace_1160049 : CollatzResearch.WordTrace tailWord_1160049 prefixEnd_1160049 264738986563394238512239 := by
  unfold tailWord_1160049
  simp only [CollatzResearch.WordTrace]
  refine ⟨42310462974348068441123201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28206975316232045627415467 42310462974348068441123201)
  ·
    refine ⟨31732847230761051330842401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42310462974348068441123201 31732847230761051330842401)
    ·
      refine ⟨23799635423070788498131801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31732847230761051330842401 23799635423070788498131801)
      ·
        refine ⟨17849726567303091373598851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23799635423070788498131801 17849726567303091373598851)
        ·
          refine ⟨26774589850954637060398277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17849726567303091373598851 26774589850954637060398277)
          ·
            refine ⟨5020235597053994448824677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26774589850954637060398277 5020235597053994448824677)
            ·
              refine ⟨941294174447623959154627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5020235597053994448824677 941294174447623959154627)
              ·
                refine ⟨1411941261671435938731941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941294174447623959154627 1411941261671435938731941)
                ·
                  refine ⟨264738986563394238512239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411941261671435938731941 264738986563394238512239)
                  ·
                    rfl

theorem cell21_1160049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_1160049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160049 prefixEnd_1160049 := by exact prefixLift 1160049
  have htrace : WordTrace (prefixWord ++ tailWord_1160049) baseStart_1160049 baseEnd_1160049 := by
    simpa [prefixWord, tailWord_1160049, baseEnd_1160049] using wordTrace_append hprefix tailTrace_1160049
  have hstable : (prefixWord ++ tailWord_1160049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160049).length < 2 ^ (prefixWord ++ tailWord_1160049).sum := by decide
  have hdescent : baseEnd_1160049 < baseStart_1160049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160086 : List Nat := [5, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1160086 : Nat := 118140960795 + 1160086 * 2 ^ 59
def prefixEnd_1160086 : Nat := 4983230072969 + 3 ^ 40 * 1160086 * 2
def baseEnd_1160086 : Nat := 264747430467490396395497

theorem tailTrace_1160086 : CollatzResearch.WordTrace tailWord_1160086 prefixEnd_1160086 264747430467490396395497 := by
  unfold tailWord_1160086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644488279700876485013757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28207874983476015840146741 2644488279700876485013757)
  ·
    refine ⟨991683104887828681880159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2644488279700876485013757 991683104887828681880159)
    ·
      refine ⟨1487524657331743022820239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 991683104887828681880159 1487524657331743022820239)
      ·
        refine ⟨2231286985997614534230359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487524657331743022820239 2231286985997614534230359)
        ·
          refine ⟨3346930478996421801345539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231286985997614534230359 3346930478996421801345539)
          ·
            refine ⟨5020395718494632702018309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346930478996421801345539 5020395718494632702018309)
            ·
              refine ⟨941324197217743631628433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5020395718494632702018309 941324197217743631628433)
              ·
                refine ⟨705993147913307723721325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941324197217743631628433 705993147913307723721325)
                ·
                  refine ⟨264747430467490396395497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705993147913307723721325 264747430467490396395497)
                  ·
                    rfl

theorem cell21_1160086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1160086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160086 prefixEnd_1160086 := by exact prefixLift 1160086
  have htrace : WordTrace (prefixWord ++ tailWord_1160086) baseStart_1160086 baseEnd_1160086 := by
    simpa [prefixWord, tailWord_1160086, baseEnd_1160086] using wordTrace_append hprefix tailTrace_1160086
  have hstable : (prefixWord ++ tailWord_1160086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160086).length < 2 ^ (prefixWord ++ tailWord_1160086).sum := by decide
  have hdescent : baseEnd_1160086 < baseStart_1160086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160134 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1160134 : Nat := 118140960795 + 1160134 * 2 ^ 59
def prefixEnd_1160134 : Nat := 4983230072969 + 3 ^ 40 * 1160134 * 2
def baseEnd_1160134 : Nat := 264758384721452979595399

theorem tailTrace_1160134 : CollatzResearch.WordTrace tailWord_1160134 prefixEnd_1160134 264758384721452979595399 := by
  unfold tailWord_1160134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322298849345003998686483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28209042119360085305311637 1322298849345003998686483)
  ·
    refine ⟨1983448274017505998029725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322298849345003998686483 1983448274017505998029725)
    ·
      refine ⟨743793102756564749261147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1983448274017505998029725 743793102756564749261147)
      ·
        refine ⟨1115689654134847123891721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743793102756564749261147 1115689654134847123891721)
        ·
          refine ⟨836767240601135342918791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1115689654134847123891721 836767240601135342918791)
          ·
            refine ⟨1255150860901703014378187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836767240601135342918791 1255150860901703014378187)
            ·
              refine ⟨1882726291352554521567281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255150860901703014378187 1882726291352554521567281)
              ·
                refine ⟨1412044718514415891175461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1882726291352554521567281 1412044718514415891175461)
                ·
                  refine ⟨264758384721452979595399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412044718514415891175461 264758384721452979595399)
                  ·
                    rfl

theorem cell21_1160134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1160134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160134 prefixEnd_1160134 := by exact prefixLift 1160134
  have htrace : WordTrace (prefixWord ++ tailWord_1160134) baseStart_1160134 baseEnd_1160134 := by
    simpa [prefixWord, tailWord_1160134, baseEnd_1160134] using wordTrace_append hprefix tailTrace_1160134
  have hstable : (prefixWord ++ tailWord_1160134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160134).length < 2 ^ (prefixWord ++ tailWord_1160134).sum := by decide
  have hdescent : baseEnd_1160134 < baseStart_1160134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160153 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 5]
def baseStart_1160153 : Nat := 118140960795 + 1160153 * 2 ^ 59
def prefixEnd_1160153 : Nat := 4983230072969 + 3 ^ 40 * 1160153 * 2
def baseEnd_1160153 : Nat := 264762720780313168778693

theorem tailTrace_1160153 : CollatzResearch.WordTrace tailWord_1160153 prefixEnd_1160153 264762720780313168778693 := by
  unfold tailWord_1160153
  simp only [CollatzResearch.WordTrace]
  refine ⟨42314256165971294202909113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28209504110647529468606075 42314256165971294202909113)
  ·
    refine ⟨31735692124478470652181835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42314256165971294202909113 31735692124478470652181835)
    ·
      refine ⟨47603538186717705978272753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31735692124478470652181835 47603538186717705978272753)
      ·
        refine ⟨35702653640038279483704565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47603538186717705978272753 35702653640038279483704565)
        ·
          refine ⟨3347123778753588701597303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35702653640038279483704565 3347123778753588701597303)
          ·
            refine ⟨5020685668130383052395955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347123778753588701597303 5020685668130383052395955)
            ·
              refine ⟨7531028502195574578593933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020685668130383052395955 7531028502195574578593933)
              ·
                refine ⟨2824135688323340466972725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7531028502195574578593933 2824135688323340466972725)
                ·
                  refine ⟨264762720780313168778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2824135688323340466972725 264762720780313168778693)
                  ·
                    rfl

theorem cell21_1160153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_1160153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160153 prefixEnd_1160153 := by exact prefixLift 1160153
  have htrace : WordTrace (prefixWord ++ tailWord_1160153) baseStart_1160153 baseEnd_1160153 := by
    simpa [prefixWord, tailWord_1160153, baseEnd_1160153] using wordTrace_append hprefix tailTrace_1160153
  have hstable : (prefixWord ++ tailWord_1160153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160153).length < 2 ^ (prefixWord ++ tailWord_1160153).sum := by decide
  have hdescent : baseEnd_1160153 < baseStart_1160153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160215 : List Nat := [1, 1, 3, 5, 1, 2, 2, 6]
def baseStart_1160215 : Nat := 118140960795 + 1160215 * 2 ^ 59
def prefixEnd_1160215 : Nat := 4983230072969 + 3 ^ 40 * 1160215 * 2
def baseEnd_1160215 : Nat := 88258956675004946248411

theorem tailTrace_1160215 : CollatzResearch.WordTrace tailWord_1160215 prefixEnd_1160215 88258956675004946248411 := by
  unfold tailWord_1160215
  simp only [CollatzResearch.WordTrace]
  refine ⟨42316517491746678791666099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28211011661164452527777399 42316517491746678791666099)
  ·
    refine ⟨63474776237620018187499149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42316517491746678791666099 63474776237620018187499149)
    ·
      refine ⟨23803041089107506820312181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63474776237620018187499149 23803041089107506820312181)
      ·
        refine ⟨2231535102103828764404267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23803041089107506820312181 2231535102103828764404267)
        ·
          refine ⟨3347302653155743146606401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231535102103828764404267 3347302653155743146606401)
          ·
            refine ⟨2510476989866807359954801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3347302653155743146606401 2510476989866807359954801)
            ·
              refine ⟨1882857742400105519966101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2510476989866807359954801 1882857742400105519966101)
              ·
                refine ⟨88258956675004946248411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1882857742400105519966101 88258956675004946248411)
                ·
                  rfl

theorem cell21_1160215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 6].length) (baseStart_1160215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160215 prefixEnd_1160215 := by exact prefixLift 1160215
  have htrace : WordTrace (prefixWord ++ tailWord_1160215) baseStart_1160215 baseEnd_1160215 := by
    simpa [prefixWord, tailWord_1160215, baseEnd_1160215] using wordTrace_append hprefix tailTrace_1160215
  have hstable : (prefixWord ++ tailWord_1160215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160215).length < 2 ^ (prefixWord ++ tailWord_1160215).sum := by decide
  have hdescent : baseEnd_1160215 < baseStart_1160215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160263 : List Nat := [1, 1, 4, 1, 3, 2, 4, 2, 3]
def baseStart_1160263 : Nat := 118140960795 + 1160263 * 2 ^ 59
def prefixEnd_1160263 : Nat := 4983230072969 + 3 ^ 40 * 1160263 * 2
def baseEnd_1160263 : Nat := 264787824278977421945135

theorem tailTrace_1160263 : CollatzResearch.WordTrace tailWord_1160263 prefixEnd_1160263 264787824278977421945135 := by
  unfold tailWord_1160263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42318268195572782989413443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28212178797048521992942295 42318268195572782989413443)
  ·
    refine ⟨63477402293359174484120165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42318268195572782989413443 63477402293359174484120165)
    ·
      refine ⟨11902012930004845215772531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63477402293359174484120165 11902012930004845215772531)
      ·
        refine ⟨17853019395007267823658797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11902012930004845215772531 17853019395007267823658797)
        ·
          refine ⟨6694882273127725433872049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17853019395007267823658797 6694882273127725433872049)
          ·
            refine ⟨5021161704845794075404037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6694882273127725433872049 5021161704845794075404037)
            ·
              refine ⟨941467819658586389138257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5021161704845794075404037 941467819658586389138257)
              ·
                refine ⟨706100864743939791853693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941467819658586389138257 706100864743939791853693)
                ·
                  refine ⟨264787824278977421945135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706100864743939791853693 264787824278977421945135)
                  ·
                    rfl

theorem cell21_1160263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 3].length) (baseStart_1160263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160263 prefixEnd_1160263 := by exact prefixLift 1160263
  have htrace : WordTrace (prefixWord ++ tailWord_1160263) baseStart_1160263 baseEnd_1160263 := by
    simpa [prefixWord, tailWord_1160263, baseEnd_1160263] using wordTrace_append hprefix tailTrace_1160263
  have hstable : (prefixWord ++ tailWord_1160263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160263).length < 2 ^ (prefixWord ++ tailWord_1160263).sum := by decide
  have hdescent : baseEnd_1160263 < baseStart_1160263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160381 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1160381 : Nat := 118140960795 + 1160381 * 2 ^ 59
def prefixEnd_1160381 : Nat := 4983230072969 + 3 ^ 40 * 1160381 * 2
def baseEnd_1160381 : Nat := 264814753486635438978227

theorem tailTrace_1160381 : CollatzResearch.WordTrace tailWord_1160381 prefixEnd_1160381 264814753486635438978227 := by
  unfold tailWord_1160381
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322572009145289142208997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28215048006096859428139331 42322572009145289142208997)
  ·
    refine ⟨7935482251714741714164187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42322572009145289142208997 7935482251714741714164187)
    ·
      refine ⟨11903223377572112571246281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7935482251714741714164187 11903223377572112571246281)
      ·
        refine ⟨8927417533179084428434711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11903223377572112571246281 8927417533179084428434711)
        ·
          refine ⟨13391126299768626642652067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8927417533179084428434711 13391126299768626642652067)
          ·
            refine ⟨20086689449652939963978101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13391126299768626642652067 20086689449652939963978101)
            ·
              refine ⟨1883127135904963121622947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20086689449652939963978101 1883127135904963121622947)
              ·
                refine ⟨2824690703857444682434421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883127135904963121622947 2824690703857444682434421)
                ·
                  refine ⟨264814753486635438978227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2824690703857444682434421 264814753486635438978227)
                  ·
                    rfl

theorem cell21_1160381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1160381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160381 prefixEnd_1160381 := by exact prefixLift 1160381
  have htrace : WordTrace (prefixWord ++ tailWord_1160381) baseStart_1160381 baseEnd_1160381 := by
    simpa [prefixWord, tailWord_1160381, baseEnd_1160381] using wordTrace_append hprefix tailTrace_1160381
  have hstable : (prefixWord ++ tailWord_1160381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160381).length < 2 ^ (prefixWord ++ tailWord_1160381).sum := by decide
  have hdescent : baseEnd_1160381 < baseStart_1160381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160429 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1160429 : Nat := 118140960795 + 1160429 * 2 ^ 59
def prefixEnd_1160429 : Nat := 4983230072969 + 3 ^ 40 * 1160429 * 2
def baseEnd_1160429 : Nat := 264825707740598022178129

theorem tailTrace_1160429 : CollatzResearch.WordTrace tailWord_1160429 prefixEnd_1160429 264825707740598022178129 := by
  unfold tailWord_1160429
  simp only [CollatzResearch.WordTrace]
  refine ⟨42324322712971393339956341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28216215141980928893304227 42324322712971393339956341)
  ·
    refine ⟨3967905254341068125620907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42324322712971393339956341 3967905254341068125620907)
    ·
      refine ⟨5951857881511602188431361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3967905254341068125620907 5951857881511602188431361)
      ·
        refine ⟨4463893411133701641323521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5951857881511602188431361 4463893411133701641323521)
        ·
          refine ⟨3347920058350276230992641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4463893411133701641323521 3347920058350276230992641)
          ·
            refine ⟨2510940043762707173244481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3347920058350276230992641 2510940043762707173244481)
            ·
              refine ⟨1883205032822030379933361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2510940043762707173244481 1883205032822030379933361)
              ·
                refine ⟨1412403774616522784950021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883205032822030379933361 1412403774616522784950021)
                ·
                  refine ⟨264825707740598022178129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412403774616522784950021 264825707740598022178129)
                  ·
                    rfl

theorem cell21_1160429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1160429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160429 prefixEnd_1160429 := by exact prefixLift 1160429
  have htrace : WordTrace (prefixWord ++ tailWord_1160429) baseStart_1160429 baseEnd_1160429 := by
    simpa [prefixWord, tailWord_1160429, baseEnd_1160429] using wordTrace_append hprefix tailTrace_1160429
  have hstable : (prefixWord ++ tailWord_1160429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160429).length < 2 ^ (prefixWord ++ tailWord_1160429).sum := by decide
  have hdescent : baseEnd_1160429 < baseStart_1160429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160471 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 6]
def baseStart_1160471 : Nat := 118140960795 + 1160471 * 2 ^ 59
def prefixEnd_1160471 : Nat := 4983230072969 + 3 ^ 40 * 1160471 * 2
def baseEnd_1160471 : Nat := 264835292712815282478043

theorem tailTrace_1160471 : CollatzResearch.WordTrace tailWord_1160471 prefixEnd_1160471 264835292712815282478043 := by
  unfold tailWord_1160471
  simp only [CollatzResearch.WordTrace]
  refine ⟨42325854578819234512985267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28217236385879489675323511 42325854578819234512985267)
  ·
    refine ⟨63488781868228851769477901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42325854578819234512985267 63488781868228851769477901)
    ·
      refine ⟨23808293200585819413554213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63488781868228851769477901 23808293200585819413554213)
      ·
        refine ⟨4464054975109841140041415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23808293200585819413554213 4464054975109841140041415)
        ·
          refine ⟨6696082462664761710062123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464054975109841140041415 6696082462664761710062123)
          ·
            refine ⟨10044123693997142565093185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6696082462664761710062123 10044123693997142565093185)
            ·
              refine ⟨7533092770497856923819889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10044123693997142565093185 7533092770497856923819889)
              ·
                refine ⟨5649819577873392692864917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7533092770497856923819889 5649819577873392692864917)
                ·
                  refine ⟨264835292712815282478043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5649819577873392692864917 264835292712815282478043)
                  ·
                    rfl

theorem cell21_1160471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_1160471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160471 prefixEnd_1160471 := by exact prefixLift 1160471
  have htrace : WordTrace (prefixWord ++ tailWord_1160471) baseStart_1160471 baseEnd_1160471 := by
    simpa [prefixWord, tailWord_1160471, baseEnd_1160471] using wordTrace_append hprefix tailTrace_1160471
  have hstable : (prefixWord ++ tailWord_1160471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160471).length < 2 ^ (prefixWord ++ tailWord_1160471).sum := by decide
  have hdescent : baseEnd_1160471 < baseStart_1160471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160474 : List Nat := [3, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_1160474 : Nat := 118140960795 + 1160474 * 2 ^ 59
def prefixEnd_1160474 : Nat := 4983230072969 + 3 ^ 40 * 1160474 * 2
def baseEnd_1160474 : Nat := 264835977353687943928037

theorem tailTrace_1160474 : CollatzResearch.WordTrace tailWord_1160474 prefixEnd_1160474 264835977353687943928037 := by
  unfold tailWord_1160474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10581490999452091506336119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28217309331872244016896317 10581490999452091506336119)
  ·
    refine ⟨15872236499178137259504179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10581490999452091506336119 15872236499178137259504179)
    ·
      refine ⟨23808354748767205889256269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15872236499178137259504179 23808354748767205889256269)
      ·
        refine ⟨8928133030787702208471101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23808354748767205889256269 8928133030787702208471101)
        ·
          refine ⟨3348049886545388328176663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8928133030787702208471101 3348049886545388328176663)
          ·
            refine ⟨5022074829818082492264995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348049886545388328176663 5022074829818082492264995)
            ·
              refine ⟨7533112244727123738397493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022074829818082492264995 7533112244727123738397493)
              ·
                refine ⟨706229272943167850474765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7533112244727123738397493 706229272943167850474765)
                ·
                  refine ⟨264835977353687943928037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706229272943167850474765 264835977353687943928037)
                  ·
                    rfl

theorem cell21_1160474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_1160474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160474 prefixEnd_1160474 := by exact prefixLift 1160474
  have htrace : WordTrace (prefixWord ++ tailWord_1160474) baseStart_1160474 baseEnd_1160474 := by
    simpa [prefixWord, tailWord_1160474, baseEnd_1160474] using wordTrace_append hprefix tailTrace_1160474
  have hstable : (prefixWord ++ tailWord_1160474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160474).length < 2 ^ (prefixWord ++ tailWord_1160474).sum := by decide
  have hdescent : baseEnd_1160474 < baseStart_1160474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160488 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_1160488 : Nat := 118140960795 + 1160488 * 2 ^ 59
def prefixEnd_1160488 : Nat := 4983230072969 + 3 ^ 40 * 1160488 * 2
def baseEnd_1160488 : Nat := 264839172344427030694675

theorem tailTrace_1160488 : CollatzResearch.WordTrace tailWord_1160488 prefixEnd_1160488 264839172344427030694675 := by
  unfold tailWord_1160488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21163237309878823208177059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28217649746505097610902745 21163237309878823208177059)
  ·
    refine ⟨31744855964818234812265589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21163237309878823208177059 31744855964818234812265589)
    ·
      refine ⟨2976080246701709513649899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31744855964818234812265589 2976080246701709513649899)
      ·
        refine ⟨4464120370052564270474849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2976080246701709513649899 4464120370052564270474849)
        ·
          refine ⟨3348090277539423202856137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4464120370052564270474849 3348090277539423202856137)
          ·
            refine ⟨2511067708154567402142103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3348090277539423202856137 2511067708154567402142103)
            ·
              refine ⟨3766601562231851103213155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511067708154567402142103 3766601562231851103213155)
              ·
                refine ⟨5649902343347776654819733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766601562231851103213155 5649902343347776654819733)
                ·
                  refine ⟨264839172344427030694675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5649902343347776654819733 264839172344427030694675)
                  ·
                    rfl

theorem cell21_1160488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_1160488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160488 prefixEnd_1160488 := by exact prefixLift 1160488
  have htrace : WordTrace (prefixWord ++ tailWord_1160488) baseStart_1160488 baseEnd_1160488 := by
    simpa [prefixWord, tailWord_1160488, baseEnd_1160488] using wordTrace_append hprefix tailTrace_1160488
  have hstable : (prefixWord ++ tailWord_1160488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160488).length < 2 ^ (prefixWord ++ tailWord_1160488).sum := by decide
  have hdescent : baseEnd_1160488 < baseStart_1160488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160519 : List Nat := [1, 1, 4, 1, 2, 5, 2, 5]
def baseStart_1160519 : Nat := 118140960795 + 1160519 * 2 ^ 59
def prefixEnd_1160519 : Nat := 4983230072969 + 3 ^ 40 * 1160519 * 2
def baseEnd_1160519 : Nat := 88282082322259288559315

theorem tailTrace_1160519 : CollatzResearch.WordTrace tailWord_1160519 prefixEnd_1160519 88282082322259288559315 := by
  unfold tailWord_1160519
  simp only [CollatzResearch.WordTrace]
  refine ⟨42327605282645338710732611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28218403521763559140488407 42327605282645338710732611)
  ·
    refine ⟨63491407923968008066098917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42327605282645338710732611 63491407923968008066098917)
    ·
      refine ⟨11904638985744001512393547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63491407923968008066098917 11904638985744001512393547)
      ·
        refine ⟨17856958478616002268590321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11904638985744001512393547 17856958478616002268590321)
        ·
          refine ⟨13392718858962001701442741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17856958478616002268590321 13392718858962001701442741)
          ·
            refine ⟨1255567393027687659510257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13392718858962001701442741 1255567393027687659510257)
            ·
              refine ⟨941675544770765744632693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255567393027687659510257 941675544770765744632693)
              ·
                refine ⟨88282082322259288559315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 941675544770765744632693 88282082322259288559315)
                ·
                  rfl

theorem cell21_1160519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 5].length) (baseStart_1160519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160519 prefixEnd_1160519 := by exact prefixLift 1160519
  have htrace : WordTrace (prefixWord ++ tailWord_1160519) baseStart_1160519 baseEnd_1160519 := by
    simpa [prefixWord, tailWord_1160519, baseEnd_1160519] using wordTrace_append hprefix tailTrace_1160519
  have hstable : (prefixWord ++ tailWord_1160519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160519).length < 2 ^ (prefixWord ++ tailWord_1160519).sum := by decide
  have hdescent : baseEnd_1160519 < baseStart_1160519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160525 : List Nat := [1, 6, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1160525 : Nat := 118140960795 + 1160525 * 2 ^ 59
def prefixEnd_1160525 : Nat := 4983230072969 + 3 ^ 40 * 1160525 * 2
def baseEnd_1160525 : Nat := 264847616248523188577933

theorem tailTrace_1160525 : CollatzResearch.WordTrace tailWord_1160525 prefixEnd_1160525 264847616248523188577933 := by
  unfold tailWord_1160525
  simp only [CollatzResearch.WordTrace]
  refine ⟨42327824120623601735451029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28218549413749067823634019 42327824120623601735451029)
  ·
    refine ⟨1984116755654231331349267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42327824120623601735451029 1984116755654231331349267)
    ·
      refine ⟨2976175133481346997023901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984116755654231331349267 2976175133481346997023901)
      ·
        refine ⟨1116065675055505123883963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2976175133481346997023901 1116065675055505123883963)
        ·
          refine ⟨1674098512583257685825945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116065675055505123883963 1674098512583257685825945)
          ·
            refine ⟨1255573884437443264369459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1674098512583257685825945 1255573884437443264369459)
            ·
              refine ⟨1883360826656164896554189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255573884437443264369459 1883360826656164896554189)
              ·
                refine ⟨706260309996061836207821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1883360826656164896554189 706260309996061836207821)
                ·
                  refine ⟨264847616248523188577933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706260309996061836207821 264847616248523188577933)
                  ·
                    rfl

theorem cell21_1160525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1160525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160525 prefixEnd_1160525 := by exact prefixLift 1160525
  have htrace : WordTrace (prefixWord ++ tailWord_1160525) baseStart_1160525 baseEnd_1160525 := by
    simpa [prefixWord, tailWord_1160525, baseEnd_1160525] using wordTrace_append hprefix tailTrace_1160525
  have hstable : (prefixWord ++ tailWord_1160525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160525).length < 2 ^ (prefixWord ++ tailWord_1160525).sum := by decide
  have hdescent : baseEnd_1160525 < baseStart_1160525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160547 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 6]
def baseStart_1160547 : Nat := 118140960795 + 1160547 * 2 ^ 59
def prefixEnd_1160547 : Nat := 4983230072969 + 3 ^ 40 * 1160547 * 2
def baseEnd_1160547 : Nat := 264852636948256039211221

theorem tailTrace_1160547 : CollatzResearch.WordTrace tailWord_1160547 prefixEnd_1160547 264852636948256039211221 := by
  unfold tailWord_1160547
  simp only [CollatzResearch.WordTrace]
  refine ⟨42328626526543899492751895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28219084351029266328501263 42328626526543899492751895)
  ·
    refine ⟨63492939789815849239127843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42328626526543899492751895 63492939789815849239127843)
    ·
      refine ⟨95239409684723773858691765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63492939789815849239127843 95239409684723773858691765)
      ·
        refine ⟨8928694657942853799252353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95239409684723773858691765 8928694657942853799252353)
        ·
          refine ⟨6696520993457140349439265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8928694657942853799252353 6696520993457140349439265)
          ·
            refine ⟨5022390745092855262079449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6696520993457140349439265 5022390745092855262079449)
            ·
              refine ⟨3766793058819641446559587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022390745092855262079449 3766793058819641446559587)
              ·
                refine ⟨5650189588229462169839381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766793058819641446559587 5650189588229462169839381)
                ·
                  refine ⟨264852636948256039211221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5650189588229462169839381 264852636948256039211221)
                  ·
                    rfl

theorem cell21_1160547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_1160547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160547 prefixEnd_1160547 := by exact prefixLift 1160547
  have htrace : WordTrace (prefixWord ++ tailWord_1160547) baseStart_1160547 baseEnd_1160547 := by
    simpa [prefixWord, tailWord_1160547, baseEnd_1160547] using wordTrace_append hprefix tailTrace_1160547
  have hstable : (prefixWord ++ tailWord_1160547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160547).length < 2 ^ (prefixWord ++ tailWord_1160547).sum := by decide
  have hdescent : baseEnd_1160547 < baseStart_1160547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160561 : List Nat := [1, 2, 2, 2, 1, 2, 3, 8]
def baseStart_1160561 : Nat := 118140960795 + 1160561 * 2 ^ 59
def prefixEnd_1160561 : Nat := 4983230072969 + 3 ^ 40 * 1160561 * 2
def baseEnd_1160561 : Nat := 88285277312998375325953

theorem tailTrace_1160561 : CollatzResearch.WordTrace tailWord_1160561 prefixEnd_1160561 88285277312998375325953 := by
  unfold tailWord_1160561
  simp only [CollatzResearch.WordTrace]
  refine ⟨42329137148493179883761537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28219424765662119922507691 42329137148493179883761537)
  ·
    refine ⟨31746852861369884912821153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42329137148493179883761537 31746852861369884912821153)
    ·
      refine ⟨23810139646027413684615865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31746852861369884912821153 23810139646027413684615865)
      ·
        refine ⟨17857604734520560263461899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23810139646027413684615865 17857604734520560263461899)
        ·
          refine ⟨26786407101780840395192849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17857604734520560263461899 26786407101780840395192849)
          ·
            refine ⟨20089805326335630296394637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26786407101780840395192849 20089805326335630296394637)
            ·
              refine ⟨7533676997375861361147989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20089805326335630296394637 7533676997375861361147989)
              ·
                refine ⟨88285277312998375325953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7533676997375861361147989 88285277312998375325953)
                ·
                  rfl

theorem cell21_1160561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 8].length) (baseStart_1160561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160561 prefixEnd_1160561 := by exact prefixLift 1160561
  have htrace : WordTrace (prefixWord ++ tailWord_1160561) baseStart_1160561 baseEnd_1160561 := by
    simpa [prefixWord, tailWord_1160561, baseEnd_1160561] using wordTrace_append hprefix tailTrace_1160561
  have hstable : (prefixWord ++ tailWord_1160561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160561).length < 2 ^ (prefixWord ++ tailWord_1160561).sum := by decide
  have hdescent : baseEnd_1160561 < baseStart_1160561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160837 : List Nat := [1, 3, 1, 1, 4, 1, 1, 6, 3]
def baseStart_1160837 : Nat := 118140960795 + 1160837 * 2 ^ 59
def prefixEnd_1160837 : Nat := 4983230072969 + 3 ^ 40 * 1160837 * 2
def baseEnd_1160837 : Nat := 264918818899279979377295

theorem tailTrace_1160837 : CollatzResearch.WordTrace tailWord_1160837 prefixEnd_1160837 264918818899279979377295 := by
  unfold tailWord_1160837
  simp only [CollatzResearch.WordTrace]
  refine ⟨42339203695493279020808765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28226135796995519347205843 42339203695493279020808765)
  ·
    refine ⟨15877201385809979632803287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42339203695493279020808765 15877201385809979632803287)
    ·
      refine ⟨23815802078714969449204931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15877201385809979632803287 23815802078714969449204931)
      ·
        refine ⟨35723703118072454173807397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23815802078714969449204931 35723703118072454173807397)
        ·
          refine ⟨6698194334638585157588887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35723703118072454173807397 6698194334638585157588887)
          ·
            refine ⟨10047291501957877736383331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698194334638585157588887 10047291501957877736383331)
            ·
              refine ⟨15070937252936816604574997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10047291501957877736383331 15070937252936816604574997)
              ·
                refine ⟨706450183731413278339453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15070937252936816604574997 706450183731413278339453)
                ·
                  refine ⟨264918818899279979377295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706450183731413278339453 264918818899279979377295)
                  ·
                    rfl

theorem cell21_1160837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_1160837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160837 prefixEnd_1160837 := by exact prefixLift 1160837
  have htrace : WordTrace (prefixWord ++ tailWord_1160837) baseStart_1160837 baseEnd_1160837 := by
    simpa [prefixWord, tailWord_1160837, baseEnd_1160837] using wordTrace_append hprefix tailTrace_1160837
  have hstable : (prefixWord ++ tailWord_1160837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160837).length < 2 ^ (prefixWord ++ tailWord_1160837).sum := by decide
  have hdescent : baseEnd_1160837 < baseStart_1160837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160902 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1160902 : Nat := 118140960795 + 1160902 * 2 ^ 59
def prefixEnd_1160902 : Nat := 4983230072969 + 3 ^ 40 * 1160902 * 2
def baseEnd_1160902 : Nat := 264933652784854310793829

theorem tailTrace_1160902 : CollatzResearch.WordTrace tailWord_1160902 prefixEnd_1160902 264933652784854310793829 := by
  unfold tailWord_1160902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323174201258056097560155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28227716293505196747949973 1323174201258056097560155)
  ·
    refine ⟨1984761301887084146340233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323174201258056097560155 1984761301887084146340233)
    ·
      refine ⟨1488570976415313109755175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1984761301887084146340233 1488570976415313109755175)
      ·
        refine ⟨2232856464622969664632763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488570976415313109755175 2232856464622969664632763)
        ·
          refine ⟨3349284696934454496949145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232856464622969664632763 3349284696934454496949145)
          ·
            refine ⟨2511963522700840872711859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3349284696934454496949145 2511963522700840872711859)
            ·
              refine ⟨3767945284051261309067789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511963522700840872711859 3767945284051261309067789)
              ·
                refine ⟨1412979481519222990900421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3767945284051261309067789 1412979481519222990900421)
                ·
                  refine ⟨264933652784854310793829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1412979481519222990900421 264933652784854310793829)
                  ·
                    rfl

theorem cell21_1160902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1160902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160902 prefixEnd_1160902 := by exact prefixLift 1160902
  have htrace : WordTrace (prefixWord ++ tailWord_1160902) baseStart_1160902 baseEnd_1160902 := by
    simpa [prefixWord, tailWord_1160902, baseEnd_1160902] using wordTrace_append hprefix tailTrace_1160902
  have hstable : (prefixWord ++ tailWord_1160902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160902).length < 2 ^ (prefixWord ++ tailWord_1160902).sum := by decide
  have hdescent : baseEnd_1160902 < baseStart_1160902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160941 : List Nat := [1, 5, 1, 2, 1, 11]
def baseStart_1160941 : Nat := 118140960795 + 1160941 * 2 ^ 59
def prefixEnd_1160941 : Nat := 4983230072969 + 3 ^ 40 * 1160941 * 2
def baseEnd_1160941 : Nat := 9812687152451811468287

theorem tailTrace_1160941 : CollatzResearch.WordTrace tailWord_1160941 prefixEnd_1160941 9812687152451811468287 := by
  unfold tailWord_1160941
  simp only [CollatzResearch.WordTrace]
  refine ⟨42342996887116504782594677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28228664591411003188396451 42342996887116504782594677)
  ·
    refine ⟨3969655958167172323368251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42342996887116504782594677 3969655958167172323368251)
    ·
      refine ⟨5954483937250758485052377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3969655958167172323368251 5954483937250758485052377)
      ·
        refine ⟨4465862952938068863789283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5954483937250758485052377 4465862952938068863789283)
        ·
          refine ⟨6698794429407103295683925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4465862952938068863789283 6698794429407103295683925)
          ·
            refine ⟨9812687152451811468287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6698794429407103295683925 9812687152451811468287)
            ·
              rfl

theorem cell21_1160941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 11].length) (baseStart_1160941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1160941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1160941 prefixEnd_1160941 := by exact prefixLift 1160941
  have htrace : WordTrace (prefixWord ++ tailWord_1160941) baseStart_1160941 baseEnd_1160941 := by
    simpa [prefixWord, tailWord_1160941, baseEnd_1160941] using wordTrace_append hprefix tailTrace_1160941
  have hstable : (prefixWord ++ tailWord_1160941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160941).length < 2 ^ (prefixWord ++ tailWord_1160941).sum := by decide
  have hdescent : baseEnd_1160941 < baseStart_1160941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161006 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1161006 : Nat := 118140960795 + 1161006 * 2 ^ 59
def prefixEnd_1161006 : Nat := 4983230072969 + 3 ^ 40 * 1161006 * 2
def baseEnd_1161006 : Nat := 264957387001773241060283

theorem tailTrace_1161006 : CollatzResearch.WordTrace tailWord_1161006 prefixEnd_1161006 264957387001773241060283 := by
  unfold tailWord_1161006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293170953985127610463859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28230245087920680589140581 5293170953985127610463859)
  ·
    refine ⟨7939756430977691415695789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5293170953985127610463859 7939756430977691415695789)
    ·
      refine ⟨2977408661616634280885921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7939756430977691415695789 2977408661616634280885921)
      ·
        refine ⟨2233056496212475710664441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2977408661616634280885921 2233056496212475710664441)
        ·
          refine ⟨1674792372159356782998331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2233056496212475710664441 1674792372159356782998331)
          ·
            refine ⟨2512188558239035174497497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674792372159356782998331 2512188558239035174497497)
            ·
              refine ⟨1884141418679276380873123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512188558239035174497497 1884141418679276380873123)
              ·
                refine ⟨2826212128018914571309685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884141418679276380873123 2826212128018914571309685)
                ·
                  refine ⟨264957387001773241060283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826212128018914571309685 264957387001773241060283)
                  ·
                    rfl

theorem cell21_1161006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1161006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161006 prefixEnd_1161006 := by exact prefixLift 1161006
  have htrace : WordTrace (prefixWord ++ tailWord_1161006) baseStart_1161006 baseEnd_1161006 := by
    simpa [prefixWord, tailWord_1161006, baseEnd_1161006] using wordTrace_append hprefix tailTrace_1161006
  have hstable : (prefixWord ++ tailWord_1161006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161006).length < 2 ^ (prefixWord ++ tailWord_1161006).sum := by decide
  have hdescent : baseEnd_1161006 < baseStart_1161006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161245 : List Nat := [1, 4, 2, 2, 2, 1, 1, 8]
def baseStart_1161245 : Nat := 118140960795 + 1161245 * 2 ^ 59
def prefixEnd_1161245 : Nat := 4983230072969 + 3 ^ 40 * 1161245 * 2
def baseEnd_1161245 : Nat := 88337310019320645525487

theorem tailTrace_1161245 : CollatzResearch.WordTrace tailWord_1161245 prefixEnd_1161245 88337310019320645525487 := by
  unfold tailWord_1161245
  simp only [CollatzResearch.WordTrace]
  refine ⟨42354084678015164701661189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28236056452010109801107459 42354084678015164701661189)
  ·
    refine ⟨7941390877127843381561473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42354084678015164701661189 7941390877127843381561473)
    ·
      refine ⟨5956043157845882536171105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7941390877127843381561473 5956043157845882536171105)
      ·
        refine ⟨4467032368384411902128329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5956043157845882536171105 4467032368384411902128329)
        ·
          refine ⟨3350274276288308926596247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4467032368384411902128329 3350274276288308926596247)
          ·
            refine ⟨5025411414432463389894371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350274276288308926596247 5025411414432463389894371)
            ·
              refine ⟨7538117121648695084841557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025411414432463389894371 7538117121648695084841557)
              ·
                refine ⟨88337310019320645525487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7538117121648695084841557 88337310019320645525487)
                ·
                  rfl

theorem cell21_1161245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 8].length) (baseStart_1161245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161245 prefixEnd_1161245 := by exact prefixLift 1161245
  have htrace : WordTrace (prefixWord ++ tailWord_1161245) baseStart_1161245 baseEnd_1161245 := by
    simpa [prefixWord, tailWord_1161245, baseEnd_1161245] using wordTrace_append hprefix tailTrace_1161245
  have hstable : (prefixWord ++ tailWord_1161245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161245).length < 2 ^ (prefixWord ++ tailWord_1161245).sum := by decide
  have hdescent : baseEnd_1161245 < baseStart_1161245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161321 : List Nat := [1, 2, 1, 1, 1, 5, 5, 5]
def baseStart_1161321 : Nat := 118140960795 + 1161321 * 2 ^ 59
def prefixEnd_1161321 : Nat := 4983230072969 + 3 ^ 40 * 1161321 * 2
def baseEnd_1161321 : Nat := 88343091431134231103213

theorem tailTrace_1161321 : CollatzResearch.WordTrace tailWord_1161321 prefixEnd_1161321 88343091431134231103213 := by
  unfold tailWord_1161321
  simp only [CollatzResearch.WordTrace]
  refine ⟨42356856625739829681427817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28237904417159886454285211 42356856625739829681427817)
  ·
    refine ⟨31767642469304872261070863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42356856625739829681427817 31767642469304872261070863)
    ·
      refine ⟨47651463703957308391606295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31767642469304872261070863 47651463703957308391606295)
      ·
        refine ⟨71477195555935962587409443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47651463703957308391606295 71477195555935962587409443)
        ·
          refine ⟨107215793333903943881114165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71477195555935962587409443 107215793333903943881114165)
          ·
            refine ⟨10051480625053494738854453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107215793333903943881114165 10051480625053494738854453)
            ·
              refine ⟨942326308598765131767605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10051480625053494738854453 942326308598765131767605)
              ·
                refine ⟨88343091431134231103213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 942326308598765131767605 88343091431134231103213)
                ·
                  rfl

theorem cell21_1161321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 5].length) (baseStart_1161321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161321 prefixEnd_1161321 := by exact prefixLift 1161321
  have htrace : WordTrace (prefixWord ++ tailWord_1161321) baseStart_1161321 baseEnd_1161321 := by
    simpa [prefixWord, tailWord_1161321, baseEnd_1161321] using wordTrace_append hprefix tailTrace_1161321
  have hstable : (prefixWord ++ tailWord_1161321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161321).length < 2 ^ (prefixWord ++ tailWord_1161321).sum := by decide
  have hdescent : baseEnd_1161321 < baseStart_1161321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161352 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_1161352 : Nat := 118140960795 + 1161352 * 2 ^ 59
def prefixEnd_1161352 : Nat := 4983230072969 + 3 ^ 40 * 1161352 * 2
def baseEnd_1161352 : Nat := 265036348915753528292909

theorem tailTrace_1161352 : CollatzResearch.WordTrace tailWord_1161352 prefixEnd_1161352 265036348915753528292909 := by
  unfold tailWord_1161352
  simp only [CollatzResearch.WordTrace]
  refine ⟨21178993644313760987903155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28238658192418347983870873 21178993644313760987903155)
  ·
    refine ⟨31768490466470641481854733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21178993644313760987903155 31768490466470641481854733)
    ·
      refine ⟨11913183924926490555695525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31768490466470641481854733 11913183924926490555695525)
      ·
        refine ⟨2233721985923716979192911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11913183924926490555695525 2233721985923716979192911)
        ·
          refine ⟨3350582978885575468789367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233721985923716979192911 3350582978885575468789367)
          ·
            refine ⟨5025874468328363203184051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350582978885575468789367 5025874468328363203184051)
            ·
              refine ⟨7538811702492544804776077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025874468328363203184051 7538811702492544804776077)
              ·
                refine ⟨2827054388434704301791029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7538811702492544804776077 2827054388434704301791029)
                ·
                  refine ⟨265036348915753528292909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827054388434704301791029 265036348915753528292909)
                  ·
                    rfl

theorem cell21_1161352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_1161352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161352 prefixEnd_1161352 := by exact prefixLift 1161352
  have htrace : WordTrace (prefixWord ++ tailWord_1161352) baseStart_1161352 baseEnd_1161352 := by
    simpa [prefixWord, tailWord_1161352, baseEnd_1161352] using wordTrace_append hprefix tailTrace_1161352
  have hstable : (prefixWord ++ tailWord_1161352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161352).length < 2 ^ (prefixWord ++ tailWord_1161352).sum := by decide
  have hdescent : baseEnd_1161352 < baseStart_1161352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161462 : List Nat := [5, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_1161462 : Nat := 118140960795 + 1161462 * 2 ^ 59
def prefixEnd_1161462 : Nat := 4983230072969 + 3 ^ 40 * 1161462 * 2
def baseEnd_1161462 : Nat := 265061452414417781459351

theorem tailTrace_1161462 : CollatzResearch.WordTrace tailWord_1161462 prefixEnd_1161462 265061452414417781459351 := by
  unfold tailWord_1161462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2647624957389313172644415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28241332878819340508207093 2647624957389313172644415)
  ·
    refine ⟨3971437436083969758966623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2647624957389313172644415 3971437436083969758966623)
    ·
      refine ⟨5957156154125954638449935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3971437436083969758966623 5957156154125954638449935)
      ·
        refine ⟨8935734231188931957674903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5957156154125954638449935 8935734231188931957674903)
        ·
          refine ⟨13403601346783397936512355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935734231188931957674903 13403601346783397936512355)
          ·
            refine ⟨20105402020175096904768533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403601346783397936512355 20105402020175096904768533)
            ·
              refine ⟨942440719695707667411025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20105402020175096904768533 942440719695707667411025)
              ·
                refine ⟨706830539771780750558269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942440719695707667411025 706830539771780750558269)
                ·
                  refine ⟨265061452414417781459351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706830539771780750558269 265061452414417781459351)
                  ·
                    rfl

theorem cell21_1161462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_1161462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161462 prefixEnd_1161462 := by exact prefixLift 1161462
  have htrace : WordTrace (prefixWord ++ tailWord_1161462) baseStart_1161462 baseEnd_1161462 := by
    simpa [prefixWord, tailWord_1161462, baseEnd_1161462] using wordTrace_append hprefix tailTrace_1161462
  have hstable : (prefixWord ++ tailWord_1161462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161462).length < 2 ^ (prefixWord ++ tailWord_1161462).sum := by decide
  have hdescent : baseEnd_1161462 < baseStart_1161462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161532 : List Nat := [2, 2, 2, 2, 1, 2, 2, 8]
def baseStart_1161532 : Nat := 118140960795 + 1161532 * 2 ^ 59
def prefixEnd_1161532 : Nat := 4983230072969 + 3 ^ 40 * 1161532 * 2
def baseEnd_1161532 : Nat := 88359142456037738430847

theorem tailTrace_1161532 : CollatzResearch.WordTrace tailWord_1161532 prefixEnd_1161532 88359142456037738430847 := by
  unfold tailWord_1161532
  simp only [CollatzResearch.WordTrace]
  refine ⟨21182276213987706358679425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28243034951983608478239233 21182276213987706358679425)
  ·
    refine ⟨15886707160490779769009569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21182276213987706358679425 15886707160490779769009569)
    ·
      refine ⟨11915030370368084826757177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15886707160490779769009569 11915030370368084826757177)
      ·
        refine ⟨8936272777776063620067883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11915030370368084826757177 8936272777776063620067883)
        ·
          refine ⟨13404409166664095430101825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8936272777776063620067883 13404409166664095430101825)
          ·
            refine ⟨10053306874998071572576369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13404409166664095430101825 10053306874998071572576369)
            ·
              refine ⟨7539980156248553679432277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10053306874998071572576369 7539980156248553679432277)
              ·
                refine ⟨88359142456037738430847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7539980156248553679432277 88359142456037738430847)
                ·
                  rfl

theorem cell21_1161532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_1161532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161532 prefixEnd_1161532 := by exact prefixLift 1161532
  have htrace : WordTrace (prefixWord ++ tailWord_1161532) baseStart_1161532 baseEnd_1161532 := by
    simpa [prefixWord, tailWord_1161532, baseEnd_1161532] using wordTrace_append hprefix tailTrace_1161532
  have hstable : (prefixWord ++ tailWord_1161532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161532).length < 2 ^ (prefixWord ++ tailWord_1161532).sum := by decide
  have hdescent : baseEnd_1161532 < baseStart_1161532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161535 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 4]
def baseStart_1161535 : Nat := 118140960795 + 1161535 * 2 ^ 59
def prefixEnd_1161535 : Nat := 4983230072969 + 3 ^ 40 * 1161535 * 2
def baseEnd_1161535 : Nat := 265078112008985876742535

theorem tailTrace_1161535 : CollatzResearch.WordTrace tailWord_1161535 prefixEnd_1161535 265078112008985876742535 := by
  unfold tailWord_1161535
  simp only [CollatzResearch.WordTrace]
  refine ⟨42364661846964544229718059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28243107897976362819812039 42364661846964544229718059)
  ·
    refine ⟨63546992770446816344577089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42364661846964544229718059 63546992770446816344577089)
    ·
      refine ⟨47660244577835112258432817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63546992770446816344577089 47660244577835112258432817)
      ·
        refine ⟨35745183433376334193824613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47660244577835112258432817 35745183433376334193824613)
        ·
          refine ⟨6702221893758062661342115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35745183433376334193824613 6702221893758062661342115)
          ·
            refine ⟨10053332840637093992013173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702221893758062661342115 10053332840637093992013173)
            ·
              refine ⟨942499953809727561751235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10053332840637093992013173 942499953809727561751235)
              ·
                refine ⟨1413749930714591342626853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942499953809727561751235 1413749930714591342626853)
                ·
                  refine ⟨265078112008985876742535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1413749930714591342626853 265078112008985876742535)
                  ·
                    rfl

theorem cell21_1161535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 4].length) (baseStart_1161535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161535 prefixEnd_1161535 := by exact prefixLift 1161535
  have htrace : WordTrace (prefixWord ++ tailWord_1161535) baseStart_1161535 baseEnd_1161535 := by
    simpa [prefixWord, tailWord_1161535, baseEnd_1161535] using wordTrace_append hprefix tailTrace_1161535
  have hstable : (prefixWord ++ tailWord_1161535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161535).length < 2 ^ (prefixWord ++ tailWord_1161535).sum := by decide
  have hdescent : baseEnd_1161535 < baseStart_1161535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161577 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 6]
def baseStart_1161577 : Nat := 118140960795 + 1161577 * 2 ^ 59
def prefixEnd_1161577 : Nat := 4983230072969 + 3 ^ 40 * 1161577 * 2
def baseEnd_1161577 : Nat := 265087696981203137042449

theorem tailTrace_1161577 : CollatzResearch.WordTrace tailWord_1161577 prefixEnd_1161577 265087696981203137042449 := by
  unfold tailWord_1161577
  simp only [CollatzResearch.WordTrace]
  refine ⟨42366193712812385402746985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28244129141874923601831323 42366193712812385402746985)
  ·
    refine ⟨31774645284609289052060239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42366193712812385402746985 31774645284609289052060239)
    ·
      refine ⟨47661967926913933578090359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31774645284609289052060239 47661967926913933578090359)
      ·
        refine ⟨71492951890370900367135539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47661967926913933578090359 71492951890370900367135539)
        ·
          refine ⟨107239427835556350550703309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71492951890370900367135539 107239427835556350550703309)
          ·
            refine ⟨40214785438333631456513741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107239427835556350550703309 40214785438333631456513741)
            ·
              refine ⟨15080544539375111796192653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40214785438333631456513741 15080544539375111796192653)
              ·
                refine ⟨5655204202265666923572245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15080544539375111796192653 5655204202265666923572245)
                ·
                  refine ⟨265087696981203137042449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5655204202265666923572245 265087696981203137042449)
                  ·
                    rfl

theorem cell21_1161577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_1161577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161577 prefixEnd_1161577 := by exact prefixLift 1161577
  have htrace : WordTrace (prefixWord ++ tailWord_1161577) baseStart_1161577 baseEnd_1161577 := by
    simpa [prefixWord, tailWord_1161577, baseEnd_1161577] using wordTrace_append hprefix tailTrace_1161577
  have hstable : (prefixWord ++ tailWord_1161577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161577).length < 2 ^ (prefixWord ++ tailWord_1161577).sum := by decide
  have hdescent : baseEnd_1161577 < baseStart_1161577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161608 : List Nat := [2, 1, 3, 3, 1, 1, 1, 9]
def baseStart_1161608 : Nat := 118140960795 + 1161608 * 2 ^ 59
def prefixEnd_1161608 : Nat := 4983230072969 + 3 ^ 40 * 1161608 * 2
def baseEnd_1161608 : Nat := 88364923867851324008573

theorem tailTrace_1161608 : CollatzResearch.WordTrace tailWord_1161608 prefixEnd_1161608 88364923867851324008573 := by
  unfold tailWord_1161608
  simp only [CollatzResearch.WordTrace]
  refine ⟨21183662187850038848562739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28244882917133385131416985 21183662187850038848562739)
  ·
    refine ⟨31775493281775058272844109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21183662187850038848562739 31775493281775058272844109)
    ·
      refine ⟨11915809980665646852316541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31775493281775058272844109 11915809980665646852316541)
      ·
        refine ⟨4468428742749617569618703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11915809980665646852316541 4468428742749617569618703)
        ·
          refine ⟨6702643114124426354428055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468428742749617569618703 6702643114124426354428055)
          ·
            refine ⟨10053964671186639531642083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702643114124426354428055 10053964671186639531642083)
            ·
              refine ⟨15080947006779959297463125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10053964671186639531642083 15080947006779959297463125)
              ·
                refine ⟨88364923867851324008573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15080947006779959297463125 88364923867851324008573)
                ·
                  rfl

theorem cell21_1161608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_1161608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161608 prefixEnd_1161608 := by exact prefixLift 1161608
  have htrace : WordTrace (prefixWord ++ tailWord_1161608) baseStart_1161608 baseEnd_1161608 := by
    simpa [prefixWord, tailWord_1161608, baseEnd_1161608] using wordTrace_append hprefix tailTrace_1161608
  have hstable : (prefixWord ++ tailWord_1161608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161608).length < 2 ^ (prefixWord ++ tailWord_1161608).sum := by decide
  have hdescent : baseEnd_1161608 < baseStart_1161608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161749 : List Nat := [1, 3, 2, 1, 3, 1, 5, 2, 3]
def baseStart_1161749 : Nat := 118140960795 + 1161749 * 2 ^ 59
def prefixEnd_1161749 : Nat := 4983230072969 + 3 ^ 40 * 1161749 * 2
def baseEnd_1161749 : Nat := 265126949724569060175431

theorem tailTrace_1161749 : CollatzResearch.WordTrace tailWord_1161749 prefixEnd_1161749 265126949724569060175431 := by
  unfold tailWord_1161749
  simp only [CollatzResearch.WordTrace]
  refine ⟨42372467068189258778008301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28248311378792839185338867 42372467068189258778008301)
  ·
    refine ⟨15889675150570972041753113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42372467068189258778008301 15889675150570972041753113)
    ·
      refine ⟨11917256362928229031314835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15889675150570972041753113 11917256362928229031314835)
      ·
        refine ⟨17875884544392343546972253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11917256362928229031314835 17875884544392343546972253)
        ·
          refine ⟨6703456704147128830114595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17875884544392343546972253 6703456704147128830114595)
          ·
            refine ⟨10055185056220693245171893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703456704147128830114595 10055185056220693245171893)
            ·
              refine ⟨942673599020689991734865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10055185056220693245171893 942673599020689991734865)
              ·
                refine ⟨707005199265517493801149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942673599020689991734865 707005199265517493801149)
                ·
                  refine ⟨265126949724569060175431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707005199265517493801149 265126949724569060175431)
                  ·
                    rfl

theorem cell21_1161749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_1161749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161749 prefixEnd_1161749 := by exact prefixLift 1161749
  have htrace : WordTrace (prefixWord ++ tailWord_1161749) baseStart_1161749 baseEnd_1161749 := by
    simpa [prefixWord, tailWord_1161749, baseEnd_1161749] using wordTrace_append hprefix tailTrace_1161749
  have hstable : (prefixWord ++ tailWord_1161749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161749).length < 2 ^ (prefixWord ++ tailWord_1161749).sum := by decide
  have hdescent : baseEnd_1161749 < baseStart_1161749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161763 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 4]
def baseStart_1161763 : Nat := 118140960795 + 1161763 * 2 ^ 59
def prefixEnd_1161763 : Nat := 4983230072969 + 3 ^ 40 * 1161763 * 2
def baseEnd_1161763 : Nat := 265130144715308146942069

theorem tailTrace_1161763 : CollatzResearch.WordTrace tailWord_1161763 prefixEnd_1161763 265130144715308146942069 := by
  unfold tailWord_1161763
  simp only [CollatzResearch.WordTrace]
  refine ⟨42372977690138539169017943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28248651793425692779345295 42372977690138539169017943)
  ·
    refine ⟨63559466535207808753526915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42372977690138539169017943 63559466535207808753526915)
    ·
      refine ⟨95339199802811713130290373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63559466535207808753526915 95339199802811713130290373)
      ·
        refine ⟨17876099963027196211929445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95339199802811713130290373 17876099963027196211929445)
        ·
          refine ⟨3351768743067599289736771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17876099963027196211929445 3351768743067599289736771)
          ·
            refine ⟨5027653114601398934605157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351768743067599289736771 5027653114601398934605157)
            ·
              refine ⟨942684958987762300238467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5027653114601398934605157 942684958987762300238467)
              ·
                refine ⟨1414027438481643450357701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942684958987762300238467 1414027438481643450357701)
                ·
                  refine ⟨265130144715308146942069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414027438481643450357701 265130144715308146942069)
                  ·
                    rfl

theorem cell21_1161763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 4].length) (baseStart_1161763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161763 prefixEnd_1161763 := by exact prefixLift 1161763
  have htrace : WordTrace (prefixWord ++ tailWord_1161763) baseStart_1161763 baseEnd_1161763 := by
    simpa [prefixWord, tailWord_1161763, baseEnd_1161763] using wordTrace_append hprefix tailTrace_1161763
  have hstable : (prefixWord ++ tailWord_1161763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161763).length < 2 ^ (prefixWord ++ tailWord_1161763).sum := by decide
  have hdescent : baseEnd_1161763 < baseStart_1161763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161901 : List Nat := [1, 5, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1161901 : Nat := 118140960795 + 1161901 * 2 ^ 59
def prefixEnd_1161901 : Nat := 4983230072969 + 3 ^ 40 * 1161901 * 2
def baseEnd_1161901 : Nat := 265161638195450573641787

theorem tailTrace_1161901 : CollatzResearch.WordTrace tailWord_1161901 prefixEnd_1161901 265161638195450573641787 := by
  unfold tailWord_1161901
  simp only [CollatzResearch.WordTrace]
  refine ⟨42378010963638588737541557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28252007309092392491694371 42378010963638588737541557)
  ·
    refine ⟨3972938527841117694144521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42378010963638588737541557 3972938527841117694144521)
    ·
      refine ⟨2979703895880838270608391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3972938527841117694144521 2979703895880838270608391)
      ·
        refine ⟨4469555843821257405912587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979703895880838270608391 4469555843821257405912587)
        ·
          refine ⟨6704333765731886108868881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4469555843821257405912587 6704333765731886108868881)
          ·
            refine ⟨5028250324298914581651661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6704333765731886108868881 5028250324298914581651661)
            ·
              refine ⟨1885593871612092968119373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5028250324298914581651661 1885593871612092968119373)
              ·
                refine ⟨707097701854534863044765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1885593871612092968119373 707097701854534863044765)
                ·
                  refine ⟨265161638195450573641787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707097701854534863044765 265161638195450573641787)
                  ·
                    rfl

theorem cell21_1161901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1161901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161901 prefixEnd_1161901 := by exact prefixLift 1161901
  have htrace : WordTrace (prefixWord ++ tailWord_1161901) baseStart_1161901 baseEnd_1161901 := by
    simpa [prefixWord, tailWord_1161901, baseEnd_1161901] using wordTrace_append hprefix tailTrace_1161901
  have hstable : (prefixWord ++ tailWord_1161901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161901).length < 2 ^ (prefixWord ++ tailWord_1161901).sum := by decide
  have hdescent : baseEnd_1161901 < baseStart_1161901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161932 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_1161932 : Nat := 118140960795 + 1161932 * 2 ^ 59
def prefixEnd_1161932 : Nat := 4983230072969 + 3 ^ 40 * 1161932 * 2
def baseEnd_1161932 : Nat := 265168712817801408625057

theorem tailTrace_1161932 : CollatzResearch.WordTrace tailWord_1161932 prefixEnd_1161932 265168712817801408625057 := by
  unfold tailWord_1161932
  simp only [CollatzResearch.WordTrace]
  refine ⟨21189570813263140515960025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28252761084350854021280033 21189570813263140515960025)
  ·
    refine ⟨15892178109947355386970019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21189570813263140515960025 15892178109947355386970019)
    ·
      refine ⟨23838267164921033080455029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15892178109947355386970019 23838267164921033080455029)
      ·
        refine ⟨2234837546711346851292659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23838267164921033080455029 2234837546711346851292659)
        ·
          refine ⟨3352256320067020276938989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234837546711346851292659 3352256320067020276938989)
          ·
            refine ⟨1257096120025132603852121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3352256320067020276938989 1257096120025132603852121)
            ·
              refine ⟨942822090018849452889091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257096120025132603852121 942822090018849452889091)
              ·
                refine ⟨1414233135028274179333637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942822090018849452889091 1414233135028274179333637)
                ·
                  refine ⟨265168712817801408625057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414233135028274179333637 265168712817801408625057)
                  ·
                    rfl

theorem cell21_1161932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_1161932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1161932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1161932 prefixEnd_1161932 := by exact prefixLift 1161932
  have htrace : WordTrace (prefixWord ++ tailWord_1161932) baseStart_1161932 baseEnd_1161932 := by
    simpa [prefixWord, tailWord_1161932, baseEnd_1161932] using wordTrace_append hprefix tailTrace_1161932
  have hstable : (prefixWord ++ tailWord_1161932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161932).length < 2 ^ (prefixWord ++ tailWord_1161932).sum := by decide
  have hdescent : baseEnd_1161932 < baseStart_1161932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162033 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 6]
def baseStart_1162033 : Nat := 118140960795 + 1162033 * 2 ^ 59
def prefixEnd_1162033 : Nat := 4983230072969 + 3 ^ 40 * 1162033 * 2
def baseEnd_1162033 : Nat := 265191762393847677441517

theorem tailTrace_1162033 : CollatzResearch.WordTrace tailWord_1162033 prefixEnd_1162033 265191762393847677441517 := by
  unfold tailWord_1162033
  simp only [CollatzResearch.WordTrace]
  refine ⟨42382825399160375281346753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28255216932773583520897835 42382825399160375281346753)
  ·
    refine ⟨31787119049370281461010065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42382825399160375281346753 31787119049370281461010065)
    ·
      refine ⟨23840339287027711095757549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31787119049370281461010065 23840339287027711095757549)
      ·
        refine ⟨8940127232635391660909081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23840339287027711095757549 8940127232635391660909081)
        ·
          refine ⟨6705095424476543745681811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8940127232635391660909081 6705095424476543745681811)
          ·
            refine ⟨10057643136714815618522717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705095424476543745681811 10057643136714815618522717)
            ·
              refine ⟨3771616176268055856946019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10057643136714815618522717 3771616176268055856946019)
              ·
                refine ⟨5657424264402083785419029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771616176268055856946019 5657424264402083785419029)
                ·
                  refine ⟨265191762393847677441517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5657424264402083785419029 265191762393847677441517)
                  ·
                    rfl

theorem cell21_1162033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_1162033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162033 prefixEnd_1162033 := by exact prefixLift 1162033
  have htrace : WordTrace (prefixWord ++ tailWord_1162033) baseStart_1162033 baseEnd_1162033 := by
    simpa [prefixWord, tailWord_1162033, baseEnd_1162033] using wordTrace_append hprefix tailTrace_1162033
  have hstable : (prefixWord ++ tailWord_1162033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162033).length < 2 ^ (prefixWord ++ tailWord_1162033).sum := by decide
  have hdescent : baseEnd_1162033 < baseStart_1162033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162064 : List Nat := [2, 1, 1, 1, 1, 4, 6, 5]
def baseStart_1162064 : Nat := 118140960795 + 1162064 * 2 ^ 59
def prefixEnd_1162064 : Nat := 4983230072969 + 3 ^ 40 * 1162064 * 2
def baseEnd_1162064 : Nat := 88399612338732837474929

theorem tailTrace_1162064 : CollatzResearch.WordTrace tailWord_1162064 prefixEnd_1162064 88399612338732837474929 := by
  unfold tailWord_1162064
  simp only [CollatzResearch.WordTrace]
  refine ⟨21191978031024033787862623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28255970708032045050483497 21191978031024033787862623)
  ·
    refine ⟨31787967046536050681793935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21191978031024033787862623 31787967046536050681793935)
    ·
      refine ⟨47681950569804076022690903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31787967046536050681793935 47681950569804076022690903)
      ·
        refine ⟨71522925854706114034036355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47681950569804076022690903 71522925854706114034036355)
        ·
          refine ⟨107284388782059171051054533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71522925854706114034036355 107284388782059171051054533)
          ·
            refine ⟨20115822896636094572072725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107284388782059171051054533 20115822896636094572072725)
            ·
              refine ⟨942929198279816933065909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20115822896636094572072725 942929198279816933065909)
              ·
                refine ⟨88399612338732837474929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 942929198279816933065909 88399612338732837474929)
                ·
                  rfl

theorem cell21_1162064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_1162064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162064 prefixEnd_1162064 := by exact prefixLift 1162064
  have htrace : WordTrace (prefixWord ++ tailWord_1162064) baseStart_1162064 baseEnd_1162064 := by
    simpa [prefixWord, tailWord_1162064, baseEnd_1162064] using wordTrace_append hprefix tailTrace_1162064
  have hstable : (prefixWord ++ tailWord_1162064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162064).length < 2 ^ (prefixWord ++ tailWord_1162064).sum := by decide
  have hdescent : baseEnd_1162064 < baseStart_1162064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162095 : List Nat := [1, 1, 2, 1, 3, 1, 1, 8, 3]
def baseStart_1162095 : Nat := 118140960795 + 1162095 * 2 ^ 59
def prefixEnd_1162095 : Nat := 4983230072969 + 3 ^ 40 * 1162095 * 2
def baseEnd_1162095 : Nat := 265205911638549347408057

theorem tailTrace_1162095 : CollatzResearch.WordTrace tailWord_1162095 prefixEnd_1162095 265205911638549347408057 := by
  unfold tailWord_1162095
  simp only [CollatzResearch.WordTrace]
  refine ⟨42385086724935759870103739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28256724483290506580069159 42385086724935759870103739)
  ·
    refine ⟨63577630087403639805155609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42385086724935759870103739 63577630087403639805155609)
    ·
      refine ⟨47683222565552729853866707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63577630087403639805155609 47683222565552729853866707)
      ·
        refine ⟨71524833848329094780800061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47683222565552729853866707 71524833848329094780800061)
        ·
          refine ⟨26821812693123410542800023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71524833848329094780800061 26821812693123410542800023)
          ·
            refine ⟨40232719039685115814200035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26821812693123410542800023 40232719039685115814200035)
            ·
              refine ⟨60349078559527673721300053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40232719039685115814200035 60349078559527673721300053)
              ·
                refine ⟨707215764369464926421485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 60349078559527673721300053 707215764369464926421485)
                ·
                  refine ⟨265205911638549347408057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707215764369464926421485 265205911638549347408057)
                  ·
                    rfl

theorem cell21_1162095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 3].length) (baseStart_1162095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162095 prefixEnd_1162095 := by exact prefixLift 1162095
  have htrace : WordTrace (prefixWord ++ tailWord_1162095) baseStart_1162095 baseEnd_1162095 := by
    simpa [prefixWord, tailWord_1162095, baseEnd_1162095] using wordTrace_append hprefix tailTrace_1162095
  have hstable : (prefixWord ++ tailWord_1162095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162095).length < 2 ^ (prefixWord ++ tailWord_1162095).sum := by decide
  have hdescent : baseEnd_1162095 < baseStart_1162095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162123 : List Nat := [1, 1, 1, 1, 4, 2, 4, 7]
def baseStart_1162123 : Nat := 118140960795 + 1162123 * 2 ^ 59
def prefixEnd_1162123 : Nat := 4983230072969 + 3 ^ 40 * 1162123 * 2
def baseEnd_1162123 : Nat := 88404100540009173647111

theorem tailTrace_1162123 : CollatzResearch.WordTrace tailWord_1162123 prefixEnd_1162123 88404100540009173647111 := by
  unfold tailWord_1162123
  simp only [CollatzResearch.WordTrace]
  refine ⟨42386107968834320652123023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28257405312556213768082015 42386107968834320652123023)
  ·
    refine ⟨63579161953251480978184535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42386107968834320652123023 63579161953251480978184535)
    ·
      refine ⟨95368742929877221467276803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63579161953251480978184535 95368742929877221467276803)
      ·
        refine ⟨143053114394815832200915205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95368742929877221467276803 143053114394815832200915205)
        ·
          refine ⟨26822458949027968537671601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143053114394815832200915205 26822458949027968537671601)
          ·
            refine ⟨20116844211770976403253701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26822458949027968537671601 20116844211770976403253701)
            ·
              refine ⟨3771908289707058075610069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20116844211770976403253701 3771908289707058075610069)
              ·
                refine ⟨88404100540009173647111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3771908289707058075610069 88404100540009173647111)
                ·
                  rfl

theorem cell21_1162123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_1162123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162123 prefixEnd_1162123 := by exact prefixLift 1162123
  have htrace : WordTrace (prefixWord ++ tailWord_1162123) baseStart_1162123 baseEnd_1162123 := by
    simpa [prefixWord, tailWord_1162123, baseEnd_1162123] using wordTrace_append hprefix tailTrace_1162123
  have hstable : (prefixWord ++ tailWord_1162123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162123).length < 2 ^ (prefixWord ++ tailWord_1162123).sum := by decide
  have hdescent : baseEnd_1162123 < baseStart_1162123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162140 : List Nat := [2, 2, 3, 3, 2, 9]
def baseStart_1162140 : Nat := 118140960795 + 1162140 * 2 ^ 59
def prefixEnd_1162140 : Nat := 4983230072969 + 3 ^ 40 * 1162140 * 2
def baseEnd_1162140 : Nat := 9822821527838491450295

theorem tailTrace_1162140 : CollatzResearch.WordTrace tailWord_1162140 prefixEnd_1162140 9822821527838491450295 := by
  unfold tailWord_1162140
  simp only [CollatzResearch.WordTrace]
  refine ⟨21193364004886366277745937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28257818673181821703661249 21193364004886366277745937)
  ·
    refine ⟨15895023003664774708309453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21193364004886366277745937 15895023003664774708309453)
    ·
      refine ⟨5960633626374290515616045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15895023003664774708309453 5960633626374290515616045)
      ·
        refine ⟨2235237609890358943356017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5960633626374290515616045 2235237609890358943356017)
        ·
          refine ⟨1676428207417769207517013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235237609890358943356017 1676428207417769207517013)
          ·
            refine ⟨9822821527838491450295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1676428207417769207517013 9822821527838491450295)
            ·
              rfl

theorem cell21_1162140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 9].length) (baseStart_1162140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162140 prefixEnd_1162140 := by exact prefixLift 1162140
  have htrace : WordTrace (prefixWord ++ tailWord_1162140) baseStart_1162140 baseEnd_1162140 := by
    simpa [prefixWord, tailWord_1162140, baseEnd_1162140] using wordTrace_append hprefix tailTrace_1162140
  have hstable : (prefixWord ++ tailWord_1162140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162140).length < 2 ^ (prefixWord ++ tailWord_1162140).sum := by decide
  have hdescent : baseEnd_1162140 < baseStart_1162140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162146 : List Nat := [3, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1162146 : Nat := 118140960795 + 1162146 * 2 ^ 59
def prefixEnd_1162146 : Nat := 4983230072969 + 3 ^ 40 * 1162146 * 2
def baseEnd_1162146 : Nat := 265217550533384592057953

theorem tailTrace_1162146 : CollatzResearch.WordTrace tailWord_1162146 prefixEnd_1162146 265217550533384592057953 := by
  unfold tailWord_1162146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596736711937748895052573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28257964565167330386806861 10596736711937748895052573)
  ·
    refine ⟨3973776266976655835644715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10596736711937748895052573 3973776266976655835644715)
    ·
      refine ⟨5960664400464983753467073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3973776266976655835644715 5960664400464983753467073)
      ·
        refine ⟨4470498300348737815100305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5960664400464983753467073 4470498300348737815100305)
        ·
          refine ⟨3352873725261553361325229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4470498300348737815100305 3352873725261553361325229)
          ·
            refine ⟨1257327646973082510496961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3352873725261553361325229 1257327646973082510496961)
            ·
              refine ⟨942995735229811882872721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257327646973082510496961 942995735229811882872721)
              ·
                refine ⟨707246801422358912154541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942995735229811882872721 707246801422358912154541)
                ·
                  refine ⟨265217550533384592057953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707246801422358912154541 265217550533384592057953)
                  ·
                    rfl

theorem cell21_1162146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1162146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162146 prefixEnd_1162146 := by exact prefixLift 1162146
  have htrace : WordTrace (prefixWord ++ tailWord_1162146) baseStart_1162146 baseEnd_1162146 := by
    simpa [prefixWord, tailWord_1162146, baseEnd_1162146] using wordTrace_append hprefix tailTrace_1162146
  have hstable : (prefixWord ++ tailWord_1162146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162146).length < 2 ^ (prefixWord ++ tailWord_1162146).sum := by decide
  have hdescent : baseEnd_1162146 < baseStart_1162146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162188 : List Nat := [2, 2, 1, 4, 1, 1, 4, 3, 3]
def baseStart_1162188 : Nat := 118140960795 + 1162188 * 2 ^ 59
def prefixEnd_1162188 : Nat := 4983230072969 + 3 ^ 40 * 1162188 * 2
def baseEnd_1162188 : Nat := 265227135505601852357867

theorem tailTrace_1162188 : CollatzResearch.WordTrace tailWord_1162188 prefixEnd_1162188 265227135505601852357867 := by
  unfold tailWord_1162188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21194239356799418376619609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28258985809065891168826145 21194239356799418376619609)
  ·
    refine ⟨15895679517599563782464707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21194239356799418376619609 15895679517599563782464707)
    ·
      refine ⟨23843519276399345673697061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15895679517599563782464707 23843519276399345673697061)
      ·
        refine ⟨4470659864324877313818199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23843519276399345673697061 4470659864324877313818199)
        ·
          refine ⟨6705989796487315970727299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470659864324877313818199 6705989796487315970727299)
          ·
            refine ⟨10058984694730973956090949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705989796487315970727299 10058984694730973956090949)
            ·
              refine ⟨1886059630262057616767053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10058984694730973956090949 1886059630262057616767053)
              ·
                refine ⟨707272361348271606287645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886059630262057616767053 707272361348271606287645)
                ·
                  refine ⟨265227135505601852357867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707272361348271606287645 265227135505601852357867)
                  ·
                    rfl

theorem cell21_1162188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_1162188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162188 prefixEnd_1162188 := by exact prefixLift 1162188
  have htrace : WordTrace (prefixWord ++ tailWord_1162188) baseStart_1162188 baseEnd_1162188 := by
    simpa [prefixWord, tailWord_1162188, baseEnd_1162188] using wordTrace_append hprefix tailTrace_1162188
  have hstable : (prefixWord ++ tailWord_1162188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162188).length < 2 ^ (prefixWord ++ tailWord_1162188).sum := by decide
  have hdescent : baseEnd_1162188 < baseStart_1162188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162202 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_1162202 : Nat := 118140960795 + 1162202 * 2 ^ 59
def prefixEnd_1162202 : Nat := 4983230072969 + 3 ^ 40 * 1162202 * 2
def baseEnd_1162202 : Nat := 265230330496340939124505

theorem tailTrace_1162202 : CollatzResearch.WordTrace tailWord_1162202 prefixEnd_1162202 265230330496340939124505 := by
  unfold tailWord_1162202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10597247333887029286062215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28259326223698744762832573 10597247333887029286062215)
  ·
    refine ⟨15895871000830543929093323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10597247333887029286062215 15895871000830543929093323)
    ·
      refine ⟨23843806501245815893639985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15895871000830543929093323 23843806501245815893639985)
      ·
        refine ⟨17882854875934361920229989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23843806501245815893639985 17882854875934361920229989)
        ·
          refine ⟨3353035289237692860043123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17882854875934361920229989 3353035289237692860043123)
          ·
            refine ⟨5029552933856539290064685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353035289237692860043123 5029552933856539290064685)
            ·
              refine ⟨1886082350196202233774257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5029552933856539290064685 1886082350196202233774257)
              ·
                refine ⟨1414561762647151675330693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886082350196202233774257 1414561762647151675330693)
                ·
                  refine ⟨265230330496340939124505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414561762647151675330693 265230330496340939124505)
                  ·
                    rfl

theorem cell21_1162202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_1162202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162202 prefixEnd_1162202 := by exact prefixLift 1162202
  have htrace : WordTrace (prefixWord ++ tailWord_1162202) baseStart_1162202 baseEnd_1162202 := by
    simpa [prefixWord, tailWord_1162202, baseEnd_1162202] using wordTrace_append hprefix tailTrace_1162202
  have hstable : (prefixWord ++ tailWord_1162202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162202).length < 2 ^ (prefixWord ++ tailWord_1162202).sum := by decide
  have hdescent : baseEnd_1162202 < baseStart_1162202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162261 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1162261 : Nat := 118140960795 + 1162261 * 2 ^ 59
def prefixEnd_1162261 : Nat := 4983230072969 + 3 ^ 40 * 1162261 * 2
def baseEnd_1162261 : Nat := 265243795100169947641051

theorem tailTrace_1162261 : CollatzResearch.WordTrace tailWord_1162261 prefixEnd_1162261 265243795100169947641051 := by
  unfold tailWord_1162261
  simp only [CollatzResearch.WordTrace]
  refine ⟨42391141242334370220646637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28260760828222913480431091 42391141242334370220646637)
  ·
    refine ⟨15896677965875388832742489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42391141242334370220646637 15896677965875388832742489)
    ·
      refine ⟨11922508474406541624556867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15896677965875388832742489 11922508474406541624556867)
      ·
        refine ⟨17883762711609812436835301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11922508474406541624556867 17883762711609812436835301)
        ·
          refine ⟨3353205508426839831906619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17883762711609812436835301 3353205508426839831906619)
          ·
            refine ⟨5029808262640259747859929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353205508426839831906619 5029808262640259747859929)
            ·
              refine ⟨3772356196980194810894947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029808262640259747859929 3772356196980194810894947)
              ·
                refine ⟨5658534295470292216342421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3772356196980194810894947 5658534295470292216342421)
                ·
                  refine ⟨265243795100169947641051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5658534295470292216342421 265243795100169947641051)
                  ·
                    rfl

theorem cell21_1162261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1162261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162261 prefixEnd_1162261 := by exact prefixLift 1162261
  have htrace : WordTrace (prefixWord ++ tailWord_1162261) baseStart_1162261 baseEnd_1162261 := by
    simpa [prefixWord, tailWord_1162261, baseEnd_1162261] using wordTrace_append hprefix tailTrace_1162261
  have hstable : (prefixWord ++ tailWord_1162261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162261).length < 2 ^ (prefixWord ++ tailWord_1162261).sum := by decide
  have hdescent : baseEnd_1162261 < baseStart_1162261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162275 : List Nat := [1, 1, 1, 4, 3, 2, 1, 8]
def baseStart_1162275 : Nat := 118140960795 + 1162275 * 2 ^ 59
def prefixEnd_1162275 : Nat := 4983230072969 + 3 ^ 40 * 1162275 * 2
def baseEnd_1162275 : Nat := 88415663363636344802563

theorem tailTrace_1162275 : CollatzResearch.WordTrace tailWord_1162275 prefixEnd_1162275 88415663363636344802563 := by
  unfold tailWord_1162275
  simp only [CollatzResearch.WordTrace]
  refine ⟨42391651864283650611656279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28261101242855767074437519 42391651864283650611656279)
  ·
    refine ⟨63587477796425475917484419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42391651864283650611656279 63587477796425475917484419)
    ·
      refine ⟨95381216694638213876226629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63587477796425475917484419 95381216694638213876226629)
      ·
        refine ⟨17883978130244665101792493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95381216694638213876226629 17883978130244665101792493)
        ·
          refine ⟨6706491798841749413172185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17883978130244665101792493 6706491798841749413172185)
          ·
            refine ⟨5029868849131312059879139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6706491798841749413172185 5029868849131312059879139)
            ·
              refine ⟨7544803273696968089818709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5029868849131312059879139 7544803273696968089818709)
              ·
                refine ⟨88415663363636344802563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7544803273696968089818709 88415663363636344802563)
                ·
                  rfl

theorem cell21_1162275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_1162275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162275 prefixEnd_1162275 := by exact prefixLift 1162275
  have htrace : WordTrace (prefixWord ++ tailWord_1162275) baseStart_1162275 baseEnd_1162275 := by
    simpa [prefixWord, tailWord_1162275, baseEnd_1162275] using wordTrace_append hprefix tailTrace_1162275
  have hstable : (prefixWord ++ tailWord_1162275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162275).length < 2 ^ (prefixWord ++ tailWord_1162275).sum := by decide
  have hdescent : baseEnd_1162275 < baseStart_1162275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162320 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_1162320 : Nat := 118140960795 + 1162320 * 2 ^ 59
def prefixEnd_1162320 : Nat := 4983230072969 + 3 ^ 40 * 1162320 * 2
def baseEnd_1162320 : Nat := 265257259703998956157597

theorem tailTrace_1162320 : CollatzResearch.WordTrace tailWord_1162320 prefixEnd_1162320 265257259703998956157597 := by
  unfold tailWord_1162320
  simp only [CollatzResearch.WordTrace]
  refine ⟨21196646574560311648522207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28262195432747082198029609 21196646574560311648522207)
  ·
    refine ⟨31794969861840467472783311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21196646574560311648522207 31794969861840467472783311)
    ·
      refine ⟨47692454792760701209174967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31794969861840467472783311 47692454792760701209174967)
      ·
        refine ⟨71538682189141051813762451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47692454792760701209174967 71538682189141051813762451)
        ·
          refine ⟨107308023283711577720643677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71538682189141051813762451 107308023283711577720643677)
          ·
            refine ⟨40240508731391841645241379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107308023283711577720643677 40240508731391841645241379)
            ·
              refine ⟨60360763097087762467862069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40240508731391841645241379 60360763097087762467862069)
              ·
                refine ⟨5658821540351977731362069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60360763097087762467862069 5658821540351977731362069)
                ·
                  refine ⟨265257259703998956157597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5658821540351977731362069 265257259703998956157597)
                  ·
                    rfl

theorem cell21_1162320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_1162320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162320 prefixEnd_1162320 := by exact prefixLift 1162320
  have htrace : WordTrace (prefixWord ++ tailWord_1162320) baseStart_1162320 baseEnd_1162320 := by
    simpa [prefixWord, tailWord_1162320, baseEnd_1162320] using wordTrace_append hprefix tailTrace_1162320
  have hstable : (prefixWord ++ tailWord_1162320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162320).length < 2 ^ (prefixWord ++ tailWord_1162320).sum := by decide
  have hdescent : baseEnd_1162320 < baseStart_1162320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162337 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 4]
def baseStart_1162337 : Nat := 118140960795 + 1162337 * 2 ^ 59
def prefixEnd_1162337 : Nat := 4983230072969 + 3 ^ 40 * 1162337 * 2
def baseEnd_1162337 : Nat := 265261139335610704374229

theorem tailTrace_1162337 : CollatzResearch.WordTrace tailWord_1162337 prefixEnd_1162337 265261139335610704374229 := by
  unfold tailWord_1162337
  simp only [CollatzResearch.WordTrace]
  refine ⟨42393913190059035200413265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28262608793372690133608843 42393913190059035200413265)
  ·
    refine ⟨31795434892544276400309949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42393913190059035200413265 31795434892544276400309949)
    ·
      refine ⟨11923288084704103650116231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31795434892544276400309949 11923288084704103650116231)
      ·
        refine ⟨17884932127056155475174347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11923288084704103650116231 17884932127056155475174347)
        ·
          refine ⟨26827398190584233212761521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17884932127056155475174347 26827398190584233212761521)
          ·
            refine ⟨20120548642938174909571141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26827398190584233212761521 20120548642938174909571141)
            ·
              refine ⟨3772602870550907795544589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20120548642938174909571141 3772602870550907795544589)
              ·
                refine ⟨1414726076456590423329221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3772602870550907795544589 1414726076456590423329221)
                ·
                  refine ⟨265261139335610704374229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414726076456590423329221 265261139335610704374229)
                  ·
                    rfl

theorem cell21_1162337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_1162337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162337 prefixEnd_1162337 := by exact prefixLift 1162337
  have htrace : WordTrace (prefixWord ++ tailWord_1162337) baseStart_1162337 baseEnd_1162337 := by
    simpa [prefixWord, tailWord_1162337, baseEnd_1162337] using wordTrace_append hprefix tailTrace_1162337
  have hstable : (prefixWord ++ tailWord_1162337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162337).length < 2 ^ (prefixWord ++ tailWord_1162337).sum := by decide
  have hdescent : baseEnd_1162337 < baseStart_1162337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162402 : List Nat := [3, 3, 1, 3, 2, 2, 2, 5]
def baseStart_1162402 : Nat := 118140960795 + 1162402 * 2 ^ 59
def prefixEnd_1162402 : Nat := 4983230072969 + 3 ^ 40 * 1162402 * 2
def baseEnd_1162402 : Nat := 88425324407061678596921

theorem tailTrace_1162402 : CollatzResearch.WordTrace tailWord_1162402 prefixEnd_1162402 88425324407061678596921 := by
  unfold tailWord_1162402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10599070983705887825382365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28264189289882367534352973 10599070983705887825382365)
  ·
    refine ⟨3974651618889707934518387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10599070983705887825382365 3974651618889707934518387)
    ·
      refine ⟨5961977428334561901777581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974651618889707934518387 5961977428334561901777581)
      ·
        refine ⟨2235741535625460713166593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5961977428334561901777581 2235741535625460713166593)
        ·
          refine ⟨1676806151719095534874945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235741535625460713166593 1676806151719095534874945)
          ·
            refine ⟨1257604613789321651156209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676806151719095534874945 1257604613789321651156209)
            ·
              refine ⟨943203460341991238367157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257604613789321651156209 943203460341991238367157)
              ·
                refine ⟨88425324407061678596921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 943203460341991238367157 88425324407061678596921)
                ·
                  rfl

theorem cell21_1162402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_1162402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162402 prefixEnd_1162402 := by exact prefixLift 1162402
  have htrace : WordTrace (prefixWord ++ tailWord_1162402) baseStart_1162402 baseEnd_1162402 := by
    simpa [prefixWord, tailWord_1162402, baseEnd_1162402] using wordTrace_append hprefix tailTrace_1162402
  have hstable : (prefixWord ++ tailWord_1162402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162402).length < 2 ^ (prefixWord ++ tailWord_1162402).sum := by decide
  have hdescent : baseEnd_1162402 < baseStart_1162402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162484 : List Nat := [2, 6, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1162484 : Nat := 118140960795 + 1162484 * 2 ^ 59
def prefixEnd_1162484 : Nat := 4983230072969 + 3 ^ 40 * 1162484 * 2
def baseEnd_1162484 : Nat := 265294686738371115423929

theorem tailTrace_1162484 : CollatzResearch.WordTrace tailWord_1162484 prefixEnd_1162484 265294686738371115423929 := by
  unfold tailWord_1162484
  simp only [CollatzResearch.WordTrace]
  refine ⟨21199637360263239653007253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28266183147017652870676337 21199637360263239653007253)
  ·
    refine ⟨993733001262339358734715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21199637360263239653007253 993733001262339358734715)
    ·
      refine ⟨1490599501893509038102073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993733001262339358734715 1490599501893509038102073)
      ·
        refine ⟨1117949626420131778576555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1490599501893509038102073 1117949626420131778576555)
        ·
          refine ⟨1676924439630197667864833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117949626420131778576555 1676924439630197667864833)
          ·
            refine ⟨1257693329722648250898625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676924439630197667864833 1257693329722648250898625)
            ·
              refine ⟨943269997291986188173969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257693329722648250898625 943269997291986188173969)
              ·
                refine ⟨707452497968989641130477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943269997291986188173969 707452497968989641130477)
                ·
                  refine ⟨265294686738371115423929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707452497968989641130477 265294686738371115423929)
                  ·
                    rfl

theorem cell21_1162484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1162484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162484 prefixEnd_1162484 := by exact prefixLift 1162484
  have htrace : WordTrace (prefixWord ++ tailWord_1162484) baseStart_1162484 baseEnd_1162484 := by
    simpa [prefixWord, tailWord_1162484, baseEnd_1162484] using wordTrace_append hprefix tailTrace_1162484
  have hstable : (prefixWord ++ tailWord_1162484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162484).length < 2 ^ (prefixWord ++ tailWord_1162484).sum := by decide
  have hdescent : baseEnd_1162484 < baseStart_1162484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162489 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 4]
def baseStart_1162489 : Nat := 118140960795 + 1162489 * 2 ^ 59
def prefixEnd_1162489 : Nat := 4983230072969 + 3 ^ 40 * 1162489 * 2
def baseEnd_1162489 : Nat := 265295827806492217840585

theorem tailTrace_1162489 : CollatzResearch.WordTrace tailWord_1162489 prefixEnd_1162489 265295827806492217840585 := by
  unfold tailWord_1162489
  simp only [CollatzResearch.WordTrace]
  refine ⟨42399457085508365159946521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28266304723672243439964347 42399457085508365159946521)
  ·
    refine ⟨31799592814131273869959891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42399457085508365159946521 31799592814131273869959891)
    ·
      refine ⟨47699389221196910804939837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31799592814131273869959891 47699389221196910804939837)
      ·
        refine ⟨17887270957948841551852439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47699389221196910804939837 17887270957948841551852439)
        ·
          refine ⟨26830906436923262327778659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17887270957948841551852439 26830906436923262327778659)
          ·
            refine ⟨40246359655384893491667989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26830906436923262327778659 40246359655384893491667989)
            ·
              refine ⟨1886548108846166882421937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40246359655384893491667989 1886548108846166882421937)
              ·
                refine ⟨1414911081634625161816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886548108846166882421937 1414911081634625161816453)
                ·
                  refine ⟨265295827806492217840585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1414911081634625161816453 265295827806492217840585)
                  ·
                    rfl

theorem cell21_1162489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_1162489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162489 prefixEnd_1162489 := by exact prefixLift 1162489
  have htrace : WordTrace (prefixWord ++ tailWord_1162489) baseStart_1162489 baseEnd_1162489 := by
    simpa [prefixWord, tailWord_1162489, baseEnd_1162489] using wordTrace_append hprefix tailTrace_1162489
  have hstable : (prefixWord ++ tailWord_1162489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162489).length < 2 ^ (prefixWord ++ tailWord_1162489).sum := by decide
  have hdescent : baseEnd_1162489 < baseStart_1162489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162492 : List Nat := [2, 2, 2, 1, 5, 1, 1, 4, 3]
def baseStart_1162492 : Nat := 118140960795 + 1162492 * 2 ^ 59
def prefixEnd_1162492 : Nat := 4983230072969 + 3 ^ 40 * 1162492 * 2
def baseEnd_1162492 : Nat := 265296512447364879290579

theorem tailTrace_1162492 : CollatzResearch.WordTrace tailWord_1162492 prefixEnd_1162492 265296512447364879290579 := by
  unfold tailWord_1162492
  simp only [CollatzResearch.WordTrace]
  refine ⟨21199783252248748336152865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28266377669664997781537153 21199783252248748336152865)
  ·
    refine ⟨15899837439186561252114649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21199783252248748336152865 15899837439186561252114649)
    ·
      refine ⟨11924878079389920939085987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15899837439186561252114649 11924878079389920939085987)
      ·
        refine ⟨17887317119084881408628981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11924878079389920939085987 17887317119084881408628981)
        ·
          refine ⟨1676935979914207632058967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17887317119084881408628981 1676935979914207632058967)
          ·
            refine ⟨2515403969871311448088451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676935979914207632058967 2515403969871311448088451)
            ·
              refine ⟨3773105954806967172132677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515403969871311448088451 3773105954806967172132677)
              ·
                refine ⟨707457366526306344774877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3773105954806967172132677 707457366526306344774877)
                ·
                  refine ⟨265296512447364879290579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707457366526306344774877 265296512447364879290579)
                  ·
                    rfl

theorem cell21_1162492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_1162492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162492 prefixEnd_1162492 := by exact prefixLift 1162492
  have htrace : WordTrace (prefixWord ++ tailWord_1162492) baseStart_1162492 baseEnd_1162492 := by
    simpa [prefixWord, tailWord_1162492, baseEnd_1162492] using wordTrace_append hprefix tailTrace_1162492
  have hstable : (prefixWord ++ tailWord_1162492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162492).length < 2 ^ (prefixWord ++ tailWord_1162492).sum := by decide
  have hdescent : baseEnd_1162492 < baseStart_1162492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162520 : List Nat := [2, 1, 2, 3, 1, 4, 3, 5]
def baseStart_1162520 : Nat := 118140960795 + 1162520 * 2 ^ 59
def prefixEnd_1162520 : Nat := 4983230072969 + 3 ^ 40 * 1162520 * 2
def baseEnd_1162520 : Nat := 88434300809614350941285

theorem tailTrace_1162520 : CollatzResearch.WordTrace tailWord_1162520 prefixEnd_1162520 88434300809614350941285 := by
  unfold tailWord_1162520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21200293874198028727162507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28267058498930704969550009 21200293874198028727162507)
  ·
    refine ⟨31800440811297043090743761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21200293874198028727162507 31800440811297043090743761)
    ·
      refine ⟨23850330608472782318057821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31800440811297043090743761 23850330608472782318057821)
      ·
        refine ⟨8943873978177293369271683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23850330608472782318057821 8943873978177293369271683)
        ·
          refine ⟨13415810967265940053907525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8943873978177293369271683 13415810967265940053907525)
          ·
            refine ⟨2515464556362363760107661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13415810967265940053907525 2515464556362363760107661)
            ·
              refine ⟨943299208635886410040373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2515464556362363760107661 943299208635886410040373)
              ·
                refine ⟨88434300809614350941285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 943299208635886410040373 88434300809614350941285)
                ·
                  rfl

theorem cell21_1162520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_1162520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162520 prefixEnd_1162520 := by exact prefixLift 1162520
  have htrace : WordTrace (prefixWord ++ tailWord_1162520) baseStart_1162520 baseEnd_1162520 := by
    simpa [prefixWord, tailWord_1162520, baseEnd_1162520] using wordTrace_append hprefix tailTrace_1162520
  have hstable : (prefixWord ++ tailWord_1162520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162520).length < 2 ^ (prefixWord ++ tailWord_1162520).sum := by decide
  have hdescent : baseEnd_1162520 < baseStart_1162520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162526 : List Nat := [4, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1162526 : Nat := 118140960795 + 1162526 * 2 ^ 59
def prefixEnd_1162526 : Nat := 4983230072969 + 3 ^ 40 * 1162526 * 2
def baseEnd_1162526 : Nat := 265304271710588375723843

theorem tailTrace_1162526 : CollatzResearch.WordTrace tailWord_1162526 prefixEnd_1162526 265304271710588375723843 := by
  unfold tailWord_1162526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300100823296790059880429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28267204390916213652695621 5300100823296790059880429)
  ·
    refine ⟨1987537808736296272455161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5300100823296790059880429 1987537808736296272455161)
    ·
      refine ⟨1490653356552222204341371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1987537808736296272455161 1490653356552222204341371)
      ·
        refine ⟨2235980034828333306512057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490653356552222204341371 2235980034828333306512057)
        ·
          refine ⟨1676985026121249979884043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235980034828333306512057 1676985026121249979884043)
          ·
            refine ⟨2515477539181874969826065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676985026121249979884043 2515477539181874969826065)
            ·
              refine ⟨1886608154386406227369549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2515477539181874969826065 1886608154386406227369549)
              ·
                refine ⟨707478057894902335263581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886608154386406227369549 707478057894902335263581)
                ·
                  refine ⟨265304271710588375723843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707478057894902335263581 265304271710588375723843)
                  ·
                    rfl

theorem cell21_1162526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1162526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162526 prefixEnd_1162526 := by exact prefixLift 1162526
  have htrace : WordTrace (prefixWord ++ tailWord_1162526) baseStart_1162526 baseEnd_1162526 := by
    simpa [prefixWord, tailWord_1162526, baseEnd_1162526] using wordTrace_append hprefix tailTrace_1162526
  have hstable : (prefixWord ++ tailWord_1162526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162526).length < 2 ^ (prefixWord ++ tailWord_1162526).sum := by decide
  have hdescent : baseEnd_1162526 < baseStart_1162526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162593 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 7]
def baseStart_1162593 : Nat := 118140960795 + 1162593 * 2 ^ 59
def prefixEnd_1162593 : Nat := 4983230072969 + 3 ^ 40 * 1162593 * 2
def baseEnd_1162593 : Nat := 265319562023411148107039

theorem tailTrace_1162593 : CollatzResearch.WordTrace tailWord_1162593 prefixEnd_1162593 265319562023411148107039 := by
  unfold tailWord_1162593
  simp only [CollatzResearch.WordTrace]
  refine ⟨42403250277131590921732433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28268833518087727281154955 42403250277131590921732433)
  ·
    refine ⟨31802437707848693191299325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42403250277131590921732433 31802437707848693191299325)
    ·
      refine ⟨11925914140443259946737247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31802437707848693191299325 11925914140443259946737247)
      ·
        refine ⟨17888871210664889920105871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11925914140443259946737247 17888871210664889920105871)
        ·
          refine ⟨26833306815997334880158807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17888871210664889920105871 26833306815997334880158807)
          ·
            refine ⟨40249960223996002320238211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26833306815997334880158807 40249960223996002320238211)
            ·
              refine ⟨60374940335994003480357317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40249960223996002320238211 60374940335994003480357317)
              ·
                refine ⟨11320301312998875652566997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60374940335994003480357317 11320301312998875652566997)
                ·
                  refine ⟨265319562023411148107039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11320301312998875652566997 265319562023411148107039)
                  ·
                    rfl

theorem cell21_1162593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_1162593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162593 prefixEnd_1162593 := by exact prefixLift 1162593
  have htrace : WordTrace (prefixWord ++ tailWord_1162593) baseStart_1162593 baseEnd_1162593 := by
    simpa [prefixWord, tailWord_1162593, baseEnd_1162593] using wordTrace_append hprefix tailTrace_1162593
  have hstable : (prefixWord ++ tailWord_1162593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162593).length < 2 ^ (prefixWord ++ tailWord_1162593).sum := by decide
  have hdescent : baseEnd_1162593 < baseStart_1162593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162658 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1162658 : Nat := 118140960795 + 1162658 * 2 ^ 59
def prefixEnd_1162658 : Nat := 4983230072969 + 3 ^ 40 * 1162658 * 2
def baseEnd_1162658 : Nat := 265334395908985479523573

theorem tailTrace_1162658 : CollatzResearch.WordTrace tailWord_1162658 prefixEnd_1162658 265334395908985479523573 := by
  unfold tailWord_1162658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10601405255474026755712157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28270414014597404681899085 10601405255474026755712157)
  ·
    refine ⟨3975526970802760033392059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10601405255474026755712157 3975526970802760033392059)
    ·
      refine ⟨5963290456204140050088089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975526970802760033392059 5963290456204140050088089)
      ·
        refine ⟨4472467842153105037566067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5963290456204140050088089 4472467842153105037566067)
        ·
          refine ⟨6708701763229657556349101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472467842153105037566067 6708701763229657556349101)
          ·
            refine ⟨2515763161211121583630913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6708701763229657556349101 2515763161211121583630913)
            ·
              refine ⟨1886822370908341187723185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2515763161211121583630913 1886822370908341187723185)
              ·
                refine ⟨1415116778181255890792389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886822370908341187723185 1415116778181255890792389)
                ·
                  refine ⟨265334395908985479523573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1415116778181255890792389 265334395908985479523573)
                  ·
                    rfl

theorem cell21_1162658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1162658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162658 prefixEnd_1162658 := by exact prefixLift 1162658
  have htrace : WordTrace (prefixWord ++ tailWord_1162658) baseStart_1162658 baseEnd_1162658 := by
    simpa [prefixWord, tailWord_1162658, baseEnd_1162658] using wordTrace_append hprefix tailTrace_1162658
  have hstable : (prefixWord ++ tailWord_1162658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162658).length < 2 ^ (prefixWord ++ tailWord_1162658).sum := by decide
  have hdescent : baseEnd_1162658 < baseStart_1162658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162717 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1162717 : Nat := 118140960795 + 1162717 * 2 ^ 59
def prefixEnd_1162717 : Nat := 4983230072969 + 3 ^ 40 * 1162717 * 2
def baseEnd_1162717 : Nat := 265347860512814488040119

theorem tailTrace_1162717 : CollatzResearch.WordTrace tailWord_1162717 prefixEnd_1162717 265347860512814488040119 := by
  unfold tailWord_1162717
  simp only [CollatzResearch.WordTrace]
  refine ⟨42407772928682360099246405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28271848619121573399497603 42407772928682360099246405)
  ·
    refine ⟨7951457424127942518608701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42407772928682360099246405 7951457424127942518608701)
    ·
      refine ⟨2981796534047978444478263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7951457424127942518608701 2981796534047978444478263)
      ·
        refine ⟨4472694801071967666717395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981796534047978444478263 4472694801071967666717395)
        ·
          refine ⟨6709042201607951500076093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472694801071967666717395 6709042201607951500076093)
          ·
            refine ⟨2515890825602981812528535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6709042201607951500076093 2515890825602981812528535)
            ·
              refine ⟨3773836238404472718792803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515890825602981812528535 3773836238404472718792803)
              ·
                refine ⟨5660754357606709078189205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773836238404472718792803 5660754357606709078189205)
                ·
                  refine ⟨265347860512814488040119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5660754357606709078189205 265347860512814488040119)
                  ·
                    rfl

theorem cell21_1162717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1162717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162717 prefixEnd_1162717 := by exact prefixLift 1162717
  have htrace : WordTrace (prefixWord ++ tailWord_1162717) baseStart_1162717 baseEnd_1162717 := by
    simpa [prefixWord, tailWord_1162717, baseEnd_1162717] using wordTrace_append hprefix tailTrace_1162717
  have hstable : (prefixWord ++ tailWord_1162717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162717).length < 2 ^ (prefixWord ++ tailWord_1162717).sum := by decide
  have hdescent : baseEnd_1162717 < baseStart_1162717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162734 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1162734 : Nat := 118140960795 + 1162734 * 2 ^ 59
def prefixEnd_1162734 : Nat := 4983230072969 + 3 ^ 40 * 1162734 * 2
def baseEnd_1162734 : Nat := 265351740144426236256751

theorem tailTrace_1162734 : CollatzResearch.WordTrace tailWord_1162734 prefixEnd_1162734 265351740144426236256751 := by
  unfold tailWord_1162734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5301049121202596500326907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28272261979747181335076837 5301049121202596500326907)
  ·
    refine ⟨7951573681803894750490361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5301049121202596500326907 7951573681803894750490361)
    ·
      refine ⟨5963680261352921062867771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7951573681803894750490361 5963680261352921062867771)
      ·
        refine ⟨8945520392029381594301657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5963680261352921062867771 8945520392029381594301657)
        ·
          refine ⟨6709140294022036195726243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8945520392029381594301657 6709140294022036195726243)
          ·
            refine ⟨10063710441033054293589365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6709140294022036195726243 10063710441033054293589365)
            ·
              refine ⟨943472853846848840024003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10063710441033054293589365 943472853846848840024003)
              ·
                refine ⟨1415209280770273260036005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943472853846848840024003 1415209280770273260036005)
                ·
                  refine ⟨265351740144426236256751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1415209280770273260036005 265351740144426236256751)
                  ·
                    rfl

theorem cell21_1162734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1162734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162734 prefixEnd_1162734 := by exact prefixLift 1162734
  have htrace : WordTrace (prefixWord ++ tailWord_1162734) baseStart_1162734 baseEnd_1162734 := by
    simpa [prefixWord, tailWord_1162734, baseEnd_1162734] using wordTrace_append hprefix tailTrace_1162734
  have hstable : (prefixWord ++ tailWord_1162734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162734).length < 2 ^ (prefixWord ++ tailWord_1162734).sum := by decide
  have hdescent : baseEnd_1162734 < baseStart_1162734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162948 : List Nat := [2, 3, 3, 1, 1, 1, 5, 2, 3]
def baseStart_1162948 : Nat := 118140960795 + 1162948 * 2 ^ 59
def prefixEnd_1162948 : Nat := 4983230072969 + 3 ^ 40 * 1162948 * 2
def baseEnd_1162948 : Nat := 265400577860009419689647

theorem tailTrace_1162948 : CollatzResearch.WordTrace tailWord_1162948 prefixEnd_1162948 265400577860009419689647 := by
  unfold tailWord_1162948
  simp only [CollatzResearch.WordTrace]
  refine ⟨21208099095422743275452749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28277465460563657700603665 21208099095422743275452749)
  ·
    refine ⟨7953037160783528728294781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21208099095422743275452749 7953037160783528728294781)
    ·
      refine ⟨2982388935293823273110543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7953037160783528728294781 2982388935293823273110543)
      ·
        refine ⟨4473583402940734909665815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2982388935293823273110543 4473583402940734909665815)
        ·
          refine ⟨6710375104411102364498723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4473583402940734909665815 6710375104411102364498723)
          ·
            refine ⟨10065562656616653546748085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6710375104411102364498723 10065562656616653546748085)
            ·
              refine ⟨943646499057811270007633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10065562656616653546748085 943646499057811270007633)
              ·
                refine ⟨707734874293358452505725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943646499057811270007633 707734874293358452505725)
                ·
                  refine ⟨265400577860009419689647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707734874293358452505725 265400577860009419689647)
                  ·
                    rfl

theorem cell21_1162948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_1162948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162948 prefixEnd_1162948 := by exact prefixLift 1162948
  have htrace : WordTrace (prefixWord ++ tailWord_1162948) baseStart_1162948 baseEnd_1162948 := by
    simpa [prefixWord, tailWord_1162948, baseEnd_1162948] using wordTrace_append hprefix tailTrace_1162948
  have hstable : (prefixWord ++ tailWord_1162948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162948).length < 2 ^ (prefixWord ++ tailWord_1162948).sum := by decide
  have hdescent : baseEnd_1162948 < baseStart_1162948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162962 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_1162962 : Nat := 118140960795 + 1162962 * 2 ^ 59
def prefixEnd_1162962 : Nat := 4983230072969 + 3 ^ 40 * 1162962 * 2
def baseEnd_1162962 : Nat := 265403772850748506456285

theorem tailTrace_1162962 : CollatzResearch.WordTrace tailWord_1162962 prefixEnd_1162962 265403772850748506456285 := by
  unfold tailWord_1162962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10604177203198691735478785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28277805875196511294610093 10604177203198691735478785)
  ·
    refine ⟨7953132902399018801609089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10604177203198691735478785 7953132902399018801609089)
    ·
      refine ⟨5964849676799264101206817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7953132902399018801609089 5964849676799264101206817)
      ·
        refine ⟨4473637257599448075905113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5964849676799264101206817 4473637257599448075905113)
        ·
          refine ⟨3355227943199586056928835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4473637257599448075905113 3355227943199586056928835)
          ·
            refine ⟨5032841914799379085393253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355227943199586056928835 5032841914799379085393253)
            ·
              refine ⟨943657859024883578511235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5032841914799379085393253 943657859024883578511235)
              ·
                refine ⟨1415486788537325367766853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943657859024883578511235 1415486788537325367766853)
                ·
                  refine ⟨265403772850748506456285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1415486788537325367766853 265403772850748506456285)
                  ·
                    rfl

theorem cell21_1162962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_1162962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162962 prefixEnd_1162962 := by exact prefixLift 1162962
  have htrace : WordTrace (prefixWord ++ tailWord_1162962) baseStart_1162962 baseEnd_1162962 := by
    simpa [prefixWord, tailWord_1162962, baseEnd_1162962] using wordTrace_append hprefix tailTrace_1162962
  have hstable : (prefixWord ++ tailWord_1162962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162962).length < 2 ^ (prefixWord ++ tailWord_1162962).sum := by decide
  have hdescent : baseEnd_1162962 < baseStart_1162962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162987 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 8]
def baseStart_1162987 : Nat := 118140960795 + 1162987 * 2 ^ 59
def prefixEnd_1162987 : Nat := 4983230072969 + 3 ^ 40 * 1162987 * 2
def baseEnd_1162987 : Nat := 265409478191354018539567

theorem tailTrace_1162987 : CollatzResearch.WordTrace tailWord_1162987 prefixEnd_1162987 265409478191354018539567 := by
  unfold tailWord_1162987
  simp only [CollatzResearch.WordTrace]
  refine ⟨42417620637704196211575215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28278413758469464141050143 42417620637704196211575215)
  ·
    refine ⟨63626430956556294317362823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42417620637704196211575215 63626430956556294317362823)
    ·
      refine ⟨95439646434834441476044235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63626430956556294317362823 95439646434834441476044235)
      ·
        refine ⟨143159469652251662214066353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95439646434834441476044235 143159469652251662214066353)
        ·
          refine ⟨107369602239188746660549765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143159469652251662214066353 107369602239188746660549765)
          ·
            refine ⟨20131800419847889998853081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107369602239188746660549765 20131800419847889998853081)
            ·
              refine ⟨15098850314885917499139811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20131800419847889998853081 15098850314885917499139811)
              ·
                refine ⟨22648275472328876248709717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15098850314885917499139811 22648275472328876248709717)
                ·
                  refine ⟨265409478191354018539567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22648275472328876248709717 265409478191354018539567)
                  ·
                    rfl

theorem cell21_1162987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_1162987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1162987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1162987 prefixEnd_1162987 := by exact prefixLift 1162987
  have htrace : WordTrace (prefixWord ++ tailWord_1162987) baseStart_1162987 baseEnd_1162987 := by
    simpa [prefixWord, tailWord_1162987, baseEnd_1162987] using wordTrace_append hprefix tailTrace_1162987
  have hstable : (prefixWord ++ tailWord_1162987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162987).length < 2 ^ (prefixWord ++ tailWord_1162987).sum := by decide
  have hdescent : baseEnd_1162987 < baseStart_1162987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163007 : List Nat := [1, 1, 2, 2, 1, 3, 6, 2, 3]
def baseStart_1163007 : Nat := 118140960795 + 1163007 * 2 ^ 59
def prefixEnd_1163007 : Nat := 4983230072969 + 3 ^ 40 * 1163007 * 2
def baseEnd_1163007 : Nat := 265414042463838428206193

theorem tailTrace_1163007 : CollatzResearch.WordTrace tailWord_1163007 prefixEnd_1163007 265414042463838428206193 := by
  unfold tailWord_1163007
  simp only [CollatzResearch.WordTrace]
  refine ⟨42418350097631739627303275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28278900065087826418202183 42418350097631739627303275)
  ·
    refine ⟨63627525146447609440954913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42418350097631739627303275 63627525146447609440954913)
    ·
      refine ⟨47720643859835707080716185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63627525146447609440954913 47720643859835707080716185)
      ·
        refine ⟨35790482894876780310537139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47720643859835707080716185 35790482894876780310537139)
        ·
          refine ⟨53685724342315170465805709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35790482894876780310537139 53685724342315170465805709)
          ·
            refine ⟨20132146628368188924677141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53685724342315170465805709 20132146628368188924677141)
            ·
              refine ⟨943694373204758855844241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20132146628368188924677141 943694373204758855844241)
              ·
                refine ⟨707770779903569141883181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943694373204758855844241 707770779903569141883181)
                ·
                  refine ⟨265414042463838428206193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 707770779903569141883181 265414042463838428206193)
                  ·
                    rfl

theorem cell21_1163007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 3].length) (baseStart_1163007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163007 prefixEnd_1163007 := by exact prefixLift 1163007
  have htrace : WordTrace (prefixWord ++ tailWord_1163007) baseStart_1163007 baseEnd_1163007 := by
    simpa [prefixWord, tailWord_1163007, baseEnd_1163007] using wordTrace_append hprefix tailTrace_1163007
  have hstable : (prefixWord ++ tailWord_1163007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163007).length < 2 ^ (prefixWord ++ tailWord_1163007).sum := by decide
  have hdescent : baseEnd_1163007 < baseStart_1163007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163066 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_1163066 : Nat := 118140960795 + 1163066 * 2 ^ 59
def prefixEnd_1163066 : Nat := 4983230072969 + 3 ^ 40 * 1163066 * 2
def baseEnd_1163066 : Nat := 265427507067667436722739

theorem tailTrace_1163066 : CollatzResearch.WordTrace tailWord_1163066 prefixEnd_1163066 265427507067667436722739 := by
  unfold tailWord_1163066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605125501104498175925263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28280334669611995135800701 10605125501104498175925263)
  ·
    refine ⟨15907688251656747263887895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10605125501104498175925263 15907688251656747263887895)
    ·
      refine ⟨23861532377485120895831843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15907688251656747263887895 23861532377485120895831843)
      ·
        refine ⟨35792298566227681343747765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23861532377485120895831843 35792298566227681343747765)
        ·
          refine ⟨3355527990583845125976353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35792298566227681343747765 3355527990583845125976353)
          ·
            refine ⟨2516645992937883844482265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3355527990583845125976353 2516645992937883844482265)
            ·
              refine ⟨1887484494703412883361699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516645992937883844482265 1887484494703412883361699)
              ·
                refine ⟨2831226742055119325042549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887484494703412883361699 2831226742055119325042549)
                ·
                  refine ⟨265427507067667436722739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2831226742055119325042549 265427507067667436722739)
                  ·
                    rfl

theorem cell21_1163066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_1163066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163066 prefixEnd_1163066 := by exact prefixLift 1163066
  have htrace : WordTrace (prefixWord ++ tailWord_1163066) baseStart_1163066 baseEnd_1163066 := by
    simpa [prefixWord, tailWord_1163066, baseEnd_1163066] using wordTrace_append hprefix tailTrace_1163066
  have hstable : (prefixWord ++ tailWord_1163066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163066).length < 2 ^ (prefixWord ++ tailWord_1163066).sum := by decide
  have hdescent : baseEnd_1163066 < baseStart_1163066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163170 : List Nat := [3, 3, 1, 2, 12]
def baseStart_1163170 : Nat := 118140960795 + 1163170 * 2 ^ 59
def prefixEnd_1163170 : Nat := 4983230072969 + 3 ^ 40 * 1163170 * 2
def baseEnd_1163170 : Nat := 3277175818328226752953

theorem tailTrace_1163170 : CollatzResearch.WordTrace tailWord_1163170 prefixEnd_1163170 3277175818328226752953 := by
  unfold tailWord_1163170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10606073799010304616371741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28282863464027478976991309 10606073799010304616371741)
  ·
    refine ⟨3977277674628864231139403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10606073799010304616371741 3977277674628864231139403)
    ·
      refine ⟨5965916511943296346709105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3977277674628864231139403 5965916511943296346709105)
      ·
        refine ⟨4474437383957472260031829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5965916511943296346709105 4474437383957472260031829)
        ·
          refine ⟨3277175818328226752953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4474437383957472260031829 3277175818328226752953)
          ·
            rfl

theorem cell21_1163170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 12].length) (baseStart_1163170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163170 prefixEnd_1163170 := by exact prefixLift 1163170
  have htrace : WordTrace (prefixWord ++ tailWord_1163170) baseStart_1163170 baseEnd_1163170 := by
    simpa [prefixWord, tailWord_1163170, baseEnd_1163170] using wordTrace_append hprefix tailTrace_1163170
  have hstable : (prefixWord ++ tailWord_1163170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163170).length < 2 ^ (prefixWord ++ tailWord_1163170).sum := by decide
  have hdescent : baseEnd_1163170 < baseStart_1163170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163184 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_1163184 : Nat := 118140960795 + 1163184 * 2 ^ 59
def prefixEnd_1163184 : Nat := 4983230072969 + 3 ^ 40 * 1163184 * 2
def baseEnd_1163184 : Nat := 265454436275325453755831

theorem tailTrace_1163184 : CollatzResearch.WordTrace tailWord_1163184 prefixEnd_1163184 265454436275325453755831 := by
  unfold tailWord_1163184
  simp only [CollatzResearch.WordTrace]
  refine ⟨21212402908995249428248303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28283203878660332570997737 21212402908995249428248303)
  ·
    refine ⟨31818604363492874142372455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21212402908995249428248303 31818604363492874142372455)
    ·
      refine ⟨47727906545239311213558683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31818604363492874142372455 47727906545239311213558683)
      ·
        refine ⟨71591859817858966820338025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47727906545239311213558683 71591859817858966820338025)
        ·
          refine ⟨53693894863394225115253519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71591859817858966820338025 53693894863394225115253519)
          ·
            refine ⟨80540842295091337672880279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53693894863394225115253519 80540842295091337672880279)
            ·
              refine ⟨120811263442637006509320419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80540842295091337672880279 120811263442637006509320419)
              ·
                refine ⟨181216895163955509763980629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120811263442637006509320419 181216895163955509763980629)
                ·
                  refine ⟨265454436275325453755831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 181216895163955509763980629 265454436275325453755831)
                  ·
                    rfl

theorem cell21_1163184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_1163184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163184 prefixEnd_1163184 := by exact prefixLift 1163184
  have htrace : WordTrace (prefixWord ++ tailWord_1163184) baseStart_1163184 baseEnd_1163184 := by
    simpa [prefixWord, tailWord_1163184, baseEnd_1163184] using wordTrace_append hprefix tailTrace_1163184
  have hstable : (prefixWord ++ tailWord_1163184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163184).length < 2 ^ (prefixWord ++ tailWord_1163184).sum := by decide
  have hdescent : baseEnd_1163184 < baseStart_1163184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163215 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 6]
def baseStart_1163215 : Nat := 118140960795 + 1163215 * 2 ^ 59
def prefixEnd_1163215 : Nat := 4983230072969 + 3 ^ 40 * 1163215 * 2
def baseEnd_1163215 : Nat := 265461510897676288739101

theorem tailTrace_1163215 : CollatzResearch.WordTrace tailWord_1163215 prefixEnd_1163215 265461510897676288739101 := by
  unfold tailWord_1163215
  simp only [CollatzResearch.WordTrace]
  refine ⟨42425936480878191150875099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28283957653918794100583399 42425936480878191150875099)
  ·
    refine ⟨63638904721317286726312649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42425936480878191150875099 63638904721317286726312649)
    ·
      refine ⟨47729178540987965044734487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63638904721317286726312649 47729178540987965044734487)
      ·
        refine ⟨71593767811481947567101731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47729178540987965044734487 71593767811481947567101731)
        ·
          refine ⟨107390651717222921350652597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71593767811481947567101731 107390651717222921350652597)
          ·
            refine ⟨10067873598489648876623681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107390651717222921350652597 10067873598489648876623681)
            ·
              refine ⟨7550905198867236657467761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067873598489648876623681 7550905198867236657467761)
              ·
                refine ⟨5663178899150427493100821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7550905198867236657467761 5663178899150427493100821)
                ·
                  refine ⟨265461510897676288739101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5663178899150427493100821 265461510897676288739101)
                  ·
                    rfl

theorem cell21_1163215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_1163215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163215 prefixEnd_1163215 := by exact prefixLift 1163215
  have htrace : WordTrace (prefixWord ++ tailWord_1163215) baseStart_1163215 baseEnd_1163215 := by
    simpa [prefixWord, tailWord_1163215, baseEnd_1163215] using wordTrace_append hprefix tailTrace_1163215
  have hstable : (prefixWord ++ tailWord_1163215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163215).length < 2 ^ (prefixWord ++ tailWord_1163215).sum := by decide
  have hdescent : baseEnd_1163215 < baseStart_1163215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163336 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_1163336 : Nat := 118140960795 + 1163336 * 2 ^ 59
def prefixEnd_1163336 : Nat := 4983230072969 + 3 ^ 40 * 1163336 * 2
def baseEnd_1163336 : Nat := 265489124746206967222187

theorem tailTrace_1163336 : CollatzResearch.WordTrace tailWord_1163336 prefixEnd_1163336 265489124746206967222187 := by
  unfold tailWord_1163336
  simp only [CollatzResearch.WordTrace]
  refine ⟨21215174856719914408014931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28286899808959885877353241 21215174856719914408014931)
  ·
    refine ⟨31822762285079871612022397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21215174856719914408014931 31822762285079871612022397)
    ·
      refine ⟨11933535856904951854508399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31822762285079871612022397 11933535856904951854508399)
      ·
        refine ⟨17900303785357427781762599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11933535856904951854508399 17900303785357427781762599)
        ·
          refine ⟨26850455678036141672643899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17900303785357427781762599 26850455678036141672643899)
          ·
            refine ⟨40275683517054212508965849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26850455678036141672643899 40275683517054212508965849)
            ·
              refine ⟨30206762637790659381724387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40275683517054212508965849 30206762637790659381724387)
              ·
                refine ⟨45310143956685989072586581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30206762637790659381724387 45310143956685989072586581)
                ·
                  refine ⟨265489124746206967222187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45310143956685989072586581 265489124746206967222187)
                  ·
                    rfl

theorem cell21_1163336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_1163336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163336 prefixEnd_1163336 := by exact prefixLift 1163336
  have htrace : WordTrace (prefixWord ++ tailWord_1163336) baseStart_1163336 baseEnd_1163336 := by
    simpa [prefixWord, tailWord_1163336, baseEnd_1163336] using wordTrace_append hprefix tailTrace_1163336
  have hstable : (prefixWord ++ tailWord_1163336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163336).length < 2 ^ (prefixWord ++ tailWord_1163336).sum := by decide
  have hdescent : baseEnd_1163336 < baseStart_1163336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163370 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_1163370 : Nat := 118140960795 + 1163370 * 2 ^ 59
def prefixEnd_1163370 : Nat := 4983230072969 + 3 ^ 40 * 1163370 * 2
def baseEnd_1163370 : Nat := 265496884009430463655451

theorem tailTrace_1163370 : CollatzResearch.WordTrace tailWord_1163370 prefixEnd_1163370 265496884009430463655451 := by
  unfold tailWord_1163370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10607897448829163155691891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28287726530211101748511709 10607897448829163155691891)
  ·
    refine ⟨15911846173243744733537837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10607897448829163155691891 15911846173243744733537837)
    ·
      refine ⟨5966942314966404275076689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15911846173243744733537837 5966942314966404275076689)
      ·
        refine ⟨4475206736224803206307517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5966942314966404275076689 4475206736224803206307517)
        ·
          refine ⟨1678202526084301202365319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4475206736224803206307517 1678202526084301202365319)
          ·
            refine ⟨2517303789126451803547979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678202526084301202365319 2517303789126451803547979)
            ·
              refine ⟨3775955683689677705321969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517303789126451803547979 3775955683689677705321969)
              ·
                refine ⟨2831966762767258278991477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3775955683689677705321969 2831966762767258278991477)
                ·
                  refine ⟨265496884009430463655451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2831966762767258278991477 265496884009430463655451)
                  ·
                    rfl

theorem cell21_1163370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_1163370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163370 prefixEnd_1163370 := by exact prefixLift 1163370
  have htrace : WordTrace (prefixWord ++ tailWord_1163370) baseStart_1163370 baseEnd_1163370 := by
    simpa [prefixWord, tailWord_1163370, baseEnd_1163370] using wordTrace_append hprefix tailTrace_1163370
  have hstable : (prefixWord ++ tailWord_1163370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163370).length < 2 ^ (prefixWord ++ tailWord_1163370).sum := by decide
  have hdescent : baseEnd_1163370 < baseStart_1163370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163418 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_1163418 : Nat := 118140960795 + 1163418 * 2 ^ 59
def prefixEnd_1163418 : Nat := 4983230072969 + 3 ^ 40 * 1163418 * 2
def baseEnd_1163418 : Nat := 265507838263393046855353

theorem tailTrace_1163418 : CollatzResearch.WordTrace tailWord_1163418 prefixEnd_1163418 265507838263393046855353 := by
  unfold tailWord_1163418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608335124785689205128727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28288893666095171213676605 10608335124785689205128727)
  ·
    refine ⟨15912502687178533807693091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608335124785689205128727 15912502687178533807693091)
    ·
      refine ⟨23868754030767800711539637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15912502687178533807693091 23868754030767800711539637)
      ·
        refine ⟨2237695690384481316706841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23868754030767800711539637 2237695690384481316706841)
        ·
          refine ⟨1678271767788360987530131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2237695690384481316706841 1678271767788360987530131)
          ·
            refine ⟨2517407651682541481295197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678271767788360987530131 2517407651682541481295197)
            ·
              refine ⟨944027869380953055485699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2517407651682541481295197 944027869380953055485699)
              ·
                refine ⟨1416041804071429583228549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944027869380953055485699 1416041804071429583228549)
                ·
                  refine ⟨265507838263393046855353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416041804071429583228549 265507838263393046855353)
                  ·
                    rfl

theorem cell21_1163418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_1163418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163418 prefixEnd_1163418 := by exact prefixLift 1163418
  have htrace : WordTrace (prefixWord ++ tailWord_1163418) baseStart_1163418 baseEnd_1163418 := by
    simpa [prefixWord, tailWord_1163418, baseEnd_1163418] using wordTrace_append hprefix tailTrace_1163418
  have hstable : (prefixWord ++ tailWord_1163418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163418).length < 2 ^ (prefixWord ++ tailWord_1163418).sum := by decide
  have hdescent : baseEnd_1163418 < baseStart_1163418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163438 : List Nat := [4, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_1163438 : Nat := 118140960795 + 1163438 * 2 ^ 59
def prefixEnd_1163438 : Nat := 4983230072969 + 3 ^ 40 * 1163438 * 2
def baseEnd_1163438 : Nat := 265512402535877456521979

theorem tailTrace_1163438 : CollatzResearch.WordTrace tailWord_1163438 prefixEnd_1163438 265512402535877456521979 := by
  unfold tailWord_1163438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304258744883787529530371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28289379972713533490828645 5304258744883787529530371)
  ·
    refine ⟨7956388117325681294295557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5304258744883787529530371 7956388117325681294295557)
    ·
      refine ⟨1491822771998565242680417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7956388117325681294295557 1491822771998565242680417)
      ·
        refine ⟨1118867078998923932010313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1491822771998565242680417 1118867078998923932010313)
        ·
          refine ⟨839150309249192949007735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1118867078998923932010313 839150309249192949007735)
          ·
            refine ⟨1258725463873789423511603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839150309249192949007735 1258725463873789423511603)
            ·
              refine ⟨1888088195810684135267405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258725463873789423511603 1888088195810684135267405)
              ·
                refine ⟨708033073429006550725277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1888088195810684135267405 708033073429006550725277)
                ·
                  refine ⟨265512402535877456521979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708033073429006550725277 265512402535877456521979)
                  ·
                    rfl

theorem cell21_1163438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_1163438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163438 prefixEnd_1163438 := by exact prefixLift 1163438
  have htrace : WordTrace (prefixWord ++ tailWord_1163438) baseStart_1163438 baseEnd_1163438 := by
    simpa [prefixWord, tailWord_1163438, baseEnd_1163438] using wordTrace_append hprefix tailTrace_1163438
  have hstable : (prefixWord ++ tailWord_1163438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163438).length < 2 ^ (prefixWord ++ tailWord_1163438).sum := by decide
  have hdescent : baseEnd_1163438 < baseStart_1163438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163460 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1163460 : Nat := 118140960795 + 1163460 * 2 ^ 59
def prefixEnd_1163460 : Nat := 4983230072969 + 3 ^ 40 * 1163460 * 2
def baseEnd_1163460 : Nat := 265517423235610307155267

theorem tailTrace_1163460 : CollatzResearch.WordTrace tailWord_1163460 prefixEnd_1163460 265517423235610307155267 := by
  unfold tailWord_1163460
  simp only [CollatzResearch.WordTrace]
  refine ⟨21217436182495298996771917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28289914909993731995695889 21217436182495298996771917)
  ·
    refine ⟨7956538568435737123789469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21217436182495298996771917 7956538568435737123789469)
    ·
      refine ⟨2983701963163401421421051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7956538568435737123789469 2983701963163401421421051)
      ·
        refine ⟨4475552944745102132131577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2983701963163401421421051 4475552944745102132131577)
        ·
          refine ⟨3356664708558826599098683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4475552944745102132131577 3356664708558826599098683)
          ·
            refine ⟨5034997062838239898648025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356664708558826599098683 5034997062838239898648025)
            ·
              refine ⟨3776247797128679923986019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5034997062838239898648025 3776247797128679923986019)
              ·
                refine ⟨5664371695693019885979029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776247797128679923986019 5664371695693019885979029)
                ·
                  refine ⟨265517423235610307155267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5664371695693019885979029 265517423235610307155267)
                  ·
                    rfl

theorem cell21_1163460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1163460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163460 prefixEnd_1163460 := by exact prefixLift 1163460
  have htrace : WordTrace (prefixWord ++ tailWord_1163460) baseStart_1163460 baseEnd_1163460 := by
    simpa [prefixWord, tailWord_1163460, baseEnd_1163460] using wordTrace_append hprefix tailTrace_1163460
  have hstable : (prefixWord ++ tailWord_1163460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163460).length < 2 ^ (prefixWord ++ tailWord_1163460).sum := by decide
  have hdescent : baseEnd_1163460 < baseStart_1163460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163474 : List Nat := [3, 2, 2, 2, 1, 2, 1, 8]
def baseStart_1163474 : Nat := 118140960795 + 1163474 * 2 ^ 59
def prefixEnd_1163474 : Nat := 4983230072969 + 3 ^ 40 * 1163474 * 2
def baseEnd_1163474 : Nat := 88506872742116464640635

theorem tailTrace_1163474 : CollatzResearch.WordTrace tailWord_1163474 prefixEnd_1163474 88506872742116464640635 := by
  unfold tailWord_1163474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608845746734969596138369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28290255324626585589702317 10608845746734969596138369)
  ·
    refine ⟨7956634310051227197103777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10608845746734969596138369 7956634310051227197103777)
    ·
      refine ⟨5967475732538420397827833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7956634310051227197103777 5967475732538420397827833)
      ·
        refine ⟨4475606799403815298370875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5967475732538420397827833 4475606799403815298370875)
        ·
          refine ⟨6713410199105722947556313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4475606799403815298370875 6713410199105722947556313)
          ·
            refine ⟨5035057649329292210667235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6713410199105722947556313 5035057649329292210667235)
            ·
              refine ⟨7552586473993938316000853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035057649329292210667235 7552586473993938316000853)
              ·
                refine ⟨88506872742116464640635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7552586473993938316000853 88506872742116464640635)
                ·
                  rfl

theorem cell21_1163474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_1163474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163474 prefixEnd_1163474 := by exact prefixLift 1163474
  have htrace : WordTrace (prefixWord ++ tailWord_1163474) baseStart_1163474 baseEnd_1163474 := by
    simpa [prefixWord, tailWord_1163474, baseEnd_1163474] using wordTrace_append hprefix tailTrace_1163474
  have hstable : (prefixWord ++ tailWord_1163474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163474).length < 2 ^ (prefixWord ++ tailWord_1163474).sum := by decide
  have hdescent : baseEnd_1163474 < baseStart_1163474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163477 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 4]
def baseStart_1163477 : Nat := 118140960795 + 1163477 * 2 ^ 59
def prefixEnd_1163477 : Nat := 4983230072969 + 3 ^ 40 * 1163477 * 2
def baseEnd_1163477 : Nat := 265521302867222055371899

theorem tailTrace_1163477 : CollatzResearch.WordTrace tailWord_1163477 prefixEnd_1163477 265521302867222055371899 := by
  unfold tailWord_1163477
  simp only [CollatzResearch.WordTrace]
  refine ⟨42435492405929009896912685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28290328270619339931275123 42435492405929009896912685)
  ·
    refine ⟨15913309652223378711342257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42435492405929009896912685 15913309652223378711342257)
    ·
      refine ⟨11934982239167534033506693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15913309652223378711342257 11934982239167534033506693)
      ·
        refine ⟨2237809169843912631282505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11934982239167534033506693 2237809169843912631282505)
        ·
          refine ⟨1678356877382934473461879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2237809169843912631282505 1678356877382934473461879)
          ·
            refine ⟨2517535316074401710192819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678356877382934473461879 2517535316074401710192819)
            ·
              refine ⟨3776302974111602565289229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517535316074401710192819 3776302974111602565289229)
              ·
                refine ⟨1416113615291850961983461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3776302974111602565289229 1416113615291850961983461)
                ·
                  refine ⟨265521302867222055371899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416113615291850961983461 265521302867222055371899)
                  ·
                    rfl

theorem cell21_1163477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_1163477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163477 prefixEnd_1163477 := by exact prefixLift 1163477
  have htrace : WordTrace (prefixWord ++ tailWord_1163477) baseStart_1163477 baseEnd_1163477 := by
    simpa [prefixWord, tailWord_1163477, baseEnd_1163477] using wordTrace_append hprefix tailTrace_1163477
  have hstable : (prefixWord ++ tailWord_1163477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163477).length < 2 ^ (prefixWord ++ tailWord_1163477).sum := by decide
  have hdescent : baseEnd_1163477 < baseStart_1163477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163488 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_1163488 : Nat := 118140960795 + 1163488 * 2 ^ 59
def prefixEnd_1163488 : Nat := 4983230072969 + 3 ^ 40 * 1163488 * 2
def baseEnd_1163488 : Nat := 265523813217088480688543

theorem tailTrace_1163488 : CollatzResearch.WordTrace tailWord_1163488 prefixEnd_1163488 265523813217088480688543 := by
  unfold tailWord_1163488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21217946804444579387781559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28290595739259439183708745 21217946804444579387781559)
  ·
    refine ⟨31826920206666869081672339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21217946804444579387781559 31826920206666869081672339)
    ·
      refine ⟨47740380310000303622508509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31826920206666869081672339 47740380310000303622508509)
      ·
        refine ⟨17902642616250113858440691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47740380310000303622508509 17902642616250113858440691)
        ·
          refine ⟨26853963924375170787661037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17902642616250113858440691 26853963924375170787661037)
          ·
            refine ⟨10070236471640689045372889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26853963924375170787661037 10070236471640689045372889)
            ·
              refine ⟨7552677353730516784029667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10070236471640689045372889 7552677353730516784029667)
              ·
                refine ⟨11329016030595775176044501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7552677353730516784029667 11329016030595775176044501)
                ·
                  refine ⟨265523813217088480688543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11329016030595775176044501 265523813217088480688543)
                  ·
                    rfl

theorem cell21_1163488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_1163488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163488 prefixEnd_1163488 := by exact prefixLift 1163488
  have htrace : WordTrace (prefixWord ++ tailWord_1163488) baseStart_1163488 baseEnd_1163488 := by
    simpa [prefixWord, tailWord_1163488, baseEnd_1163488] using wordTrace_append hprefix tailTrace_1163488
  have hstable : (prefixWord ++ tailWord_1163488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163488).length < 2 ^ (prefixWord ++ tailWord_1163488).sum := by decide
  have hdescent : baseEnd_1163488 < baseStart_1163488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163570 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_1163570 : Nat := 118140960795 + 1163570 * 2 ^ 59
def prefixEnd_1163570 : Nat := 4983230072969 + 3 ^ 40 * 1163570 * 2
def baseEnd_1163570 : Nat := 265542526734274560321709

theorem tailTrace_1163570 : CollatzResearch.WordTrace tailWord_1163570 prefixEnd_1163570 265542526734274560321709 := by
  unfold tailWord_1163570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10609721098648021695012041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28292589596394724520032109 10609721098648021695012041)
  ·
    refine ⟨7957290823986016271259031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10609721098648021695012041 7957290823986016271259031)
    ·
      refine ⟨11935936235979024406888547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7957290823986016271259031 11935936235979024406888547)
      ·
        refine ⟨17903904353968536610332821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935936235979024406888547 17903904353968536610332821)
        ·
          refine ⟨839245516592275153609351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17903904353968536610332821 839245516592275153609351)
          ·
            refine ⟨1258868274888412730414027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839245516592275153609351 1258868274888412730414027)
            ·
              refine ⟨1888302412332619095621041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258868274888412730414027 1888302412332619095621041)
              ·
                refine ⟨1416226809249464321715781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1888302412332619095621041 1416226809249464321715781)
                ·
                  refine ⟨265542526734274560321709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416226809249464321715781 265542526734274560321709)
                  ·
                    rfl

theorem cell21_1163570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_1163570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163570 prefixEnd_1163570 := by exact prefixLift 1163570
  have htrace : WordTrace (prefixWord ++ tailWord_1163570) baseStart_1163570 baseEnd_1163570 := by
    simpa [prefixWord, tailWord_1163570, baseEnd_1163570] using wordTrace_append hprefix tailTrace_1163570
  have hstable : (prefixWord ++ tailWord_1163570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163570).length < 2 ^ (prefixWord ++ tailWord_1163570).sum := by decide
  have hdescent : baseEnd_1163570 < baseStart_1163570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163626 : List Nat := [3, 1, 3, 3, 1, 1, 9]
def baseStart_1163626 : Nat := 118140960795 + 1163626 * 2 ^ 59
def prefixEnd_1163626 : Nat := 4983230072969 + 3 ^ 40 * 1163626 * 2
def baseEnd_1163626 : Nat := 29506145188581211932029

theorem tailTrace_1163626 : CollatzResearch.WordTrace tailWord_1163626 prefixEnd_1163626 29506145188581211932029 := by
  unfold tailWord_1163626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10610231720597302086021683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28293951254926138896057821 10610231720597302086021683)
  ·
    refine ⟨15915347580895953129032525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10610231720597302086021683 15915347580895953129032525)
    ·
      refine ⟨5968255342835982423387197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15915347580895953129032525 5968255342835982423387197)
      ·
        refine ⟨2238095753563493408770199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5968255342835982423387197 2238095753563493408770199)
        ·
          refine ⟨3357143630345240113155299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238095753563493408770199 3357143630345240113155299)
          ·
            refine ⟨5035715445517860169732949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357143630345240113155299 5035715445517860169732949)
            ·
              refine ⟨29506145188581211932029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5035715445517860169732949 29506145188581211932029)
              ·
                rfl

theorem cell21_1163626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 9].length) (baseStart_1163626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163626 prefixEnd_1163626 := by exact prefixLift 1163626
  have htrace : WordTrace (prefixWord ++ tailWord_1163626) baseStart_1163626 baseEnd_1163626 := by
    simpa [prefixWord, tailWord_1163626, baseEnd_1163626] using wordTrace_append hprefix tailTrace_1163626
  have hstable : (prefixWord ++ tailWord_1163626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163626).length < 2 ^ (prefixWord ++ tailWord_1163626).sum := by decide
  have hdescent : baseEnd_1163626 < baseStart_1163626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163761 : List Nat := [1, 2, 2, 2, 3, 1, 2, 8]
def baseStart_1163761 : Nat := 118140960795 + 1163761 * 2 ^ 59
def prefixEnd_1163761 : Nat := 4983230072969 + 3 ^ 40 * 1163761 * 2
def baseEnd_1163761 : Nat := 88528705178833557545995

theorem tailTrace_1163761 : CollatzResearch.WordTrace tailWord_1163761 prefixEnd_1163761 88528705178833557545995 := by
  unfold tailWord_1163761
  simp only [CollatzResearch.WordTrace]
  refine ⟨42445850736900126400251137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28297233824600084266834091 42445850736900126400251137)
  ·
    refine ⟨31834388052675094800188353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42445850736900126400251137 31834388052675094800188353)
    ·
      refine ⟨23875791039506321100141265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31834388052675094800188353 23875791039506321100141265)
      ·
        refine ⟨17906843279629740825105949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23875791039506321100141265 17906843279629740825105949)
        ·
          refine ⟨6715066229861152809414731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17906843279629740825105949 6715066229861152809414731)
          ·
            refine ⟨10072599344791729214122097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6715066229861152809414731 10072599344791729214122097)
            ·
              refine ⟨7554449508593796910591573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10072599344791729214122097 7554449508593796910591573)
              ·
                refine ⟨88528705178833557545995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7554449508593796910591573 88528705178833557545995)
                ·
                  rfl

theorem cell21_1163761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 8].length) (baseStart_1163761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163761 prefixEnd_1163761 := by exact prefixLift 1163761
  have htrace : WordTrace (prefixWord ++ tailWord_1163761) baseStart_1163761 baseEnd_1163761 := by
    simpa [prefixWord, tailWord_1163761, baseEnd_1163761] using wordTrace_append hprefix tailTrace_1163761
  have hstable : (prefixWord ++ tailWord_1163761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163761).length < 2 ^ (prefixWord ++ tailWord_1163761).sum := by decide
  have hdescent : baseEnd_1163761 < baseStart_1163761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163815 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 4]
def baseStart_1163815 : Nat := 118140960795 + 1163815 * 2 ^ 59
def prefixEnd_1163815 : Nat := 4983230072969 + 3 ^ 40 * 1163815 * 2
def baseEnd_1163815 : Nat := 265598439072208578737875

theorem tailTrace_1163815 : CollatzResearch.WordTrace tailWord_1163815 prefixEnd_1163815 265598439072208578737875 := by
  unfold tailWord_1163815
  simp only [CollatzResearch.WordTrace]
  refine ⟨42447820278704493622716899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28298546852469662415144599 42447820278704493622716899)
  ·
    refine ⟨63671730418056740434075349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42447820278704493622716899 63671730418056740434075349)
    ·
      refine ⟨1492306181673204853923641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 63671730418056740434075349 1492306181673204853923641)
      ·
        refine ⟨1119229636254903640442731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1492306181673204853923641 1119229636254903640442731)
        ·
          refine ⟨1678844454382355460664097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119229636254903640442731 1678844454382355460664097)
          ·
            refine ⟨1259133340786766595498073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678844454382355460664097 1259133340786766595498073)
            ·
              refine ⟨944350005590074946623555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259133340786766595498073 944350005590074946623555)
              ·
                refine ⟨1416525008385112419935333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944350005590074946623555 1416525008385112419935333)
                ·
                  refine ⟨265598439072208578737875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416525008385112419935333 265598439072208578737875)
                  ·
                    rfl

theorem cell21_1163815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 4].length) (baseStart_1163815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163815 prefixEnd_1163815 := by exact prefixLift 1163815
  have htrace : WordTrace (prefixWord ++ tailWord_1163815) baseStart_1163815 baseEnd_1163815 := by
    simpa [prefixWord, tailWord_1163815, baseEnd_1163815] using wordTrace_append hprefix tailTrace_1163815
  have hstable : (prefixWord ++ tailWord_1163815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163815).length < 2 ^ (prefixWord ++ tailWord_1163815).sum := by decide
  have hdescent : baseEnd_1163815 < baseStart_1163815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163885 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1163885 : Nat := 118140960795 + 1163885 * 2 ^ 59
def prefixEnd_1163885 : Nat := 4983230072969 + 3 ^ 40 * 1163885 * 2
def baseEnd_1163885 : Nat := 265614414025904012571065

theorem tailTrace_1163885 : CollatzResearch.WordTrace tailWord_1163885 prefixEnd_1163885 265614414025904012571065 := by
  unfold tailWord_1163885
  simp only [CollatzResearch.WordTrace]
  refine ⟨42450373388450895577765109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28300248925633930385176739 42450373388450895577765109)
  ·
    refine ⟨3979722505167271460415479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42450373388450895577765109 3979722505167271460415479)
    ·
      refine ⟨5969583757750907190623219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979722505167271460415479 5969583757750907190623219)
      ·
        refine ⟨8954375636626360785934829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5969583757750907190623219 8954375636626360785934829)
        ·
          refine ⟨3357890863734885294725561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8954375636626360785934829 3357890863734885294725561)
          ·
            refine ⟨2518418147801163971044171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3357890863734885294725561 2518418147801163971044171)
            ·
              refine ⟨3777627221701745956566257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518418147801163971044171 3777627221701745956566257)
              ·
                refine ⟨2833220416276309467424693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3777627221701745956566257 2833220416276309467424693)
                ·
                  refine ⟨265614414025904012571065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2833220416276309467424693 265614414025904012571065)
                  ·
                    rfl

theorem cell21_1163885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1163885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163885 prefixEnd_1163885 := by exact prefixLift 1163885
  have htrace : WordTrace (prefixWord ++ tailWord_1163885) baseStart_1163885 baseEnd_1163885 := by
    simpa [prefixWord, tailWord_1163885, baseEnd_1163885] using wordTrace_append hprefix tailTrace_1163885
  have hstable : (prefixWord ++ tailWord_1163885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163885).length < 2 ^ (prefixWord ++ tailWord_1163885).sum := by decide
  have hdescent : baseEnd_1163885 < baseStart_1163885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163992 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_1163992 : Nat := 118140960795 + 1163992 * 2 ^ 59
def prefixEnd_1163992 : Nat := 4983230072969 + 3 ^ 40 * 1163992 * 2
def baseEnd_1163992 : Nat := 265638832883695604287513

theorem tailTrace_1163992 : CollatzResearch.WordTrace tailWord_1163992 prefixEnd_1163992 265638832883695604287513 := by
  unfold tailWord_1163992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227137999531626425955115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28302850666042168567940153 21227137999531626425955115)
  ·
    refine ⟨31840706999297439638932673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21227137999531626425955115 31840706999297439638932673)
    ·
      refine ⟨23880530249473079729199505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31840706999297439638932673 23880530249473079729199505)
      ·
        refine ⟨17910397687104809796899629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23880530249473079729199505 17910397687104809796899629)
        ·
          refine ⟨6716399132664303673837361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17910397687104809796899629 6716399132664303673837361)
          ·
            refine ⟨5037299349498227755378021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6716399132664303673837361 5037299349498227755378021)
            ·
              refine ⟨944493628030917704133379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5037299349498227755378021 944493628030917704133379)
              ·
                refine ⟨1416740442046376556200069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944493628030917704133379 1416740442046376556200069)
                ·
                  refine ⟨265638832883695604287513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1416740442046376556200069 265638832883695604287513)
                  ·
                    rfl

theorem cell21_1163992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_1163992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1163992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1163992 prefixEnd_1163992 := by exact prefixLift 1163992
  have htrace : WordTrace (prefixWord ++ tailWord_1163992) baseStart_1163992 baseEnd_1163992 := by
    simpa [prefixWord, tailWord_1163992, baseEnd_1163992] using wordTrace_append hprefix tailTrace_1163992
  have hstable : (prefixWord ++ tailWord_1163992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163992).length < 2 ^ (prefixWord ++ tailWord_1163992).sum := by decide
  have hdescent : baseEnd_1163992 < baseStart_1163992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164116 : List Nat := [2, 4, 1, 1, 5, 1, 2, 5]
def baseStart_1164116 : Nat := 118140960795 + 1164116 * 2 ^ 59
def prefixEnd_1164116 : Nat := 4983230072969 + 3 ^ 40 * 1164116 * 2
def baseEnd_1164116 : Nat := 88555710457699648073531

theorem tailTrace_1164116 : CollatzResearch.WordTrace tailWord_1164116 prefixEnd_1164116 88555710457699648073531 := by
  unfold tailWord_1164116
  simp only [CollatzResearch.WordTrace]
  refine ⟨21229399325307011014712101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28305865767076014686282801 21229399325307011014712101)
  ·
    refine ⟨3980512373495064565258519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21229399325307011014712101 3980512373495064565258519)
    ·
      refine ⟨5970768560242596847887779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980512373495064565258519 5970768560242596847887779)
      ·
        refine ⟨8956152840363895271831669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970768560242596847887779 8956152840363895271831669)
        ·
          refine ⟨839639328784115181734219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8956152840363895271831669 839639328784115181734219)
          ·
            refine ⟨1259458993176172772601329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839639328784115181734219 1259458993176172772601329)
            ·
              refine ⟨944594244882129579450997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259458993176172772601329 944594244882129579450997)
              ·
                refine ⟨88555710457699648073531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 944594244882129579450997 88555710457699648073531)
                ·
                  rfl

theorem cell21_1164116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_1164116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164116 prefixEnd_1164116 := by exact prefixLift 1164116
  have htrace : WordTrace (prefixWord ++ tailWord_1164116) baseStart_1164116 baseEnd_1164116 := by
    simpa [prefixWord, tailWord_1164116, baseEnd_1164116] using wordTrace_append hprefix tailTrace_1164116
  have hstable : (prefixWord ++ tailWord_1164116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164116).length < 2 ^ (prefixWord ++ tailWord_1164116).sum := by decide
  have hdescent : baseEnd_1164116 < baseStart_1164116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164189 : List Nat := [1, 4, 2, 1, 2, 1, 2, 5, 3]
def baseStart_1164189 : Nat := 118140960795 + 1164189 * 2 ^ 59
def prefixEnd_1164189 : Nat := 4983230072969 + 3 ^ 40 * 1164189 * 2
def baseEnd_1164189 : Nat := 265683790967667039503777

theorem tailTrace_1164189 : CollatzResearch.WordTrace tailWord_1164189 prefixEnd_1164189 265683790967667039503777 := by
  unfold tailWord_1164189
  simp only [CollatzResearch.WordTrace]
  refine ⟨42461461179349555496831621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28307640786233036997887747 42461461179349555496831621)
  ·
    refine ⟨7961523971128041655655929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42461461179349555496831621 7961523971128041655655929)
    ·
      refine ⟨5971142978346031241741947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7961523971128041655655929 5971142978346031241741947)
      ·
        refine ⟨8956714467519046862612921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5971142978346031241741947 8956714467519046862612921)
        ·
          refine ⟨6717535850639285146959691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8956714467519046862612921 6717535850639285146959691)
          ·
            refine ⟨10076303775958927720439537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6717535850639285146959691 10076303775958927720439537)
            ·
              refine ⟨7557227831969195790329653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10076303775958927720439537 7557227831969195790329653)
              ·
                refine ⟨708490109247112105343405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7557227831969195790329653 708490109247112105343405)
                ·
                  refine ⟨265683790967667039503777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708490109247112105343405 265683790967667039503777)
                  ·
                    rfl

theorem cell21_1164189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_1164189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164189 prefixEnd_1164189 := by exact prefixLift 1164189
  have htrace : WordTrace (prefixWord ++ tailWord_1164189) baseStart_1164189 baseEnd_1164189 := by
    simpa [prefixWord, tailWord_1164189, baseEnd_1164189] using wordTrace_append hprefix tailTrace_1164189
  have hstable : (prefixWord ++ tailWord_1164189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164189).length < 2 ^ (prefixWord ++ tailWord_1164189).sum := by decide
  have hdescent : baseEnd_1164189 < baseStart_1164189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164217 : List Nat := [1, 2, 1, 4, 2, 2, 3, 6]
def baseStart_1164217 : Nat := 118140960795 + 1164217 * 2 ^ 59
def prefixEnd_1164217 : Nat := 4983230072969 + 3 ^ 40 * 1164217 * 2
def baseEnd_1164217 : Nat := 88563393649715071012351

theorem tailTrace_1164217 : CollatzResearch.WordTrace tailWord_1164217 prefixEnd_1164217 88563393649715071012351 := by
  unfold tailWord_1164217
  simp only [CollatzResearch.WordTrace]
  refine ⟨42462482423248116278850905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28308321615498744185900603 42462482423248116278850905)
  ·
    refine ⟨31846861817436087209138179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42462482423248116278850905 31846861817436087209138179)
    ·
      refine ⟨47770292726154130813707269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31846861817436087209138179 47770292726154130813707269)
      ·
        refine ⟨8956929886153899527570113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47770292726154130813707269 8956929886153899527570113)
        ·
          refine ⟨6717697414615424645677585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8956929886153899527570113 6717697414615424645677585)
          ·
            refine ⟨5038273060961568484258189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6717697414615424645677585 5038273060961568484258189)
            ·
              refine ⟨1889352397860588181596821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5038273060961568484258189 1889352397860588181596821)
              ·
                refine ⟨88563393649715071012351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1889352397860588181596821 88563393649715071012351)
                ·
                  rfl

theorem cell21_1164217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 6].length) (baseStart_1164217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164217 prefixEnd_1164217 := by exact prefixLift 1164217
  have htrace : WordTrace (prefixWord ++ tailWord_1164217) baseStart_1164217 baseEnd_1164217 := by
    simpa [prefixWord, tailWord_1164217, baseEnd_1164217] using wordTrace_append hprefix tailTrace_1164217
  have hstable : (prefixWord ++ tailWord_1164217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164217).length < 2 ^ (prefixWord ++ tailWord_1164217).sum := by decide
  have hdescent : baseEnd_1164217 < baseStart_1164217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164231 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 7]
def baseStart_1164231 : Nat := 118140960795 + 1164231 * 2 ^ 59
def prefixEnd_1164231 : Nat := 4983230072969 + 3 ^ 40 * 1164231 * 2
def baseEnd_1164231 : Nat := 265693375939884299803691

theorem tailTrace_1164231 : CollatzResearch.WordTrace tailWord_1164231 prefixEnd_1164231 265693375939884299803691 := by
  unfold tailWord_1164231
  simp only [CollatzResearch.WordTrace]
  refine ⟨42462993045197396669860547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28308662030131597779907031 42462993045197396669860547)
  ·
    refine ⟨63694489567796095004790821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42462993045197396669860547 63694489567796095004790821)
    ·
      refine ⟨11942716793961767813398279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63694489567796095004790821 11942716793961767813398279)
      ·
        refine ⟨17914075190942651720097419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11942716793961767813398279 17914075190942651720097419)
        ·
          refine ⟨26871112786413977580146129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17914075190942651720097419 26871112786413977580146129)
          ·
            refine ⟨20153334589810483185109597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26871112786413977580146129 20153334589810483185109597)
            ·
              refine ⟨7557500471178931194416099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20153334589810483185109597 7557500471178931194416099)
              ·
                refine ⟨11336250706768396791624149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557500471178931194416099 11336250706768396791624149)
                ·
                  refine ⟨265693375939884299803691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11336250706768396791624149 265693375939884299803691)
                  ·
                    rfl

theorem cell21_1164231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_1164231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164231 prefixEnd_1164231 := by exact prefixLift 1164231
  have htrace : WordTrace (prefixWord ++ tailWord_1164231) baseStart_1164231 baseEnd_1164231 := by
    simpa [prefixWord, tailWord_1164231, baseEnd_1164231] using wordTrace_append hprefix tailTrace_1164231
  have hstable : (prefixWord ++ tailWord_1164231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164231).length < 2 ^ (prefixWord ++ tailWord_1164231).sum := by decide
  have hdescent : baseEnd_1164231 < baseStart_1164231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164330 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_1164330 : Nat := 118140960795 + 1164330 * 2 ^ 59
def prefixEnd_1164330 : Nat := 4983230072969 + 3 ^ 40 * 1164330 * 2
def baseEnd_1164330 : Nat := 265715969088682127653489

theorem tailTrace_1164330 : CollatzResearch.WordTrace tailWord_1164330 prefixEnd_1164330 265715969088682127653489 := by
  unfold tailWord_1164330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616650967959684144428611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28311069247892491051809629 10616650967959684144428611)
  ·
    refine ⟨15924976451939526216642917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10616650967959684144428611 15924976451939526216642917)
    ·
      refine ⟨2985933084738661165620547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15924976451939526216642917 2985933084738661165620547)
      ·
        refine ⟨4478899627107991748430821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985933084738661165620547 4478899627107991748430821)
        ·
          refine ⟨839793680082748452830779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4478899627107991748430821 839793680082748452830779)
          ·
            refine ⟨1259690520124122679246169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839793680082748452830779 1259690520124122679246169)
            ·
              refine ⟨944767890093092009434627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259690520124122679246169 944767890093092009434627)
              ·
                refine ⟨1417151835139638014151941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944767890093092009434627 1417151835139638014151941)
                ·
                  refine ⟨265715969088682127653489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417151835139638014151941 265715969088682127653489)
                  ·
                    rfl

theorem cell21_1164330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_1164330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164330 prefixEnd_1164330 := by exact prefixLift 1164330
  have htrace : WordTrace (prefixWord ++ tailWord_1164330) baseStart_1164330 baseEnd_1164330 := by
    simpa [prefixWord, tailWord_1164330, baseEnd_1164330] using wordTrace_append hprefix tailTrace_1164330
  have hstable : (prefixWord ++ tailWord_1164330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164330).length < 2 ^ (prefixWord ++ tailWord_1164330).sum := by decide
  have hdescent : baseEnd_1164330 < baseStart_1164330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164352 : List Nat := [2, 1, 1, 2, 2, 3, 1, 9]
def baseStart_1164352 : Nat := 118140960795 + 1164352 * 2 ^ 59
def prefixEnd_1164352 : Nat := 4983230072969 + 3 ^ 40 * 1164352 * 2
def baseEnd_1164352 : Nat := 88573663262804992762259

theorem tailTrace_1164352 : CollatzResearch.WordTrace tailWord_1164352 prefixEnd_1164352 88573663262804992762259 := by
  unfold tailWord_1164352
  simp only [CollatzResearch.WordTrace]
  refine ⟨21233703138879517167507655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28311604185172689556676873 21233703138879517167507655)
  ·
    refine ⟨31850554708319275751261483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21233703138879517167507655 31850554708319275751261483)
    ·
      refine ⟨47775832062478913626892225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31850554708319275751261483 47775832062478913626892225)
      ·
        refine ⟨35831874046859185220169169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47775832062478913626892225 35831874046859185220169169)
        ·
          refine ⟨26873905535144388915126877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35831874046859185220169169 26873905535144388915126877)
          ·
            refine ⟨10077714575679145843172579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26873905535144388915126877 10077714575679145843172579)
            ·
              refine ⟨15116571863518718764758869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10077714575679145843172579 15116571863518718764758869)
              ·
                refine ⟨88573663262804992762259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15116571863518718764758869 88573663262804992762259)
                ·
                  rfl

theorem cell21_1164352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_1164352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164352 prefixEnd_1164352 := by exact prefixLift 1164352
  have htrace : WordTrace (prefixWord ++ tailWord_1164352) baseStart_1164352 baseEnd_1164352 := by
    simpa [prefixWord, tailWord_1164352, baseEnd_1164352] using wordTrace_append hprefix tailTrace_1164352
  have hstable : (prefixWord ++ tailWord_1164352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164352).length < 2 ^ (prefixWord ++ tailWord_1164352).sum := by decide
  have hdescent : baseEnd_1164352 < baseStart_1164352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164383 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 5]
def baseStart_1164383 : Nat := 118140960795 + 1164383 * 2 ^ 59
def prefixEnd_1164383 : Nat := 4983230072969 + 3 ^ 40 * 1164383 * 2
def baseEnd_1164383 : Nat := 265728064410765813270047

theorem tailTrace_1164383 : CollatzResearch.WordTrace tailWord_1164383 prefixEnd_1164383 265728064410765813270047 := by
  unfold tailWord_1164383
  simp only [CollatzResearch.WordTrace]
  refine ⟨42468536940646726629393803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28312357960431151086262535 42468536940646726629393803)
  ·
    refine ⟨63702805410970089944090705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42468536940646726629393803 63702805410970089944090705)
    ·
      refine ⟨47777104058227567458068029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63702805410970089944090705 47777104058227567458068029)
      ·
        refine ⟨17916414021835337796775511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47777104058227567458068029 17916414021835337796775511)
        ·
          refine ⟨26874621032753006695163267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17916414021835337796775511 26874621032753006695163267)
          ·
            refine ⟨40311931549129510042744901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26874621032753006695163267 40311931549129510042744901)
            ·
              refine ⟨7558487165461783133014669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40311931549129510042744901 7558487165461783133014669)
              ·
                refine ⟨2834432687048168674880501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7558487165461783133014669 2834432687048168674880501)
                ·
                  refine ⟨265728064410765813270047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2834432687048168674880501 265728064410765813270047)
                  ·
                    rfl

theorem cell21_1164383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_1164383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164383 prefixEnd_1164383 := by exact prefixLift 1164383
  have htrace : WordTrace (prefixWord ++ tailWord_1164383) baseStart_1164383 baseEnd_1164383 := by
    simpa [prefixWord, tailWord_1164383, baseEnd_1164383] using wordTrace_append hprefix tailTrace_1164383
  have hstable : (prefixWord ++ tailWord_1164383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164383).length < 2 ^ (prefixWord ++ tailWord_1164383).sum := by decide
  have hdescent : baseEnd_1164383 < baseStart_1164383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164386 : List Nat := [3, 3, 2, 2, 1, 1, 3, 6]
def baseStart_1164386 : Nat := 118140960795 + 1164386 * 2 ^ 59
def prefixEnd_1164386 : Nat := 4983230072969 + 3 ^ 40 * 1164386 * 2
def baseEnd_1164386 : Nat := 88576249683879491573347

theorem tailTrace_1164386 : CollatzResearch.WordTrace tailWord_1164386 prefixEnd_1164386 88576249683879491573347 := by
  unfold tailWord_1164386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10617161589908964535438253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28312430906423905427835341 10617161589908964535438253)
  ·
    refine ⟨3981435596215861700789345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10617161589908964535438253 3981435596215861700789345)
    ·
      refine ⟨2986076697161896275592009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3981435596215861700789345 2986076697161896275592009)
      ·
        refine ⟨2239557522871422206694007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2986076697161896275592009 2239557522871422206694007)
        ·
          refine ⟨3359336284307133310041011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239557522871422206694007 3359336284307133310041011)
          ·
            refine ⟨5039004426460699965061517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359336284307133310041011 5039004426460699965061517)
            ·
              refine ⟨1889626659922762486898069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5039004426460699965061517 1889626659922762486898069)
              ·
                refine ⟨88576249683879491573347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1889626659922762486898069 88576249683879491573347)
                ·
                  rfl

theorem cell21_1164386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_1164386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164386 prefixEnd_1164386 := by exact prefixLift 1164386
  have htrace : WordTrace (prefixWord ++ tailWord_1164386) baseStart_1164386 baseEnd_1164386 := by
    simpa [prefixWord, tailWord_1164386, baseEnd_1164386] using wordTrace_append hprefix tailTrace_1164386
  have hstable : (prefixWord ++ tailWord_1164386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164386).length < 2 ^ (prefixWord ++ tailWord_1164386).sum := by decide
  have hdescent : baseEnd_1164386 < baseStart_1164386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164417 : List Nat := [1, 2, 4, 2, 2, 1, 1, 5, 3]
def baseStart_1164417 : Nat := 118140960795 + 1164417 * 2 ^ 59
def prefixEnd_1164417 : Nat := 4983230072969 + 3 ^ 40 * 1164417 * 2
def baseEnd_1164417 : Nat := 265735823673989309703311

theorem tailTrace_1164417 : CollatzResearch.WordTrace tailWord_1164417 prefixEnd_1164417 265735823673989309703311 := by
  unfold tailWord_1164417
  simp only [CollatzResearch.WordTrace]
  refine ⟨42469777022523550436131505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28313184681682366957421003 42469777022523550436131505)
  ·
    refine ⟨31852332766892662827098629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42469777022523550436131505 31852332766892662827098629)
    ·
      refine ⟨5972312393792374280080993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31852332766892662827098629 5972312393792374280080993)
      ·
        refine ⟨4479234295344280710060745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5972312393792374280080993 4479234295344280710060745)
        ·
          refine ⟨3359425721508210532545559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4479234295344280710060745 3359425721508210532545559)
          ·
            refine ⟨5039138582262315798818339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359425721508210532545559 5039138582262315798818339)
            ·
              refine ⟨7558707873393473698227509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039138582262315798818339 7558707873393473698227509)
              ·
                refine ⟨708628863130638159208829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7558707873393473698227509 708628863130638159208829)
                ·
                  refine ⟨265735823673989309703311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708628863130638159208829 265735823673989309703311)
                  ·
                    rfl

theorem cell21_1164417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_1164417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164417 prefixEnd_1164417 := by exact prefixLift 1164417
  have htrace : WordTrace (prefixWord ++ tailWord_1164417) baseStart_1164417 baseEnd_1164417 := by
    simpa [prefixWord, tailWord_1164417, baseEnd_1164417] using wordTrace_append hprefix tailTrace_1164417
  have hstable : (prefixWord ++ tailWord_1164417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164417).length < 2 ^ (prefixWord ++ tailWord_1164417).sum := by decide
  have hdescent : baseEnd_1164417 < baseStart_1164417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164490 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_1164490 : Nat := 118140960795 + 1164490 * 2 ^ 59
def prefixEnd_1164490 : Nat := 4983230072969 + 3 ^ 40 * 1164490 * 2
def baseEnd_1164490 : Nat := 265752483268557404986495

theorem tailTrace_1164490 : CollatzResearch.WordTrace tailWord_1164490 prefixEnd_1164490 265752483268557404986495 := by
  unfold tailWord_1164490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10618109887814770975884731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28314959700839389269025949 10618109887814770975884731)
  ·
    refine ⟨15927164831722156463827097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10618109887814770975884731 15927164831722156463827097)
    ·
      refine ⟨11945373623791617347870323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15927164831722156463827097 11945373623791617347870323)
      ·
        refine ⟨17918060435687426021805485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11945373623791617347870323 17918060435687426021805485)
        ·
          refine ⟨6719272663382784758177057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17918060435687426021805485 6719272663382784758177057)
          ·
            refine ⟨5039454497537088568632793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6719272663382784758177057 5039454497537088568632793)
            ·
              refine ⟨3779590873152816426474595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5039454497537088568632793 3779590873152816426474595)
              ·
                refine ⟨5669386309729224639711893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779590873152816426474595 5669386309729224639711893)
                ·
                  refine ⟨265752483268557404986495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5669386309729224639711893 265752483268557404986495)
                  ·
                    rfl

theorem cell21_1164490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_1164490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164490 prefixEnd_1164490 := by exact prefixLift 1164490
  have htrace : WordTrace (prefixWord ++ tailWord_1164490) baseStart_1164490 baseEnd_1164490 := by
    simpa [prefixWord, tailWord_1164490, baseEnd_1164490] using wordTrace_append hprefix tailTrace_1164490
  have hstable : (prefixWord ++ tailWord_1164490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164490).length < 2 ^ (prefixWord ++ tailWord_1164490).sum := by decide
  have hdescent : baseEnd_1164490 < baseStart_1164490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164586 : List Nat := [3, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_1164586 : Nat := 118140960795 + 1164586 * 2 ^ 59
def prefixEnd_1164586 : Nat := 4983230072969 + 3 ^ 40 * 1164586 * 2
def baseEnd_1164586 : Nat := 265774391776482571386299

theorem tailTrace_1164586 : CollatzResearch.WordTrace tailWord_1164586 prefixEnd_1164586 265774391776482571386299 := by
  unfold tailWord_1164586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10618985239727823074758403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28317293972607528199355741 10618985239727823074758403)
  ·
    refine ⟨15928477859591734612137605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10618985239727823074758403 15928477859591734612137605)
    ·
      refine ⟨2986589598673450239775801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15928477859591734612137605 2986589598673450239775801)
      ·
        refine ⟨2239942199005087679831851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2986589598673450239775801 2239942199005087679831851)
        ·
          refine ⟨3359913298507631519747777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239942199005087679831851 3359913298507631519747777)
          ·
            refine ⟨2519934973880723639810833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3359913298507631519747777 2519934973880723639810833)
            ·
              refine ⟨1889951230410542729858125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2519934973880723639810833 1889951230410542729858125)
              ·
                refine ⟨708731711403953523696797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1889951230410542729858125 708731711403953523696797)
                ·
                  refine ⟨265774391776482571386299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708731711403953523696797 265774391776482571386299)
                  ·
                    rfl

theorem cell21_1164586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_1164586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164586 prefixEnd_1164586 := by exact prefixLift 1164586
  have htrace : WordTrace (prefixWord ++ tailWord_1164586) baseStart_1164586 baseEnd_1164586 := by
    simpa [prefixWord, tailWord_1164586, baseEnd_1164586] using wordTrace_append hprefix tailTrace_1164586
  have hstable : (prefixWord ++ tailWord_1164586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164586).length < 2 ^ (prefixWord ++ tailWord_1164586).sum := by decide
  have hdescent : baseEnd_1164586 < baseStart_1164586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164637 : List Nat := [1, 4, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1164637 : Nat := 118140960795 + 1164637 * 2 ^ 59
def prefixEnd_1164637 : Nat := 4983230072969 + 3 ^ 40 * 1164637 * 2
def baseEnd_1164637 : Nat := 265786030671317816036195

theorem tailTrace_1164637 : CollatzResearch.WordTrace tailWord_1164637 prefixEnd_1164637 265786030671317816036195 := by
  unfold tailWord_1164637
  simp only [CollatzResearch.WordTrace]
  refine ⟨42477801081726528009140165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28318534054484352006093443 42477801081726528009140165)
  ·
    refine ⟨7964587702823724001713781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42477801081726528009140165 7964587702823724001713781)
    ·
      refine ⟨746680097139724125160667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7964587702823724001713781 746680097139724125160667)
      ·
        refine ⟨1120020145709586187741001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746680097139724125160667 1120020145709586187741001)
        ·
          refine ⟨840015109282189640805751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1120020145709586187741001 840015109282189640805751)
          ·
            refine ⟨1260022663923284461208627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840015109282189640805751 1260022663923284461208627)
            ·
              refine ⟨1890033995884926691812941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260022663923284461208627 1890033995884926691812941)
              ·
                refine ⟨708762748456847509429853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1890033995884926691812941 708762748456847509429853)
                ·
                  refine ⟨265786030671317816036195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708762748456847509429853 265786030671317816036195)
                  ·
                    rfl

theorem cell21_1164637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1164637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164637 prefixEnd_1164637 := by exact prefixLift 1164637
  have htrace : WordTrace (prefixWord ++ tailWord_1164637) baseStart_1164637 baseEnd_1164637 := by
    simpa [prefixWord, tailWord_1164637, baseEnd_1164637] using wordTrace_append hprefix tailTrace_1164637
  have hstable : (prefixWord ++ tailWord_1164637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164637).length < 2 ^ (prefixWord ++ tailWord_1164637).sum := by decide
  have hdescent : baseEnd_1164637 < baseStart_1164637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164642 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1164642 : Nat := 118140960795 + 1164642 * 2 ^ 59
def prefixEnd_1164642 : Nat := 4983230072969 + 3 ^ 40 * 1164642 * 2
def baseEnd_1164642 : Nat := 265787171739438918452851

theorem tailTrace_1164642 : CollatzResearch.WordTrace tailWord_1164642 prefixEnd_1164642 265787171739438918452851 := by
  unfold tailWord_1164642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10619495861677103465768045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28318655631138942575381453 10619495861677103465768045)
  ·
    refine ⟨3982310948128913799663017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10619495861677103465768045 3982310948128913799663017)
    ·
      refine ⟨2986733211096685349747263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3982310948128913799663017 2986733211096685349747263)
      ·
        refine ⟨4480099816645028024620895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2986733211096685349747263 4480099816645028024620895)
        ·
          refine ⟨6720149724967542036931343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480099816645028024620895 6720149724967542036931343)
          ·
            refine ⟨10080224587451313055397015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6720149724967542036931343 10080224587451313055397015)
            ·
              refine ⟨15120336881176969583095523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10080224587451313055397015 15120336881176969583095523)
              ·
                refine ⟨22680505321765454374643285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15120336881176969583095523 22680505321765454374643285)
                ·
                  refine ⟨265787171739438918452851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22680505321765454374643285 265787171739438918452851)
                  ·
                    rfl

theorem cell21_1164642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1164642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164642 prefixEnd_1164642 := by exact prefixLift 1164642
  have htrace : WordTrace (prefixWord ++ tailWord_1164642) baseStart_1164642 baseEnd_1164642 := by
    simpa [prefixWord, tailWord_1164642, baseEnd_1164642] using wordTrace_append hprefix tailTrace_1164642
  have hstable : (prefixWord ++ tailWord_1164642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164642).length < 2 ^ (prefixWord ++ tailWord_1164642).sum := by decide
  have hdescent : baseEnd_1164642 < baseStart_1164642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164676 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1164676 : Nat := 118140960795 + 1164676 * 2 ^ 59
def prefixEnd_1164676 : Nat := 4983230072969 + 3 ^ 40 * 1164676 * 2
def baseEnd_1164676 : Nat := 265794931002662414886115

theorem tailTrace_1164676 : CollatzResearch.WordTrace tailWord_1164676 prefixEnd_1164676 265794931002662414886115 := by
  unfold tailWord_1164676
  simp only [CollatzResearch.WordTrace]
  refine ⟨21239611764292618834904941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28319482352390158446539921 21239611764292618834904941)
  ·
    refine ⟨7964854411609732063089353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21239611764292618834904941 7964854411609732063089353)
    ·
      refine ⟨5973640808707299047317015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7964854411609732063089353 5973640808707299047317015)
      ·
        refine ⟨8960461213060948570975523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5973640808707299047317015 8960461213060948570975523)
        ·
          refine ⟨13440691819591422856463285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8960461213060948570975523 13440691819591422856463285)
          ·
            refine ⟨1260064858086695892793433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13440691819591422856463285 1260064858086695892793433)
            ·
              refine ⟨945048643565021919595075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260064858086695892793433 945048643565021919595075)
              ·
                refine ⟨1417572965347532879392613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945048643565021919595075 1417572965347532879392613)
                ·
                  refine ⟨265794931002662414886115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417572965347532879392613 265794931002662414886115)
                  ·
                    rfl

theorem cell21_1164676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1164676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164676 prefixEnd_1164676 := by exact prefixLift 1164676
  have htrace : WordTrace (prefixWord ++ tailWord_1164676) baseStart_1164676 baseEnd_1164676 := by
    simpa [prefixWord, tailWord_1164676, baseEnd_1164676] using wordTrace_append hprefix tailTrace_1164676
  have hstable : (prefixWord ++ tailWord_1164676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164676).length < 2 ^ (prefixWord ++ tailWord_1164676).sum := by decide
  have hdescent : baseEnd_1164676 < baseStart_1164676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164704 : List Nat := [2, 1, 1, 4, 1, 2, 2, 5, 3]
def baseStart_1164704 : Nat := 118140960795 + 1164704 * 2 ^ 59
def prefixEnd_1164704 : Nat := 4983230072969 + 3 ^ 40 * 1164704 * 2
def baseEnd_1164704 : Nat := 265801320984140588419391

theorem tailTrace_1164704 : CollatzResearch.WordTrace tailWord_1164704 prefixEnd_1164704 265801320984140588419391 := by
  unfold tailWord_1164704
  simp only [CollatzResearch.WordTrace]
  refine ⟨21240122386241899225914583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28320163181655865634552777 21240122386241899225914583)
  ·
    refine ⟨31860183579362848838871875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21240122386241899225914583 31860183579362848838871875)
    ·
      refine ⟨47790275369044273258307813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31860183579362848838871875 47790275369044273258307813)
      ·
        refine ⟨8960676631695801235932715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47790275369044273258307813 8960676631695801235932715)
        ·
          refine ⟨13441014947543701853899073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8960676631695801235932715 13441014947543701853899073)
          ·
            refine ⟨10080761210657776390424305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13441014947543701853899073 10080761210657776390424305)
            ·
              refine ⟨7560570907993332292818229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10080761210657776390424305 7560570907993332292818229)
              ·
                refine ⟨708803522624374902451709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7560570907993332292818229 708803522624374902451709)
                ·
                  refine ⟨265801320984140588419391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708803522624374902451709 265801320984140588419391)
                  ·
                    rfl

theorem cell21_1164704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_1164704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164704 prefixEnd_1164704 := by exact prefixLift 1164704
  have htrace : WordTrace (prefixWord ++ tailWord_1164704) baseStart_1164704 baseEnd_1164704 := by
    simpa [prefixWord, tailWord_1164704, baseEnd_1164704] using wordTrace_append hprefix tailTrace_1164704
  have hstable : (prefixWord ++ tailWord_1164704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164704).length < 2 ^ (prefixWord ++ tailWord_1164704).sum := by decide
  have hdescent : baseEnd_1164704 < baseStart_1164704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164814 : List Nat := [4, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_1164814 : Nat := 118140960795 + 1164814 * 2 ^ 59
def prefixEnd_1164814 : Nat := 4983230072969 + 3 ^ 40 * 1164814 * 2
def baseEnd_1164814 : Nat := 265826424482804841585833

theorem tailTrace_1164814 : CollatzResearch.WordTrace tailWord_1164814 prefixEnd_1164814 265826424482804841585833 := by
  unfold tailWord_1164814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310532100260660904791687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28322837868056858158888997 5310532100260660904791687)
  ·
    refine ⟨7965798150390991357187531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5310532100260660904791687 7965798150390991357187531)
    ·
      refine ⟨11948697225586487035781297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7965798150390991357187531 11948697225586487035781297)
      ·
        refine ⟨8961522919189865276835973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11948697225586487035781297 8961522919189865276835973)
        ·
          refine ⟨1680285547348099739406745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8961522919189865276835973 1680285547348099739406745)
          ·
            refine ⟨1260214160511074804555059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1680285547348099739406745 1260214160511074804555059)
            ·
              refine ⟨1890321240766612206832589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260214160511074804555059 1890321240766612206832589)
              ·
                refine ⟨708870465287479577562221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1890321240766612206832589 708870465287479577562221)
                ·
                  refine ⟨265826424482804841585833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 708870465287479577562221 265826424482804841585833)
                  ·
                    rfl

theorem cell21_1164814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_1164814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164814 prefixEnd_1164814 := by exact prefixLift 1164814
  have htrace : WordTrace (prefixWord ++ tailWord_1164814) baseStart_1164814 baseEnd_1164814 := by
    simpa [prefixWord, tailWord_1164814, baseEnd_1164814] using wordTrace_append hprefix tailTrace_1164814
  have hstable : (prefixWord ++ tailWord_1164814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164814).length < 2 ^ (prefixWord ++ tailWord_1164814).sum := by decide
  have hdescent : baseEnd_1164814 < baseStart_1164814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164901 : List Nat := [1, 3, 1, 3, 3, 3, 1, 6]
def baseStart_1164901 : Nat := 118140960795 + 1164901 * 2 ^ 59
def prefixEnd_1164901 : Nat := 4983230072969 + 3 ^ 40 * 1164901 * 2
def baseEnd_1164901 : Nat := 88615426356037341211885

theorem tailTrace_1164901 : CollatzResearch.WordTrace tailWord_1164901 prefixEnd_1164901 88615426356037341211885 := by
  unfold tailWord_1164901
  simp only [CollatzResearch.WordTrace]
  refine ⟨42487429952770101096750557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28324953301846734064500371 42487429952770101096750557)
  ·
    refine ⟨15932786232288787911281459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42487429952770101096750557 15932786232288787911281459)
    ·
      refine ⟨23899179348433181866922189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15932786232288787911281459 23899179348433181866922189)
      ·
        refine ⟨8962192255662443200095821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23899179348433181866922189 8962192255662443200095821)
        ·
          refine ⟨3360822095873416200035933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8962192255662443200095821 3360822095873416200035933)
          ·
            refine ⟨1260308285952531075013475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3360822095873416200035933 1260308285952531075013475)
            ·
              refine ⟨1890462428928796612520213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260308285952531075013475 1890462428928796612520213)
              ·
                refine ⟨88615426356037341211885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1890462428928796612520213 88615426356037341211885)
                ·
                  rfl

theorem cell21_1164901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 6].length) (baseStart_1164901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164901 prefixEnd_1164901 := by exact prefixLift 1164901
  have htrace : WordTrace (prefixWord ++ tailWord_1164901) baseStart_1164901 baseEnd_1164901 := by
    simpa [prefixWord, tailWord_1164901, baseEnd_1164901] using wordTrace_append hprefix tailTrace_1164901
  have hstable : (prefixWord ++ tailWord_1164901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164901).length < 2 ^ (prefixWord ++ tailWord_1164901).sum := by decide
  have hdescent : baseEnd_1164901 < baseStart_1164901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164918 : List Nat := [5, 1, 1, 2, 2, 2, 3, 5]
def baseStart_1164918 : Nat := 118140960795 + 1164918 * 2 ^ 59
def prefixEnd_1164918 : Nat := 4983230072969 + 3 ^ 40 * 1164918 * 2
def baseEnd_1164918 : Nat := 88616719566574590617429

theorem tailTrace_1164918 : CollatzResearch.WordTrace tailWord_1164918 prefixEnd_1164918 88616719566574590617429 := by
  unfold tailWord_1164918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655503124606782062507463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28325366662472342000079605 2655503124606782062507463)
  ·
    refine ⟨3983254686910173093761195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655503124606782062507463 3983254686910173093761195)
    ·
      refine ⟨5974882030365259640641793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3983254686910173093761195 5974882030365259640641793)
      ·
        refine ⟨4481161522773944730481345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5974882030365259640641793 4481161522773944730481345)
        ·
          refine ⟨3360871142080458547861009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4481161522773944730481345 3360871142080458547861009)
          ·
            refine ⟨2520653356560343910895757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3360871142080458547861009 2520653356560343910895757)
            ·
              refine ⟨945245008710128966585909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520653356560343910895757 945245008710128966585909)
              ·
                refine ⟨88616719566574590617429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 945245008710128966585909 88616719566574590617429)
                ·
                  rfl

theorem cell21_1164918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_1164918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1164918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1164918 prefixEnd_1164918 := by exact prefixLift 1164918
  have htrace : WordTrace (prefixWord ++ tailWord_1164918) baseStart_1164918 baseEnd_1164918 := by
    simpa [prefixWord, tailWord_1164918, baseEnd_1164918] using wordTrace_append hprefix tailTrace_1164918
  have hstable : (prefixWord ++ tailWord_1164918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164918).length < 2 ^ (prefixWord ++ tailWord_1164918).sum := by decide
  have hdescent : baseEnd_1164918 < baseStart_1164918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165014 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1165014 : Nat := 118140960795 + 1165014 * 2 ^ 59
def prefixEnd_1165014 : Nat := 4983230072969 + 3 ^ 40 * 1165014 * 2
def baseEnd_1165014 : Nat := 265872067207648938252091

theorem tailTrace_1165014 : CollatzResearch.WordTrace tailWord_1165014 prefixEnd_1165014 265872067207648938252091 := by
  unfold tailWord_1165014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655721962585045087225881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28327700934240480930409397 2655721962585045087225881)
  ·
    refine ⟨1991791471938783815419411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2655721962585045087225881 1991791471938783815419411)
    ·
      refine ⟨2987687207908175723129117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1991791471938783815419411 2987687207908175723129117)
      ·
        refine ⟨1120382702965565896173419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2987687207908175723129117 1120382702965565896173419)
        ·
          refine ⟨1680574054448348844260129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120382702965565896173419 1680574054448348844260129)
          ·
            refine ⟨1260430540836261633195097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1680574054448348844260129 1260430540836261633195097)
            ·
              refine ⟨945322905627196224896323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260430540836261633195097 945322905627196224896323)
              ·
                refine ⟨1417984358440794337344485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945322905627196224896323 1417984358440794337344485)
                ·
                  refine ⟨265872067207648938252091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417984358440794337344485 265872067207648938252091)
                  ·
                    rfl

theorem cell21_1165014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1165014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165014 prefixEnd_1165014 := by exact prefixLift 1165014
  have htrace : WordTrace (prefixWord ++ tailWord_1165014) baseStart_1165014 baseEnd_1165014 := by
    simpa [prefixWord, tailWord_1165014, baseEnd_1165014] using wordTrace_append hprefix tailTrace_1165014
  have hstable : (prefixWord ++ tailWord_1165014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165014).length < 2 ^ (prefixWord ++ tailWord_1165014).sum := by decide
  have hdescent : baseEnd_1165014 < baseStart_1165014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165062 : List Nat := [6, 2, 2, 1, 2, 1, 1, 6]
def baseStart_1165062 : Nat := 118140960795 + 1165062 * 2 ^ 59
def prefixEnd_1165062 : Nat := 4983230072969 + 3 ^ 40 * 1165062 * 2
def baseEnd_1165062 : Nat := 88627673820537173817331

theorem tailTrace_1165062 : CollatzResearch.WordTrace tailWord_1165062 prefixEnd_1165062 88627673820537173817331 := by
  unfold tailWord_1165062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327915690787088299792545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28328868070124550395574293 1327915690787088299792545)
  ·
    refine ⟨995936768090316224844409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1327915690787088299792545 995936768090316224844409)
    ·
      refine ⟨746952576067737168633307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 995936768090316224844409 746952576067737168633307)
      ·
        refine ⟨1120428864101605752949961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746952576067737168633307 1120428864101605752949961)
        ·
          refine ⟨840321648076204314712471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1120428864101605752949961 840321648076204314712471)
          ·
            refine ⟨1260482472114306472068707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840321648076204314712471 1260482472114306472068707)
            ·
              refine ⟨1890723708171459708103061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260482472114306472068707 1890723708171459708103061)
              ·
                refine ⟨88627673820537173817331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1890723708171459708103061 88627673820537173817331)
                ·
                  rfl

theorem cell21_1165062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_1165062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165062 prefixEnd_1165062 := by exact prefixLift 1165062
  have htrace : WordTrace (prefixWord ++ tailWord_1165062) baseStart_1165062 baseEnd_1165062 := by
    simpa [prefixWord, tailWord_1165062, baseEnd_1165062] using wordTrace_append hprefix tailTrace_1165062
  have hstable : (prefixWord ++ tailWord_1165062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165062).length < 2 ^ (prefixWord ++ tailWord_1165062).sum := by decide
  have hdescent : baseEnd_1165062 < baseStart_1165062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165219 : List Nat := [1, 1, 1, 4, 1, 2, 1, 7, 3]
def baseStart_1165219 : Nat := 118140960795 + 1165219 * 2 ^ 59
def prefixEnd_1165219 : Nat := 4983230072969 + 3 ^ 40 * 1165219 * 2
def baseEnd_1165219 : Nat := 265918851000614137335005

theorem tailTrace_1165219 : CollatzResearch.WordTrace tailWord_1165219 prefixEnd_1165219 265918851000614137335005 := by
  unfold tailWord_1165219
  simp only [CollatzResearch.WordTrace]
  refine ⟨42499028365618041406826711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28332685577078694271217807 42499028365618041406826711)
  ·
    refine ⟨63748542548427062110240067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42499028365618041406826711 63748542548427062110240067)
    ·
      refine ⟨95622813822640593165360101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63748542548427062110240067 95622813822640593165360101)
      ·
        refine ⟨17929277591745111218505019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95622813822640593165360101 17929277591745111218505019)
        ·
          refine ⟨26893916387617666827757529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17929277591745111218505019 26893916387617666827757529)
          ·
            refine ⟨20170437290713250120818147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26893916387617666827757529 20170437290713250120818147)
            ·
              refine ⟨30255655936069875181227221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20170437290713250120818147 30255655936069875181227221)
              ·
                refine ⟨709116936001637699560013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30255655936069875181227221 709116936001637699560013)
                ·
                  refine ⟨265918851000614137335005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709116936001637699560013 265918851000614137335005)
                  ·
                    rfl

theorem cell21_1165219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 3].length) (baseStart_1165219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165219 prefixEnd_1165219 := by exact prefixLift 1165219
  have htrace : WordTrace (prefixWord ++ tailWord_1165219) baseStart_1165219 baseEnd_1165219 := by
    simpa [prefixWord, tailWord_1165219, baseEnd_1165219] using wordTrace_append hprefix tailTrace_1165219
  have hstable : (prefixWord ++ tailWord_1165219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165219).length < 2 ^ (prefixWord ++ tailWord_1165219).sum := by decide
  have hdescent : baseEnd_1165219 < baseStart_1165219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165270 : List Nat := [5, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1165270 : Nat := 118140960795 + 1165270 * 2 ^ 59
def prefixEnd_1165270 : Nat := 4983230072969 + 3 ^ 40 * 1165270 * 2
def baseEnd_1165270 : Nat := 265930489895449381984901

theorem tailTrace_1165270 : CollatzResearch.WordTrace tailWord_1165270 prefixEnd_1165270 265930489895449381984901 := by
  unfold tailWord_1165270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656305530527079819808329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28333925658955518077955509 2656305530527079819808329)
  ·
    refine ⟨1992229147895309864856247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2656305530527079819808329 1992229147895309864856247)
    ·
      refine ⟨2988343721842964797284371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1992229147895309864856247 2988343721842964797284371)
      ·
        refine ⟨4482515582764447195926557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2988343721842964797284371 4482515582764447195926557)
        ·
          refine ⟨1680943343536667698472459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4482515582764447195926557 1680943343536667698472459)
          ·
            refine ⟨2521415015305001547708689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680943343536667698472459 2521415015305001547708689)
            ·
              refine ⟨1891061261478751160781517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521415015305001547708689 1891061261478751160781517)
              ·
                refine ⟨709147973054531685293069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1891061261478751160781517 709147973054531685293069)
                ·
                  refine ⟨265930489895449381984901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709147973054531685293069 265930489895449381984901)
                  ·
                    rfl

theorem cell21_1165270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1165270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165270 prefixEnd_1165270 := by exact prefixLift 1165270
  have htrace : WordTrace (prefixWord ++ tailWord_1165270) baseStart_1165270 baseEnd_1165270 := by
    simpa [prefixWord, tailWord_1165270, baseEnd_1165270] using wordTrace_append hprefix tailTrace_1165270
  have hstable : (prefixWord ++ tailWord_1165270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165270).length < 2 ^ (prefixWord ++ tailWord_1165270).sum := by decide
  have hdescent : baseEnd_1165270 < baseStart_1165270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165295 : List Nat := [1, 1, 2, 1, 4, 2, 1, 6, 3]
def baseStart_1165295 : Nat := 118140960795 + 1165295 * 2 ^ 59
def prefixEnd_1165295 : Nat := 4983230072969 + 3 ^ 40 * 1165295 * 2
def baseEnd_1165295 : Nat := 265936195236054894068183

theorem tailTrace_1165295 : CollatzResearch.WordTrace tailWord_1165295 prefixEnd_1165295 265936195236054894068183 := by
  unfold tailWord_1165295
  simp only [CollatzResearch.WordTrace]
  refine ⟨42501800313342706386593339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28334533542228470924395559 42501800313342706386593339)
  ·
    refine ⟨63752700470014059579890009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42501800313342706386593339 63752700470014059579890009)
    ·
      refine ⟨47814525352510544684917507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63752700470014059579890009 47814525352510544684917507)
      ·
        refine ⟨71721788028765817027376261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47814525352510544684917507 71721788028765817027376261)
        ·
          refine ⟨13447835255393590692633049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71721788028765817027376261 13447835255393590692633049)
          ·
            refine ⟨10085876441545193019474787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13447835255393590692633049 10085876441545193019474787)
            ·
              refine ⟨15128814662317789529212181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10085876441545193019474787 15128814662317789529212181)
              ·
                refine ⟨709163187296146384181821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15128814662317789529212181 709163187296146384181821)
                ·
                  refine ⟨265936195236054894068183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709163187296146384181821 265936195236054894068183)
                  ·
                    rfl

theorem cell21_1165295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 3].length) (baseStart_1165295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165295 prefixEnd_1165295 := by exact prefixLift 1165295
  have htrace : WordTrace (prefixWord ++ tailWord_1165295) baseStart_1165295 baseEnd_1165295 := by
    simpa [prefixWord, tailWord_1165295, baseEnd_1165295] using wordTrace_append hprefix tailTrace_1165295
  have hstable : (prefixWord ++ tailWord_1165295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165295).length < 2 ^ (prefixWord ++ tailWord_1165295).sum := by decide
  have hdescent : baseEnd_1165295 < baseStart_1165295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165309 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1165309 : Nat := 118140960795 + 1165309 * 2 ^ 59
def prefixEnd_1165309 : Nat := 4983230072969 + 3 ^ 40 * 1165309 * 2
def baseEnd_1165309 : Nat := 265939390226793980834821

theorem tailTrace_1165309 : CollatzResearch.WordTrace tailWord_1165309 prefixEnd_1165309 265939390226793980834821 := by
  unfold tailWord_1165309
  simp only [CollatzResearch.WordTrace]
  refine ⟨42502310935291986777602981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28334873956861324518401987 42502310935291986777602981)
  ·
    refine ⟨7969183300367247520800559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42502310935291986777602981 7969183300367247520800559)
    ·
      refine ⟨11953774950550871281200839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7969183300367247520800559 11953774950550871281200839)
      ·
        refine ⟨17930662425826306921801259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11953774950550871281200839 17930662425826306921801259)
        ·
          refine ⟨26895993638739460382701889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17930662425826306921801259 26895993638739460382701889)
          ·
            refine ⟨20171995229054595287026417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26895993638739460382701889 20171995229054595287026417)
            ·
              refine ⟨15128996421790946465269813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20171995229054595287026417 15128996421790946465269813)
              ·
                refine ⟨1418343414542901231119045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15128996421790946465269813 1418343414542901231119045)
                ·
                  refine ⟨265939390226793980834821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418343414542901231119045 265939390226793980834821)
                  ·
                    rfl

theorem cell21_1165309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1165309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165309 prefixEnd_1165309 := by exact prefixLift 1165309
  have htrace : WordTrace (prefixWord ++ tailWord_1165309) baseStart_1165309 baseEnd_1165309 := by
    simpa [prefixWord, tailWord_1165309, baseEnd_1165309] using wordTrace_append hprefix tailTrace_1165309
  have hstable : (prefixWord ++ tailWord_1165309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165309).length < 2 ^ (prefixWord ++ tailWord_1165309).sum := by decide
  have hdescent : baseEnd_1165309 < baseStart_1165309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165323 : List Nat := [1, 1, 1, 1, 6, 1, 3, 7]
def baseStart_1165323 : Nat := 118140960795 + 1165323 * 2 ^ 59
def prefixEnd_1165323 : Nat := 4983230072969 + 3 ^ 40 * 1165323 * 2
def baseEnd_1165323 : Nat := 88647528405844355867153

theorem tailTrace_1165323 : CollatzResearch.WordTrace tailWord_1165323 prefixEnd_1165323 88647528405844355867153 := by
  unfold tailWord_1165323
  simp only [CollatzResearch.WordTrace]
  refine ⟨42502821557241267168612623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28335214371494178112408415 42502821557241267168612623)
  ·
    refine ⟨63754232335861900752918935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42502821557241267168612623 63754232335861900752918935)
    ·
      refine ⟨95631348503792851129378403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63754232335861900752918935 95631348503792851129378403)
      ·
        refine ⟨143447022755689276694067605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95631348503792851129378403 143447022755689276694067605)
        ·
          refine ⟨6724079191672934845034419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143447022755689276694067605 6724079191672934845034419)
          ·
            refine ⟨10086118787509402267551629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6724079191672934845034419 10086118787509402267551629)
            ·
              refine ⟨3782294545316025850331861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10086118787509402267551629 3782294545316025850331861)
              ·
                refine ⟨88647528405844355867153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3782294545316025850331861 88647528405844355867153)
                ·
                  rfl

theorem cell21_1165323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_1165323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165323 prefixEnd_1165323 := by exact prefixLift 1165323
  have htrace : WordTrace (prefixWord ++ tailWord_1165323) baseStart_1165323 baseEnd_1165323 := by
    simpa [prefixWord, tailWord_1165323, baseEnd_1165323] using wordTrace_append hprefix tailTrace_1165323
  have hstable : (prefixWord ++ tailWord_1165323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165323).length < 2 ^ (prefixWord ++ tailWord_1165323).sum := by decide
  have hdescent : baseEnd_1165323 < baseStart_1165323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165340 : List Nat := [2, 2, 3, 1, 3, 3, 7]
def baseStart_1165340 : Nat := 118140960795 + 1165340 * 2 ^ 59
def prefixEnd_1165340 : Nat := 4983230072969 + 3 ^ 40 * 1165340 * 2
def baseEnd_1165340 : Nat := 29549607205460535090899

theorem tailTrace_1165340 : CollatzResearch.WordTrace tailWord_1165340 prefixEnd_1165340 29549607205460535090899 := by
  unfold tailWord_1165340
  simp only [CollatzResearch.WordTrace]
  refine ⟨21251720799089839535990737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28335627732119786047987649 21251720799089839535990737)
  ·
    refine ⟨15938790599317379651993053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21251720799089839535990737 15938790599317379651993053)
    ·
      refine ⟨5977046474744017369497395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15938790599317379651993053 5977046474744017369497395)
      ·
        refine ⟨8965569712116026054246093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5977046474744017369497395 8965569712116026054246093)
        ·
          refine ⟨3362088642043509770342285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8965569712116026054246093 3362088642043509770342285)
          ·
            refine ⟨1260783240766316163878357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3362088642043509770342285 1260783240766316163878357)
            ·
              refine ⟨29549607205460535090899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1260783240766316163878357 29549607205460535090899)
              ·
                rfl

theorem cell21_1165340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 7].length) (baseStart_1165340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165340 prefixEnd_1165340 := by exact prefixLift 1165340
  have htrace : WordTrace (prefixWord ++ tailWord_1165340) baseStart_1165340 baseEnd_1165340 := by
    simpa [prefixWord, tailWord_1165340, baseEnd_1165340] using wordTrace_append hprefix tailTrace_1165340
  have hstable : (prefixWord ++ tailWord_1165340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165340).length < 2 ^ (prefixWord ++ tailWord_1165340).sum := by decide
  have hdescent : baseEnd_1165340 < baseStart_1165340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165405 : List Nat := [1, 4, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1165405 : Nat := 118140960795 + 1165405 * 2 ^ 59
def prefixEnd_1165405 : Nat := 4983230072969 + 3 ^ 40 * 1165405 * 2
def baseEnd_1165405 : Nat := 265961298734719147234625

theorem tailTrace_1165405 : CollatzResearch.WordTrace tailWord_1165405 prefixEnd_1165405 265961298734719147234625 := by
  unfold tailWord_1165405
  simp only [CollatzResearch.WordTrace]
  refine ⟨42505812342944195173097669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28337208228629463448731779 42505812342944195173097669)
  ·
    refine ⟨7969839814302036594955813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42505812342944195173097669 7969839814302036594955813)
    ·
      refine ⟨1494344965181631861554215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7969839814302036594955813 1494344965181631861554215)
      ·
        refine ⟨2241517447772447792331323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494344965181631861554215 2241517447772447792331323)
        ·
          refine ⟨3362276171658671688496985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241517447772447792331323 3362276171658671688496985)
          ·
            refine ⟨2521707128744003766372739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3362276171658671688496985 2521707128744003766372739)
            ·
              refine ⟨3782560693116005649559109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521707128744003766372739 3782560693116005649559109)
              ·
                refine ⟨709230129959251059292333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3782560693116005649559109 709230129959251059292333)
                ·
                  refine ⟨265961298734719147234625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709230129959251059292333 265961298734719147234625)
                  ·
                    rfl

theorem cell21_1165405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1165405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165405 prefixEnd_1165405 := by exact prefixLift 1165405
  have htrace : WordTrace (prefixWord ++ tailWord_1165405) baseStart_1165405 baseEnd_1165405 := by
    simpa [prefixWord, tailWord_1165405, baseEnd_1165405] using wordTrace_append hprefix tailTrace_1165405
  have hstable : (prefixWord ++ tailWord_1165405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165405).length < 2 ^ (prefixWord ++ tailWord_1165405).sum := by decide
  have hdescent : baseEnd_1165405 < baseStart_1165405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165447 : List Nat := [1, 1, 4, 2, 1, 1, 3, 5, 3]
def baseStart_1165447 : Nat := 118140960795 + 1165447 * 2 ^ 59
def prefixEnd_1165447 : Nat := 4983230072969 + 3 ^ 40 * 1165447 * 2
def baseEnd_1165447 : Nat := 265970883706936407534539

theorem tailTrace_1165447 : CollatzResearch.WordTrace tailWord_1165447 prefixEnd_1165447 265970883706936407534539 := by
  unfold tailWord_1165447
  simp only [CollatzResearch.WordTrace]
  refine ⟨42507344208792036346126595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28338229472528024230751063 42507344208792036346126595)
  ·
    refine ⟨63761016313188054519189893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42507344208792036346126595 63761016313188054519189893)
    ·
      refine ⟨11955190558722760222348105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63761016313188054519189893 11955190558722760222348105)
      ·
        refine ⟨8966392919042070166761079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11955190558722760222348105 8966392919042070166761079)
        ·
          refine ⟨13449589378563105250141619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8966392919042070166761079 13449589378563105250141619)
          ·
            refine ⟨20174384067844657875212429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13449589378563105250141619 20174384067844657875212429)
            ·
              refine ⟨7565394025441746703204661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20174384067844657875212429 7565394025441746703204661)
              ·
                refine ⟨709255689885163753425437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7565394025441746703204661 709255689885163753425437)
                ·
                  refine ⟨265970883706936407534539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709255689885163753425437 265970883706936407534539)
                  ·
                    rfl

theorem cell21_1165447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 3].length) (baseStart_1165447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165447 prefixEnd_1165447 := by exact prefixLift 1165447
  have htrace : WordTrace (prefixWord ++ tailWord_1165447) baseStart_1165447 baseEnd_1165447 := by
    simpa [prefixWord, tailWord_1165447, baseEnd_1165447] using wordTrace_append hprefix tailTrace_1165447
  have hstable : (prefixWord ++ tailWord_1165447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165447).length < 2 ^ (prefixWord ++ tailWord_1165447).sum := by decide
  have hdescent : baseEnd_1165447 < baseStart_1165447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165537 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 4]
def baseStart_1165537 : Nat := 118140960795 + 1165537 * 2 ^ 59
def prefixEnd_1165537 : Nat := 4983230072969 + 3 ^ 40 * 1165537 * 2
def baseEnd_1165537 : Nat := 265991422933116251034355

theorem tailTrace_1165537 : CollatzResearch.WordTrace tailWord_1165537 prefixEnd_1165537 265991422933116251034355 := by
  unfold tailWord_1165537
  simp only [CollatzResearch.WordTrace]
  refine ⟨42510626778465981716902865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28340417852310654477935243 42510626778465981716902865)
  ·
    refine ⟨31882970083849486287677149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42510626778465981716902865 31882970083849486287677149)
    ·
      refine ⟨11956113781443557357878931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31882970083849486287677149 11956113781443557357878931)
      ·
        refine ⟨17934170672165336036818397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11956113781443557357878931 17934170672165336036818397)
        ·
          refine ⟨6725314002062001013806899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17934170672165336036818397 6725314002062001013806899)
          ·
            refine ⟨10087971003093001520710349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6725314002062001013806899 10087971003093001520710349)
            ·
              refine ⟨3782989126159875570266381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10087971003093001520710349 3782989126159875570266381)
              ·
                refine ⟨1418620922309953338849893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3782989126159875570266381 1418620922309953338849893)
                ·
                  refine ⟨265991422933116251034355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418620922309953338849893 265991422933116251034355)
                  ·
                    rfl

theorem cell21_1165537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_1165537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165537 prefixEnd_1165537 := by exact prefixLift 1165537
  have htrace : WordTrace (prefixWord ++ tailWord_1165537) baseStart_1165537 baseEnd_1165537 := by
    simpa [prefixWord, tailWord_1165537, baseEnd_1165537] using wordTrace_append hprefix tailTrace_1165537
  have hstable : (prefixWord ++ tailWord_1165537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165537).length < 2 ^ (prefixWord ++ tailWord_1165537).sum := by decide
  have hdescent : baseEnd_1165537 < baseStart_1165537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165551 : List Nat := [1, 1, 2, 1, 6, 1, 2, 7]
def baseStart_1165551 : Nat := 118140960795 + 1165551 * 2 ^ 59
def prefixEnd_1165551 : Nat := 4983230072969 + 3 ^ 40 * 1165551 * 2
def baseEnd_1165551 : Nat := 88664872641285112600331

theorem tailTrace_1165551 : CollatzResearch.WordTrace tailWord_1165551 prefixEnd_1165551 88664872641285112600331 := by
  unfold tailWord_1165551
  simp only [CollatzResearch.WordTrace]
  refine ⟨42511137400415262107912507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28340758266943508071941671 42511137400415262107912507)
  ·
    refine ⟨63766706100622893161868761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42511137400415262107912507 63766706100622893161868761)
    ·
      refine ⟨47825029575467169871401571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63766706100622893161868761 47825029575467169871401571)
      ·
        refine ⟨71737544363200754807102357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47825029575467169871401571 71737544363200754807102357)
        ·
          refine ⟨3362697392025035381582923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71737544363200754807102357 3362697392025035381582923)
          ·
            refine ⟨5044046088037553072374385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362697392025035381582923 5044046088037553072374385)
            ·
              refine ⟨3783034566028164804280789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5044046088037553072374385 3783034566028164804280789)
              ·
                refine ⟨88664872641285112600331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3783034566028164804280789 88664872641285112600331)
                ·
                  rfl

theorem cell21_1165551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_1165551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165551 prefixEnd_1165551 := by exact prefixLift 1165551
  have htrace : WordTrace (prefixWord ++ tailWord_1165551) baseStart_1165551 baseEnd_1165551 := by
    simpa [prefixWord, tailWord_1165551, baseEnd_1165551] using wordTrace_append hprefix tailTrace_1165551
  have hstable : (prefixWord ++ tailWord_1165551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165551).length < 2 ^ (prefixWord ++ tailWord_1165551).sum := by decide
  have hdescent : baseEnd_1165551 < baseStart_1165551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165582 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1165582 : Nat := 118140960795 + 1165582 * 2 ^ 59
def prefixEnd_1165582 : Nat := 4983230072969 + 3 ^ 40 * 1165582 * 2
def baseEnd_1165582 : Nat := 266001692546206172784263

theorem tailTrace_1165582 : CollatzResearch.WordTrace tailWord_1165582 prefixEnd_1165582 266001692546206172784263 := by
  unfold tailWord_1165582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5314033507912869300286375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28341512042201969601527333 5314033507912869300286375)
  ·
    refine ⟨7971050261869303950429563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5314033507912869300286375 7971050261869303950429563)
    ·
      refine ⟨11956575392803955925644345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7971050261869303950429563 11956575392803955925644345)
      ·
        refine ⟨8967431544602966944233259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11956575392803955925644345 8967431544602966944233259)
        ·
          refine ⟨13451147316904450416349889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8967431544602966944233259 13451147316904450416349889)
          ·
            refine ⟨10088360487678337812262417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13451147316904450416349889 10088360487678337812262417)
            ·
              refine ⟨7566270365758753359196813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10088360487678337812262417 7566270365758753359196813)
              ·
                refine ⟨2837351387159532509698805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7566270365758753359196813 2837351387159532509698805)
                ·
                  refine ⟨266001692546206172784263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2837351387159532509698805 266001692546206172784263)
                  ·
                    rfl

theorem cell21_1165582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1165582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165582 prefixEnd_1165582 := by exact prefixLift 1165582
  have htrace : WordTrace (prefixWord ++ tailWord_1165582) baseStart_1165582 baseEnd_1165582 := by
    simpa [prefixWord, tailWord_1165582, baseEnd_1165582] using wordTrace_append hprefix tailTrace_1165582
  have hstable : (prefixWord ++ tailWord_1165582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165582).length < 2 ^ (prefixWord ++ tailWord_1165582).sum := by decide
  have hdescent : baseEnd_1165582 < baseStart_1165582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165596 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1165596 : Nat := 118140960795 + 1165596 * 2 ^ 59
def prefixEnd_1165596 : Nat := 4983230072969 + 3 ^ 40 * 1165596 * 2
def baseEnd_1165596 : Nat := 266004887536945259550901

theorem tailTrace_1165596 : CollatzResearch.WordTrace tailWord_1165596 prefixEnd_1165596 266004887536945259550901 := by
  unfold tailWord_1165596
  simp only [CollatzResearch.WordTrace]
  refine ⟨21256389342626117396650321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28341852456834823195533761 21256389342626117396650321)
  ·
    refine ⟨15942292006969588047487741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21256389342626117396650321 15942292006969588047487741)
    ·
      refine ⟨5978359502613595517807903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15942292006969588047487741 5978359502613595517807903)
      ·
        refine ⟨8967539253920393276711855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5978359502613595517807903 8967539253920393276711855)
        ·
          refine ⟨13451308880880589915067783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8967539253920393276711855 13451308880880589915067783)
          ·
            refine ⟨20176963321320884872601675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13451308880880589915067783 20176963321320884872601675)
            ·
              refine ⟨30265444981981327308902513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20176963321320884872601675 30265444981981327308902513)
              ·
                refine ⟨22699083736485995481676885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30265444981981327308902513 22699083736485995481676885)
                ·
                  refine ⟨266004887536945259550901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22699083736485995481676885 266004887536945259550901)
                  ·
                    rfl

theorem cell21_1165596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1165596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165596 prefixEnd_1165596 := by exact prefixLift 1165596
  have htrace : WordTrace (prefixWord ++ tailWord_1165596) baseStart_1165596 baseEnd_1165596 := by
    simpa [prefixWord, tailWord_1165596, baseEnd_1165596] using wordTrace_append hprefix tailTrace_1165596
  have hstable : (prefixWord ++ tailWord_1165596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165596).length < 2 ^ (prefixWord ++ tailWord_1165596).sum := by decide
  have hdescent : baseEnd_1165596 < baseStart_1165596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165630 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1165630 : Nat := 118140960795 + 1165630 * 2 ^ 59
def prefixEnd_1165630 : Nat := 4983230072969 + 3 ^ 40 * 1165630 * 2
def baseEnd_1165630 : Nat := 266012646800168755984165

theorem tailTrace_1165630 : CollatzResearch.WordTrace tailWord_1165630 prefixEnd_1165630 266012646800168755984165 := by
  unfold tailWord_1165630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5314252345891132325004793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28342679178086039066692229 5314252345891132325004793)
  ·
    refine ⟨3985689259418349243753595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5314252345891132325004793 3985689259418349243753595)
    ·
      refine ⟨5978533889127523865630393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3985689259418349243753595 5978533889127523865630393)
      ·
        refine ⟨4483900416845642899222795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5978533889127523865630393 4483900416845642899222795)
        ·
          refine ⟨6725850625268464348834193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4483900416845642899222795 6725850625268464348834193)
          ·
            refine ⟨5044387968951348261625645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6725850625268464348834193 5044387968951348261625645)
            ·
              refine ⟨1891645488356755598109617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5044387968951348261625645 1891645488356755598109617)
              ·
                refine ⟨1418734116267566698582213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891645488356755598109617 1418734116267566698582213)
                ·
                  refine ⟨266012646800168755984165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418734116267566698582213 266012646800168755984165)
                  ·
                    rfl

theorem cell21_1165630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1165630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165630 prefixEnd_1165630 := by exact prefixLift 1165630
  have htrace : WordTrace (prefixWord ++ tailWord_1165630) baseStart_1165630 baseEnd_1165630 := by
    simpa [prefixWord, tailWord_1165630, baseEnd_1165630] using wordTrace_append hprefix tailTrace_1165630
  have hstable : (prefixWord ++ tailWord_1165630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165630).length < 2 ^ (prefixWord ++ tailWord_1165630).sum := by decide
  have hdescent : baseEnd_1165630 < baseStart_1165630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165703 : List Nat := [1, 1, 4, 2, 2, 1, 4, 6]
def baseStart_1165703 : Nat := 118140960795 + 1165703 * 2 ^ 59
def prefixEnd_1165703 : Nat := 4983230072969 + 3 ^ 40 * 1165703 * 2
def baseEnd_1165703 : Nat := 88676435464912283755783

theorem tailTrace_1165703 : CollatzResearch.WordTrace tailWord_1165703 prefixEnd_1165703 88676435464912283755783 := by
  unfold tailWord_1165703
  simp only [CollatzResearch.WordTrace]
  refine ⟨42516681295864592067445763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28344454197243061378297175 42516681295864592067445763)
  ·
    refine ⟨63775021943796888101168645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42516681295864592067445763 63775021943796888101168645)
    ·
      refine ⟨11957816614461916518969121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63775021943796888101168645 11957816614461916518969121)
      ·
        refine ⟨8968362460846437389226841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11957816614461916518969121 8968362460846437389226841)
        ·
          refine ⟨6726271845634828041920131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8968362460846437389226841 6726271845634828041920131)
          ·
            refine ⟨10089407768452242062880197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726271845634828041920131 10089407768452242062880197)
            ·
              refine ⟨1891763956584795386790037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10089407768452242062880197 1891763956584795386790037)
              ·
                refine ⟨88676435464912283755783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1891763956584795386790037 88676435464912283755783)
                ·
                  rfl

theorem cell21_1165703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 6].length) (baseStart_1165703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165703 prefixEnd_1165703 := by exact prefixLift 1165703
  have htrace : WordTrace (prefixWord ++ tailWord_1165703) baseStart_1165703 baseEnd_1165703 := by
    simpa [prefixWord, tailWord_1165703, baseEnd_1165703] using wordTrace_append hprefix tailTrace_1165703
  have hstable : (prefixWord ++ tailWord_1165703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165703).length < 2 ^ (prefixWord ++ tailWord_1165703).sum := by decide
  have hdescent : baseEnd_1165703 < baseStart_1165703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165717 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1165717 : Nat := 118140960795 + 1165717 * 2 ^ 59
def prefixEnd_1165717 : Nat := 4983230072969 + 3 ^ 40 * 1165717 * 2
def baseEnd_1165717 : Nat := 266032501385475938033987

theorem tailTrace_1165717 : CollatzResearch.WordTrace tailWord_1165717 prefixEnd_1165717 266032501385475938033987 := by
  unfold tailWord_1165717
  simp only [CollatzResearch.WordTrace]
  refine ⟨42517191917813872458455405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28344794611875914972303603 42517191917813872458455405)
  ·
    refine ⟨15943946969180202171920777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42517191917813872458455405 15943946969180202171920777)
    ·
      refine ⟨11957960226885151628940583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15943946969180202171920777 11957960226885151628940583)
      ·
        refine ⟨17936940340327727443410875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11957960226885151628940583 17936940340327727443410875)
        ·
          refine ⟨26905410510491591165116313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17936940340327727443410875 26905410510491591165116313)
          ·
            refine ⟨20179057882868693373837235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26905410510491591165116313 20179057882868693373837235)
            ·
              refine ⟨30268586824303040060755853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20179057882868693373837235 30268586824303040060755853)
              ·
                refine ⟨11350720059113640022783445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30268586824303040060755853 11350720059113640022783445)
                ·
                  refine ⟨266032501385475938033987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11350720059113640022783445 266032501385475938033987)
                  ·
                    rfl

theorem cell21_1165717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1165717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165717 prefixEnd_1165717 := by exact prefixLift 1165717
  have htrace : WordTrace (prefixWord ++ tailWord_1165717) baseStart_1165717 baseEnd_1165717 := by
    simpa [prefixWord, tailWord_1165717, baseEnd_1165717] using wordTrace_append hprefix tailTrace_1165717
  have hstable : (prefixWord ++ tailWord_1165717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165717).length < 2 ^ (prefixWord ++ tailWord_1165717).sum := by decide
  have hdescent : baseEnd_1165717 < baseStart_1165717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165751 : List Nat := [1, 1, 3, 1, 3, 4, 1, 4, 3]
def baseStart_1165751 : Nat := 118140960795 + 1165751 * 2 ^ 59
def prefixEnd_1165751 : Nat := 4983230072969 + 3 ^ 40 * 1165751 * 2
def baseEnd_1165751 : Nat := 266040260648699434467251

theorem tailTrace_1165751 : CollatzResearch.WordTrace tailWord_1165751 prefixEnd_1165751 266040260648699434467251 := by
  unfold tailWord_1165751
  simp only [CollatzResearch.WordTrace]
  refine ⟨42518431999690696265193107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28345621333127130843462071 42518431999690696265193107)
  ·
    refine ⟨63777647999536044397789661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42518431999690696265193107 63777647999536044397789661)
    ·
      refine ⟨23916617999826016649171123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63777647999536044397789661 23916617999826016649171123)
      ·
        refine ⟨35874926999739024973756685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23916617999826016649171123 35874926999739024973756685)
        ·
          refine ⟨13453097624902134365158757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35874926999739024973756685 13453097624902134365158757)
          ·
            refine ⟨2522455804669150193467267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13453097624902134365158757 2522455804669150193467267)
            ·
              refine ⟨3783683707003725290200901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2522455804669150193467267 3783683707003725290200901)
              ·
                refine ⟨709440695063198491912669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3783683707003725290200901 709440695063198491912669)
                ·
                  refine ⟨266040260648699434467251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709440695063198491912669 266040260648699434467251)
                  ·
                    rfl

theorem cell21_1165751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 3].length) (baseStart_1165751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165751 prefixEnd_1165751 := by exact prefixLift 1165751
  have htrace : WordTrace (prefixWord ++ tailWord_1165751) baseStart_1165751 baseEnd_1165751 := by
    simpa [prefixWord, tailWord_1165751, baseEnd_1165751] using wordTrace_append hprefix tailTrace_1165751
  have hstable : (prefixWord ++ tailWord_1165751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165751).length < 2 ^ (prefixWord ++ tailWord_1165751).sum := by decide
  have hdescent : baseEnd_1165751 < baseStart_1165751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165793 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 7]
def baseStart_1165793 : Nat := 118140960795 + 1165793 * 2 ^ 59
def prefixEnd_1165793 : Nat := 4983230072969 + 3 ^ 40 * 1165793 * 2
def baseEnd_1165793 : Nat := 266049845620916694767165

theorem tailTrace_1165793 : CollatzResearch.WordTrace tailWord_1165793 prefixEnd_1165793 266049845620916694767165 := by
  unfold tailWord_1165793
  simp only [CollatzResearch.WordTrace]
  refine ⟨42519963865538537438222033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28346642577025691625481355 42519963865538537438222033)
  ·
    refine ⟨31889972899153903078666525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42519963865538537438222033 31889972899153903078666525)
    ·
      refine ⟨11958739837182713654499947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31889972899153903078666525 11958739837182713654499947)
      ·
        refine ⟨17938109755774070481749921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11958739837182713654499947 17938109755774070481749921)
        ·
          refine ⟨13453582316830552861312441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17938109755774070481749921 13453582316830552861312441)
          ·
            refine ⟨10090186737622914645984331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13453582316830552861312441 10090186737622914645984331)
            ·
              refine ⟨15135280106434371968976497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10090186737622914645984331 15135280106434371968976497)
              ·
                refine ⟨11351460079825778976732373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15135280106434371968976497 11351460079825778976732373)
                ·
                  refine ⟨266049845620916694767165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11351460079825778976732373 266049845620916694767165)
                  ·
                    rfl

theorem cell21_1165793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_1165793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165793 prefixEnd_1165793 := by exact prefixLift 1165793
  have htrace : WordTrace (prefixWord ++ tailWord_1165793) baseStart_1165793 baseEnd_1165793 := by
    simpa [prefixWord, tailWord_1165793, baseEnd_1165793] using wordTrace_append hprefix tailTrace_1165793
  have hstable : (prefixWord ++ tailWord_1165793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165793).length < 2 ^ (prefixWord ++ tailWord_1165793).sum := by decide
  have hdescent : baseEnd_1165793 < baseStart_1165793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165830 : List Nat := [6, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1165830 : Nat := 118140960795 + 1165830 * 2 ^ 59
def prefixEnd_1165830 : Nat := 4983230072969 + 3 ^ 40 * 1165830 * 2
def baseEnd_1165830 : Nat := 88686096508337617550141

theorem tailTrace_1165830 : CollatzResearch.WordTrace tailWord_1165830 prefixEnd_1165830 88686096508337617550141 := by
  unfold tailWord_1165830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328791042700140398666217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28347542244269661838212629 1328791042700140398666217)
  ·
    refine ⟨996593282025105298999663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1328791042700140398666217 996593282025105298999663)
    ·
      refine ⟨1494889923037657948499495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 996593282025105298999663 1494889923037657948499495)
      ·
        refine ⟨2242334884556486922749243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494889923037657948499495 2242334884556486922749243)
        ·
          refine ⟨3363502326834730384123865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242334884556486922749243 3363502326834730384123865)
          ·
            refine ⟨2522626745126047788092899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3363502326834730384123865 2522626745126047788092899)
            ·
              refine ⟨3783940117689071682139349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2522626745126047788092899 3783940117689071682139349)
              ·
                refine ⟨88686096508337617550141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3783940117689071682139349 88686096508337617550141)
                ·
                  rfl

theorem cell21_1165830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1165830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165830 prefixEnd_1165830 := by exact prefixLift 1165830
  have htrace : WordTrace (prefixWord ++ tailWord_1165830) baseStart_1165830 baseEnd_1165830 := by
    simpa [prefixWord, tailWord_1165830, baseEnd_1165830] using wordTrace_append hprefix tailTrace_1165830
  have hstable : (prefixWord ++ tailWord_1165830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165830).length < 2 ^ (prefixWord ++ tailWord_1165830).sum := by decide
  have hdescent : baseEnd_1165830 < baseStart_1165830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165945 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 7]
def baseStart_1165945 : Nat := 118140960795 + 1165945 * 2 ^ 59
def prefixEnd_1165945 : Nat := 4983230072969 + 3 ^ 40 * 1165945 * 2
def baseEnd_1165945 : Nat := 266084534091798208233521

theorem tailTrace_1165945 : CollatzResearch.WordTrace tailWord_1165945 prefixEnd_1165945 266084534091798208233521 := by
  unfold tailWord_1165945
  simp only [CollatzResearch.WordTrace]
  refine ⟨42525507760987867397755289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28350338507325244931836859 42525507760987867397755289)
  ·
    refine ⟨31894130820740900548316467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42525507760987867397755289 31894130820740900548316467)
    ·
      refine ⟨47841196231111350822474701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31894130820740900548316467 47841196231111350822474701)
      ·
        refine ⟨17940448586666756558428013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47841196231111350822474701 17940448586666756558428013)
        ·
          refine ⟨6727668220000033709410505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17940448586666756558428013 6727668220000033709410505)
          ·
            refine ⟨5045751165000025282057879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6727668220000033709410505 5045751165000025282057879)
            ·
              refine ⟨7568626747500037923086819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045751165000025282057879 7568626747500037923086819)
              ·
                refine ⟨11352940121250056884630229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7568626747500037923086819 11352940121250056884630229)
                ·
                  refine ⟨266084534091798208233521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11352940121250056884630229 266084534091798208233521)
                  ·
                    rfl

theorem cell21_1165945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_1165945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165945 prefixEnd_1165945 := by exact prefixLift 1165945
  have htrace : WordTrace (prefixWord ++ tailWord_1165945) baseStart_1165945 baseEnd_1165945 := by
    simpa [prefixWord, tailWord_1165945, baseEnd_1165945] using wordTrace_append hprefix tailTrace_1165945
  have hstable : (prefixWord ++ tailWord_1165945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165945).length < 2 ^ (prefixWord ++ tailWord_1165945).sum := by decide
  have hdescent : baseEnd_1165945 < baseStart_1165945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165976 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_1165976 : Nat := 118140960795 + 1165976 * 2 ^ 59
def prefixEnd_1165976 : Nat := 4983230072969 + 3 ^ 40 * 1165976 * 2
def baseEnd_1165976 : Nat := 266091608714149043216791

theorem tailTrace_1165976 : CollatzResearch.WordTrace tailWord_1165976 prefixEnd_1165976 266091608714149043216791 := by
  unfold tailWord_1165976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263319211937779846066891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28351092282583706461422521 21263319211937779846066891)
  ·
    refine ⟨31894978817906669769100337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21263319211937779846066891 31894978817906669769100337)
    ·
      refine ⟨23921234113430002326825253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31894978817906669769100337 23921234113430002326825253)
      ·
        refine ⟨4485231396268125436279735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23921234113430002326825253 4485231396268125436279735)
        ·
          refine ⟨6727847094402188154419603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4485231396268125436279735 6727847094402188154419603)
          ·
            refine ⟨10091770641603282231629405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727847094402188154419603 10091770641603282231629405)
            ·
              refine ⟨3784413990601230836861027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10091770641603282231629405 3784413990601230836861027)
              ·
                refine ⟨5676620985901846255291541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784413990601230836861027 5676620985901846255291541)
                ·
                  refine ⟨266091608714149043216791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5676620985901846255291541 266091608714149043216791)
                  ·
                    rfl

theorem cell21_1165976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_1165976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1165976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1165976 prefixEnd_1165976 := by exact prefixLift 1165976
  have htrace : WordTrace (prefixWord ++ tailWord_1165976) baseStart_1165976 baseEnd_1165976 := by
    simpa [prefixWord, tailWord_1165976, baseEnd_1165976] using wordTrace_append hprefix tailTrace_1165976
  have hstable : (prefixWord ++ tailWord_1165976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165976).length < 2 ^ (prefixWord ++ tailWord_1165976).sum := by decide
  have hdescent : baseEnd_1165976 < baseStart_1165976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166007 : List Nat := [1, 1, 3, 1, 6, 1, 1, 7]
def baseStart_1166007 : Nat := 118140960795 + 1166007 * 2 ^ 59
def prefixEnd_1166007 : Nat := 4983230072969 + 3 ^ 40 * 1166007 * 2
def baseEnd_1166007 : Nat := 88699561112166626066687

theorem tailTrace_1166007 : CollatzResearch.WordTrace tailWord_1166007 prefixEnd_1166007 88699561112166626066687 := by
  unfold tailWord_1166007
  simp only [CollatzResearch.WordTrace]
  refine ⟨42527769086763251986512275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28351846057842167991008183 42527769086763251986512275)
  ·
    refine ⟨63791653630144877979768413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42527769086763251986512275 63791653630144877979768413)
    ·
      refine ⟨23921870111304329242413155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63791653630144877979768413 23921870111304329242413155)
      ·
        refine ⟨35882805166956493863619733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23921870111304329242413155 35882805166956493863619733)
        ·
          refine ⟨1682006492201085649857175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35882805166956493863619733 1682006492201085649857175)
          ·
            refine ⟨2523009738301628474785763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682006492201085649857175 2523009738301628474785763)
            ·
              refine ⟨3784514607452442712178645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523009738301628474785763 3784514607452442712178645)
              ·
                refine ⟨88699561112166626066687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3784514607452442712178645 88699561112166626066687)
                ·
                  rfl

theorem cell21_1166007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 7].length) (baseStart_1166007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166007 prefixEnd_1166007 := by exact prefixLift 1166007
  have htrace : WordTrace (prefixWord ++ tailWord_1166007) baseStart_1166007 baseEnd_1166007 := by
    simpa [prefixWord, tailWord_1166007, baseEnd_1166007] using wordTrace_append hprefix tailTrace_1166007
  have hstable : (prefixWord ++ tailWord_1166007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166007).length < 2 ^ (prefixWord ++ tailWord_1166007).sum := by decide
  have hdescent : baseEnd_1166007 < baseStart_1166007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166114 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1166114 : Nat := 118140960795 + 1166114 * 2 ^ 59
def prefixEnd_1166114 : Nat := 4983230072969 + 3 ^ 40 * 1166114 * 2
def baseEnd_1166114 : Nat := 266123102194291469916509

theorem tailTrace_1166114 : CollatzResearch.WordTrace tailWord_1166114 prefixEnd_1166114 266123102194291469916509 := by
  unfold tailWord_1166114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632917924343902315164349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28354447798250406173771597 10632917924343902315164349)
  ·
    refine ⟨3987344221628963368186631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10632917924343902315164349 3987344221628963368186631)
    ·
      refine ⟨5981016332443445052279947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987344221628963368186631 5981016332443445052279947)
      ·
        refine ⟨8971524498665167578419921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5981016332443445052279947 8971524498665167578419921)
        ·
          refine ⟨6728643373998875683814941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8971524498665167578419921 6728643373998875683814941)
          ·
            refine ⟨2523241265249578381430603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6728643373998875683814941 2523241265249578381430603)
            ·
              refine ⟨3784861897874367572145905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523241265249578381430603 3784861897874367572145905)
              ·
                refine ⟨2838646423405775679109429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784861897874367572145905 2838646423405775679109429)
                ·
                  refine ⟨266123102194291469916509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2838646423405775679109429 266123102194291469916509)
                  ·
                    rfl

theorem cell21_1166114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1166114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166114 prefixEnd_1166114 := by exact prefixLift 1166114
  have htrace : WordTrace (prefixWord ++ tailWord_1166114) baseStart_1166114 baseEnd_1166114 := by
    simpa [prefixWord, tailWord_1166114, baseEnd_1166114] using wordTrace_append hprefix tailTrace_1166114
  have hstable : (prefixWord ++ tailWord_1166114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166114).length < 2 ^ (prefixWord ++ tailWord_1166114).sum := by decide
  have hdescent : baseEnd_1166114 < baseStart_1166114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166131 : List Nat := [1, 1, 1, 2, 6, 2, 2, 3, 3]
def baseStart_1166131 : Nat := 118140960795 + 1166131 * 2 ^ 59
def prefixEnd_1166131 : Nat := 4983230072969 + 3 ^ 40 * 1166131 * 2
def baseEnd_1166131 : Nat := 266126981825903218133141

theorem tailTrace_1166131 : CollatzResearch.WordTrace tailWord_1166131 prefixEnd_1166131 266126981825903218133141 := by
  unfold tailWord_1166131
  simp only [CollatzResearch.WordTrace]
  refine ⟨42532291738314021164026247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28354861158876014109350831 42532291738314021164026247)
  ·
    refine ⟨63798437607471031746039371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42532291738314021164026247 63798437607471031746039371)
    ·
      refine ⟨95697656411206547619059057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63798437607471031746039371 95697656411206547619059057)
      ·
        refine ⟨71773242308404910714294293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95697656411206547619059057 71773242308404910714294293)
        ·
          refine ⟨3364370733206480189732545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71773242308404910714294293 3364370733206480189732545)
          ·
            refine ⟨2523278049904860142299409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3364370733206480189732545 2523278049904860142299409)
            ·
              refine ⟨1892458537428645106724557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523278049904860142299409 1892458537428645106724557)
              ·
                refine ⟨709671951535741915021709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1892458537428645106724557 709671951535741915021709)
                ·
                  refine ⟨266126981825903218133141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709671951535741915021709 266126981825903218133141)
                  ·
                    rfl

theorem cell21_1166131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 3].length) (baseStart_1166131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166131 prefixEnd_1166131 := by exact prefixLift 1166131
  have htrace : WordTrace (prefixWord ++ tailWord_1166131) baseStart_1166131 baseEnd_1166131 := by
    simpa [prefixWord, tailWord_1166131, baseEnd_1166131] using wordTrace_append hprefix tailTrace_1166131
  have hstable : (prefixWord ++ tailWord_1166131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166131).length < 2 ^ (prefixWord ++ tailWord_1166131).sum := by decide
  have hdescent : baseEnd_1166131 < baseStart_1166131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166148 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1166148 : Nat := 118140960795 + 1166148 * 2 ^ 59
def prefixEnd_1166148 : Nat := 4983230072969 + 3 ^ 40 * 1166148 * 2
def baseEnd_1166148 : Nat := 266130861457514966349773

theorem tailTrace_1166148 : CollatzResearch.WordTrace tailWord_1166148 prefixEnd_1166148 266130861457514966349773 := by
  unfold tailWord_1166148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21266455889626216533697549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28355274519501622044930065 21266455889626216533697549)
  ·
    refine ⟨7974920958609831200136581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21266455889626216533697549 7974920958609831200136581)
    ·
      refine ⟨1495297679739343350025609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7974920958609831200136581 1495297679739343350025609)
      ·
        refine ⟨1121473259804507512519207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1495297679739343350025609 1121473259804507512519207)
        ·
          refine ⟨1682209889706761268778811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121473259804507512519207 1682209889706761268778811)
          ·
            refine ⟨2523314834560141903168217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682209889706761268778811 2523314834560141903168217)
            ·
              refine ⟨1892486125920106427376163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523314834560141903168217 1892486125920106427376163)
              ·
                refine ⟨2838729188880159641064245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892486125920106427376163 2838729188880159641064245)
                ·
                  refine ⟨266130861457514966349773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2838729188880159641064245 266130861457514966349773)
                  ·
                    rfl

theorem cell21_1166148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1166148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166148 prefixEnd_1166148 := by exact prefixLift 1166148
  have htrace : WordTrace (prefixWord ++ tailWord_1166148) baseStart_1166148 baseEnd_1166148 := by
    simpa [prefixWord, tailWord_1166148, baseEnd_1166148] using wordTrace_append hprefix tailTrace_1166148
  have hstable : (prefixWord ++ tailWord_1166148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166148).length < 2 ^ (prefixWord ++ tailWord_1166148).sum := by decide
  have hdescent : baseEnd_1166148 < baseStart_1166148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166187 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 6]
def baseStart_1166187 : Nat := 118140960795 + 1166187 * 2 ^ 59
def prefixEnd_1166187 : Nat := 4983230072969 + 3 ^ 40 * 1166187 * 2
def baseEnd_1166187 : Nat := 266139761788859565199693

theorem tailTrace_1166187 : CollatzResearch.WordTrace tailWord_1166187 prefixEnd_1166187 266139761788859565199693 := by
  unfold tailWord_1166187
  simp only [CollatzResearch.WordTrace]
  refine ⟨42534334226111142728064815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28356222817407428485376543 42534334226111142728064815)
  ·
    refine ⟨63801501339166714092097223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42534334226111142728064815 63801501339166714092097223)
    ·
      refine ⟨95702252008750071138145835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63801501339166714092097223 95702252008750071138145835)
      ·
        refine ⟨143553378013125106707218753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95702252008750071138145835 143553378013125106707218753)
        ·
          refine ⟨107665033509843830030414065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143553378013125106707218753 107665033509843830030414065)
          ·
            refine ⟨80748775132382872522810549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107665033509843830030414065 80748775132382872522810549)
            ·
              refine ⟨7570197668660894299013489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80748775132382872522810549 7570197668660894299013489)
              ·
                refine ⟨5677648251495670724260117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7570197668660894299013489 5677648251495670724260117)
                ·
                  refine ⟨266139761788859565199693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5677648251495670724260117 266139761788859565199693)
                  ·
                    rfl

theorem cell21_1166187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_1166187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1166187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1166187 prefixEnd_1166187 := by exact prefixLift 1166187
  have htrace : WordTrace (prefixWord ++ tailWord_1166187) baseStart_1166187 baseEnd_1166187 := by
    simpa [prefixWord, tailWord_1166187, baseEnd_1166187] using wordTrace_append hprefix tailTrace_1166187
  have hstable : (prefixWord ++ tailWord_1166187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166187).length < 2 ^ (prefixWord ++ tailWord_1166187).sum := by decide
  have hdescent : baseEnd_1166187 < baseStart_1166187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
